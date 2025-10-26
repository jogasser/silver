// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.plugin.ExtensionTypeCoordinate
import viper.silver.plugin.standard.adt.{AdtType, AdtDestructorApp, AdtConstructorApp}

import scala.collection.mutable

/* TODO:
 *   - Removed commented code
 *   - Decompose/tidy up method findNecessaryTypeInstances
 *   - Mark all internal methods as private -> easier for users to find the potentially useful ones
 *   - Add high-level comments describing how the ground instances are computed
 */

object DomainInstances {
  type TypeSubstitution = Map[TypeVar, Type]

  def getInstanceMembers(p: Program, dt: DomainType): (Seq[DomainFunc], Seq[DomainAxiom]) = {
    val domain = p.findDomain(dt.domainName)

    val functions = domain.functions.map(substitute(_, dt.typVarsMap, p)).filter(collectGroundTypes(_, p).subsetOf(p.groundTypeInstances)).distinct
    val axioms = domain.axioms.map(substitute(_, dt.typVarsMap, p)).filter(collectGroundTypes(_, p).subsetOf(p.groundTypeInstances)).distinct

    (functions, axioms)
  }


  def collectGroundTypes(n: Node, p: Program): Set[Type] = n.deepCollect {
    case t: Type if t.isConcrete => t
    case dfa: DomainFuncApp if dfa.typVarMap.values.forall(_.isConcrete) =>
      DomainType(dfa.domainName, dfa.typVarMap)(p.findDomain(dfa.domainName).typVars)
  }.toSet

  ///////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////
  //Generic type instances
  ///////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////
  //Here we calculate all the needed ground instances of generic types (domain and collection types)

  ///////////////////////////////////////////////////////////////////////////////////////////
  //Classes for generic type ground instances

  def findNecessaryTypeInstances(p: Program, tcThreshold: Int = 1): Set[Type] = {
    val domainFunctionAxiomMap = p.domains.flatMap(d => d.axioms.flatMap(a => a.exp.deepCollect{
      case dfa: DomainFuncApp => dfa -> a
    })).groupBy(pair => pair._1.funcname)

    val allGroundDFAs = p.deepCollect{
      case dfa: DomainFuncApp if dfa.typVarMap.values.forall(_.isConcrete) => dfa
    }


    def tryUnify(t1: Type, t2: Type, s: TypeSubstitution): Option[TypeSubstitution] = {
      assert(t2.isConcrete)
      (t1, t2) match {
        case (tv: TypeVar, _) =>
          if (s.contains(tv))
            if (s(tv) == t2)
               Some(s)
            else
              None
          else
            Some(s + (tv -> t2))
        case (gt1: GenericType, gt2: GenericType) =>
          if (gt1.genericName == gt2.genericName)
            tryUnifys(gt1.typeArguments, gt2.typeArguments, s)
          else
            None
        case _ => if (t1 == t2) Some(s) else None
      }
    }

    def tryUnifys(ts1: Seq[Type], ts2: Seq[Type], s: TypeSubstitution): Option[TypeSubstitution] = {
      assert(ts1.size == ts2.size)
      var ss: Option[TypeSubstitution] = Some(s)
      for (tp <- ts1.zip(ts2)) {
        ss match {
          case Some(sss) => ss = tryUnify(tp._1, tp._2, sss)
          case None => return None
        }
      }
      ss
    }

    def tryUnifyWithDefault(tvs: Seq[TypeVar], ts1: Seq[Type], ts2: Seq[Type]): Option[TypeSubstitution] = {
      tryUnifys(ts1, ts2, Map[TypeVar, Type]()) match {
        case Some(s) => Some(complete(s, tvs))
        case None => None
      }
    }
    def complete(ts: TypeSubstitution, tvs: Seq[TypeVar]) =
      (tvs map (tv => tv -> ts.getOrElse(tv, Program.defaultType))).toMap

    val gtis: Set[Type] =
      allGroundDFAs.flatMap(dfa => {
        domainFunctionAxiomMap.get(dfa.funcname) match {
          case Some(ps) =>
            ps.flatMap(f = pair => {
              val d2 = p.findDomain(dfa.domainName)
              val tvs = d2.typVars
              val axDom = p.findDomain(pair._2.domainName)
              val axTvs = axDom.typVars
              tryUnifyWithDefault(axTvs, tvs.map(pair._1.typVarMap.get(_).get), tvs.map(dfa.typVarMap.get(_).get)) match {
                case Some(ts) =>
                  Set[Type](DomainType(pair._2.domainName, ts)(axTvs))
                case None => Set[Type]()
              }
            }).toSet
          case None => Set[Type]()
        }
      }).flatMap(downClosureGround).toSet

    var allDirectGroundTypes: Set[Type] = p.deepCollect({
      case t: Type if t.isConcrete => downClosureGround(t)
      case dfa: DomainFuncApp if dfa.typVarMap.values.forall(_.isConcrete) =>
        val d = p.findDomain(dfa.func(p).domainName)
        downClosureGround(DomainType(d, dfa.typVarMap))
    }).flatten.toSet
    allDirectGroundTypes = allDirectGroundTypes.union(gtis)

    val todo = new mutable.Queue[TypeCoordinate]()
    val done = new mutable.HashSet[TypeCoordinate]()
    val tcLuggage = new mutable.HashMap[TypeCoordinate, Map[TypeVar, Int]]()

    for (gt <- allDirectGroundTypes) {
      val tc = makeTypeCoordinate(gt)
      recursiveBottomUpEnqueue(todo, done, tc)
      if (!(tcLuggage contains tc)) {
        tcLuggage(tc) = gt match {
          case dt: DomainType => dt.typeParameters.map (_ -> 0).toMap
          case _ => Map()
        }
      }
    }

    def recursiveBottomUpEnqueue(todo: mutable.Queue[TypeCoordinate], done: mutable.HashSet[TypeCoordinate], tc: TypeCoordinate): Unit = {
      if (done add tc) {
        assert(!(todo contains tc))
        for (stc <- tc.subTCs)
          if (!(todo contains stc))
            recursiveBottomUpEnqueue(todo, done, stc)
        assert(!(todo contains tc))
        todo.enqueue(tc)
      }
    }

    while (todo.nonEmpty) {
      val tc = todo.dequeue()
      assert(done contains tc)
      assert(tcLuggage contains tc)
      val ntcs = new mutable.HashSet[TypeCoordinate]()
      tc match {
        case _: AtomicTypeCoordinate =>
        case gitc@GenericInstanceTypeCoordinate(_, typeArgs) =>
          assert(typeArgs.forall { tc => done contains tc })
          val types = gitc.collectTypes(p)
          types.foreach(t => {
            val tc2 = makeTypeCoordinate(t.substitute(gitc.typeSubstitution))
            if (!(done contains tc2)) {
              val tc2InflationMap =
                (t match {
                  case dt2: DomainType =>
                    dt2.typVarsMap.map {
                      case (tv2: TypeVar, t2: Type) =>
                        tv2 -> (getFTVDepths(t2).map { case (ftv: TypeVar, d: Int) => d + tcLuggage(tc)(ftv) } ++ Seq(0)).max
                    }
                  case _ => Seq()
                }).toMap

              if (tc2InflationMap.values.forall(_ <= tcThreshold)) {
                if (!tcLuggage.contains(tc2))
                  tcLuggage(tc2) = tc2InflationMap
                else
                  tcLuggage(tc2) = (
                       tcLuggage(tc2)
                    ++ tc2InflationMap.map { case (tv, d) => tv -> (d + tcLuggage(tc2).getOrElse(tv, 0)) })

                assert(tcLuggage contains tc2)
                ntcs += tc2
              }
            }
        })
      }

      for (ntc <- ntcs) {
        assert(ntc.subTCs.forall(tc=>(done union ntcs).contains(tc)))
        recursiveBottomUpEnqueue(todo, done, ntc)
      }
    }

    val result = done.map(_.t).toSet
    result
  }

  def substitute[A <: Node](e: A, s: TypeSubstitution, p: Program): A =
    e.transform {
      case dfa@DomainFuncApp(_, args, ts) =>
        val ts2 = ts.toSeq.map(pair => (pair._1, substitute(pair._2, s, p))).toMap
        val argss = args map (substitute(_, s, p))
        DomainFuncApp(dfa.func(p), argss, ts2)(dfa.pos, dfa.info)
      case des@AdtDestructorApp(_, _, ts) =>
        val ts2 = ts.toSeq.map(pair => (pair._1, substitute(pair._2, s, p))).toMap
        AdtDestructorApp(des.name, substitute(des.rcv, s, p), ts2)(des.pos, des.info, des.typ.substitute(ts2), des.adtName, des.errT)
      case cons@AdtConstructorApp(_, args, ts) =>
        val ts2 = ts.toSeq.map(pair => (pair._1, substitute(pair._2, s, p))).toMap
        val argss = args map (substitute(_, s, p))
        AdtConstructorApp(cons.name, argss, ts2)(cons.pos, cons.info, cons.typ.substitute(ts2), cons.adtName, cons.errT)
      case lvd@LocalVar(name, _) =>
        LocalVar(name, substitute(lvd.typ, s, p))(lvd.pos, lvd.info)

      case t: Type =>
        t.substitute(s)
    }

  def getFTVDepths(t: Type): Map[TypeVar, Int] = t match {
    case dt: DomainType =>
      dt.typVarsMap.flatMap {
        case (_: TypeVar, t: Type) => getFTVDepths(t).map { case (tv2: TypeVar, d: Int) => tv2 -> d.+(1) }
      }
    case adt: AdtType =>
      adt.typVarsMap.flatMap {
        case (_: TypeVar, t: Type) => getFTVDepths(t).map { case (tv2: TypeVar, d: Int) => tv2 -> d.+(1) }
      }
    case ct: CollectionType => getFTVDepths(ct.elementType).map { case (tv2: TypeVar, d: Int) => tv2 -> d.+(1) }

    case m: MapType =>
      val keys = getFTVDepths(m.keyType).map { case (t2, d) => t2 -> d.+(1) }
      val values = getFTVDepths(m.valueType).map { case (t2, d) => t2 -> d.+(1) }
      (keys.keySet union values.keySet).map(t2 => t2 -> (keys.get(t2).toList ++ values.get(t2).toList).max).toMap

    case tv: TypeVar => Map(tv -> 0)
    case _: BuiltInType => Map()
  }


  def down1Types(t: Type): Set[Type] = t match {
    case dt: DomainType => dt.typVarsMap.values.toSet
    case ct: CollectionType => Set(ct.elementType)
    case m: MapType => Set(m.keyType, m.valueType)
    case _: BuiltInType => Set()
    case et: ExtensionType => ExtensionTypeCoordinate.down1Types(et)
    case _: TypeVar => Set()
  }

  def downClosure(t: Type): Set[Type] =
    Set(t) ++ down1Types(t).flatMap(downClosure)

  def downClosureGround(t: Type): Set[Type] =
    (if (t.isConcrete) Set(t) else Set()) ++ down1Types(t).flatMap(downClosure)


  def collectDomainTypes(n: Node, p: Program): Set[Type] ={
    n.shallowCollect {
      case t: Type =>
        downClosure(t)
      case dfa@DomainFuncApp(_, args, typVarMap) =>
        /* Given a domain function application, we collect the following types:
         *   - return type of the function application
         *   - domain that the applied function belongs to
         *   - from the provided function arguments
         *   - from the type variable map used for the application
         */
        val d = p.findDomain(dfa.domainName)
        val m = d.typVars.map(t => t -> dfa.typVarMap.getOrElse(t, Program.defaultType)).toMap
        val dt = DomainType(d, m)

        (   Set(dfa.typ, dt)
         ++ (args flatMap (collectDomainTypes(_, p)))
         ++ (typVarMap.values flatMap (collectDomainTypes(_,p))))
    }.flatten.toSet
  }

  def makeTypeCoordinate(t: Type): TypeCoordinate = t match {
    case ct: CollectionType => new CollectionTypeCoordinate(ct,makeTypeCoordinate(ct.elementType))
    case mt: MapType => new MapTypeCoordinate(mt, makeTypeCoordinate(mt.keyType), makeTypeCoordinate(mt.valueType))
    case bit: BuiltInType => AtomicTypeCoordinate(bit)
    case dt: DomainType => new DomainInstanceTypeCoordinate(dt,
      dt.typeParameters.map(tv => makeTypeCoordinate(dt.typVarsMap(tv)))
    )
    case et: ExtensionType => ExtensionTypeCoordinate.makeTypeCoordinate(et)
    case _:TypeVar => throw new Exception("Internal error in type system - unexpected non-ground type <" + t.toString() + ">")
  }

  sealed abstract class TypeCoordinate(val t: Type) {
    def subTCs: Set[TypeCoordinate]

    require(t.isConcrete)
    override def toString: String = t.toString()
  }

  object CollectionClass extends Enumeration {
    type CollectionClass = Value
    val Seq,Set,Multiset = Value

    def getCC(ct: CollectionType): CollectionClass.Value =
    {
      ct match {
        case SetType(_) => Set
        case MultisetType(_) => Multiset
        case SeqType(_) => Seq
      }
    }

    def ccName(cc:CollectionClass): String =
      cc match {
        case Set => "Set"
        case Multiset => "Multiset"
        case Seq => "Seq"
      }
  }

  sealed case class AtomicTypeCoordinate(bit: BuiltInType) extends TypeCoordinate(bit){
    override def subTCs = Set()
  }
  abstract case class GenericInstanceTypeCoordinate(gname: String, args: Seq[TypeCoordinate])(val gt: GenericType)
    extends TypeCoordinate(gt){
    def typeSubstitution: Map[TypeVar, Type]
    override def subTCs: Set[TypeCoordinate] = args.toSet

    def collectTypes(p: Program): Set[Type]
  }
  sealed class CollectionTypeCoordinate(ct: CollectionType, etc: TypeCoordinate)
    extends GenericInstanceTypeCoordinate(CollectionClass.ccName(CollectionClass.getCC(ct)),Seq(etc))(ct){
    val cc: CollectionClass.Value = CollectionClass.getCC(ct)
    override def collectTypes(p: Program) = Set()
    override def typeSubstitution = Map()
  }
  sealed class MapTypeCoordinate(mt : MapType, keyCoord : TypeCoordinate, valueCoord : TypeCoordinate)
    extends GenericInstanceTypeCoordinate("Map", Seq(keyCoord, valueCoord))(mt) {
    override def typeSubstitution: Map[TypeVar, Type] = Map()
    override def collectTypes(p: Program): Set[Type] = Set()
  }
  sealed class DomainInstanceTypeCoordinate(val dt: DomainType, typeArgs: Seq[TypeCoordinate])
    extends GenericInstanceTypeCoordinate(dt.domainName, typeArgs)(dt){
    override def collectTypes(p: Program): Set[Type] = {
      val domain = p.findDomain(dt.domainName)
      collectDomainTypes(domain, p)
    }
    override def typeSubstitution: Map[TypeVar, Type] = dt.typVarsMap
  }

  def getTVs(t: Type): Set[TypeVar] =
    t match {
      case tv: TypeVar => Set(tv)
      case dt: DomainType =>
        (dt.typeParameters.toSet -- dt.typVarsMap.keys) ++ dt.typVarsMap.values.flatMap(getTVs)
      case ct: CollectionType => getTVs(ct.elementType)
      case m: MapType => getTVs(m.keyType) union getTVs(m.valueType)
      case _ => Set()
    }

}
