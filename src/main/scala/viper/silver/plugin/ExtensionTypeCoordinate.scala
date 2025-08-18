package viper.silver.plugin

import viper.silver.ast.utility.DomainInstances
import viper.silver.ast.{ExtensionType, Program, Type, TypeVar}
import viper.silver.ast.utility.DomainInstances.{GenericInstanceTypeCoordinate, TypeCoordinate, collectDomainTypes}
import viper.silver.plugin.standard.adt.{Adt, AdtType}

object ExtensionTypeCoordinate {

  def down1Types(t: ExtensionType): Set[Type] = t match {
    case adt: AdtType => adt.typVarsMap.values.toSet
  }

  def makeTypeCoordinate(t: ExtensionType): TypeCoordinate = t match {
    case adt: AdtType => new AdtTypeCoordinate(adt,
      adt.typeParameters.map(tv => DomainInstances.makeTypeCoordinate(adt.typVarsMap(tv)))
    )
  }

  sealed class AdtTypeCoordinate(val adt: AdtType, typeArgs: Seq[TypeCoordinate])
    extends GenericInstanceTypeCoordinate(adt.adtName, typeArgs)(adt) {
    override def collectTypes(p: Program): Set[Type] = Set()

    // TODO test Adts with Domain type args & Domain with ADT type args
    override def typeSubstitution: Map[TypeVar, Type] = Map()
  }
}