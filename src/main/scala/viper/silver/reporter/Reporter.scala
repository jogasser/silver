// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silver.reporter

import java.io.FileWriter
import scala.collection.mutable._

trait Reporter {
  val name: String

  def report(msg: Message): Unit
}

object NoopReporter extends Reporter {
  val name: String = "NoopReporter"
  def report(msg: Message): Unit = ()
}

case class CSVReporter(name: String = "csv_reporter", path: String = "report.csv") extends Reporter {

  def this() = this("csv_reporter", "report.csv")

  val csv_file = new FileWriter(path, true)

  def report(msg: Message): Unit = {
    msg match {
      case AstConstructionFailureMessage(time, _) =>
        csv_file.write(s"AstConstructionFailureMessage,${time}\n")
      case AstConstructionSuccessMessage(time) =>
        csv_file.write(s"AstConstructionSuccessMessage,${time}\n")
      case OverallFailureMessage(_, time, _) =>
        csv_file.write(s"OverallFailureMessage,${time}\n")
      case OverallSuccessMessage(_, time) =>
        csv_file.write(s"OverallSuccessMessage,${time}\n")
      case ExceptionReport(e) =>
        csv_file.write(s"ExceptionReport,${e.toString}\n")
      case ExternalDependenciesReport(deps) =>
        deps.foreach(dep =>
          csv_file.write(s"ExternalDependenciesReport,${dep.name} ${dep.version} located at ${dep.location}\n")
        )
      case AnnotationWarning(text) =>
        csv_file.write(s"AnnotationWarning,${text}\n")
      case WarningsDuringParsing(warnings) =>
        warnings.foreach(report => {
          csv_file.write(s"WarningsDuringParsing,${report}\n")
        })
      case WarningsDuringTypechecking(warnings) =>
        warnings.foreach(report => {
          csv_file.write(s"WarningsDuringTypechecking,${report}\n")
        })
      case WarningsDuringVerification(warnings) =>
        warnings.foreach(report => {
          csv_file.write(s"WarningsDuringVerification,${report}\n")
        })
      case InvalidArgumentsReport(_, errors) =>
        errors.foreach(error => {
          csv_file.write(s"WarningsDuringParsing,${error}\n")
        })

      case EntitySuccessMessage(_, concerning, time, cached) =>
        csv_file.write(s"EntitySuccessMessage,${concerning.name},${time}, ${cached}\n")
      case EntityFailureMessage(_, concerning, time, _, cached) =>
        csv_file.write(s"EntityFailureMessage,${concerning.name},${time}, ${cached}\n")

      case BranchFailureMessage(_, concerning, _, cached) =>
        csv_file.write(s"BranchFailureMessage,${concerning.name},${cached}\n")

      case _: SimpleMessage | _: CopyrightReport | _: MissingDependencyReport | _: BackendSubProcessReport |
           _: InternalWarningMessage | _: ConfigurationConfirmation=> // Irrelevant for reporting

      case q: QuantifierInstantiationsMessage => csv_file.write(s"${q.toString}\n")
      case q: QuantifierChosenTriggersMessage => csv_file.write(s"${q.toString}\n")
      case t: VerificationTerminationMessage => csv_file.write(s"${t.toString}\n")
      case _ =>
        println( s"Cannot properly print message of unsupported type: $msg" )
    }
    csv_file.flush()
  }
}

case class StdIOReporter(name: String = "stdout_reporter", timeInfo: Boolean = true) extends Reporter {

  var counter = 0

  // includes the unit name (e.g., seconds, sec, or s).
  private def timeStr: Time => String = format.formatMillisReadably

  private def plurals(num_things: Int): String = if (num_things==1) "" else "s"

  private def bulletFmt(num_items: Int): String = s"%${num_items.toString.length}d"

  def report(msg: Message): Unit = {
    msg match {
      case AstConstructionFailureMessage(t, res) =>
        val num_errors = res.errors.length
        if (!timeInfo)
          println( s"AST construction resulted in $num_errors error${plurals(num_errors)}:" )
        else
          println( s"AST construction resulted in $num_errors error${plurals(num_errors)} in ${timeStr(t)}:" )
        res.errors.zipWithIndex.foreach { case(e, n) => println( s"  [${bulletFmt(num_errors).format(n)}] ${e.readableMessage}" ) }

      case AstConstructionSuccessMessage(t) =>
        if (!timeInfo)
          println( s"the file represents a consistent Viper program." )
        else
          println( s"the file represents a consistent Viper program; constructed AST in ${timeStr(t)}." )

      case OverallFailureMessage(v, t, res) =>
        val num_errors = res.errors.length
        if (!timeInfo)
          println( s"$v found $num_errors error${plurals(num_errors)}:" )
        else
          println( s"$v found $num_errors error${plurals(num_errors)} in ${timeStr(t)}:" )
        res.errors.zipWithIndex.foreach { case(e, n) => println( s"  [${bulletFmt(num_errors).format(n)}] ${e.readableMessage}" ) }

      case OverallSuccessMessage(v, t) =>
        if (!timeInfo)
          println( s"$v finished verification successfully." )
        else
          println( s"$v finished verification successfully in ${timeStr(t)}." )

      case ExceptionReport(e) =>
        /** Theoretically, we may encounter an exceptional message that has
          * not yet been reported via AbortedExceptionally. This can happen
          * if we encounter exeptions in e.g. the parser. */
        println( s"Verification aborted exceptionally: ${e.toString}" )
        e.printStackTrace(System.out);
        Option(e.getCause) match {
          case Some(cause) => println( s"  Cause: ${cause.toString}" )
          case None =>
        }
        //println( s"  See log file for more details: ..." )

      case ExternalDependenciesReport(deps) =>
        val s: String = (deps map (dep => {
          s"  ${dep.name} ${dep.version}, located at ${dep.location}."
        })).mkString("\n")
        println( s"The following dependencies are used:\n$s" )

      case WarningsDuringParsing(warnings) =>
        warnings.foreach(println)

      case WarningsDuringTypechecking(warnings) =>
        warnings.foreach(println)

      case WarningsDuringVerification(warnings) =>
        warnings.foreach(println)

      case AnnotationWarning(text) =>
        println(s"Annotation warning: ${text}")

      case InvalidArgumentsReport(_, errors) =>
        errors.foreach(e => println(s"  ${e.readableMessage}"))
        println( s"Run with just --help for usage and options" )

      case ExecutionTraceReport(memberTraces, axioms, functionPostAxioms) =>
        println("Execution trace for the last run:")
        println(s"  Members:")
        memberTraces.foreach(t => println(s"    $t"))
        println(s"  Axioms:")
        axioms.foreach(t => println(s"    $t"))
        println(s"  FunctionPostAxioms:")
        functionPostAxioms.foreach(a => println(s"    $a"))


      case CopyrightReport(text) =>
        println( text )

      case BackendSubProcessReport(_, _, _, _) =>  // Not relevant to the end user

      case MissingDependencyReport(text) =>
        println( s"encountered missing dependency: $text" )

      // These get reported without being transformed by any plugins, it would be an issue if we printed them to STDOUT.
      case EntitySuccessMessage(_, _, _, _) =>    // FIXME Currently, we only print overall verification results to STDOUT.
      case EntityFailureMessage(_, _, _, _, _) =>    // FIXME Currently, we only print overall verification results to STDOUT.
      case BranchFailureMessage(_, _, _, _) =>    // FIXME Currently, we only print overall verification results to STDOUT.
      case ConfigurationConfirmation(_) =>     // TODO  use for progress reporting
        //println( s"Configuration confirmation: $text" )
      case InternalWarningMessage(_) =>        // TODO  use for progress reporting
        //println( s"Internal warning: $text" )
      case _: SimpleMessage =>
        //println( sm.text )
      case _: QuantifierInstantiationsMessage => // too verbose, do not print
      case _: QuantifierChosenTriggersMessage => // too verbose, do not print
      case _: VerificationTerminationMessage =>
      case _: BenchmarkingMessage =>
      case _ =>
        println( s"Cannot properly print message of unsupported type: $msg" )
    }
    counter = counter + 1
  }
}

object ProverActionIDs {
  private var _id : Int = 0

  def getID : Int = {
    _id += 1
    _id
  }
}

case class BenchmarkingReporter(name: String = "benchmarking_reporter") extends Reporter {
  private val _initial_time = System.currentTimeMillis()
  // Each accumulator has a string id and a map of currently open instances to time.
  // That map has the following special keys:
  // -1: where the total time is stored
  // -2: where the number of instances is stored
  // -3: where a negative value means we have to overrule following instances on this accumulator
  //     and a positive means that we can keep opening instances (useful for benchmarking
  //     recursive methods)
  private var _accumulators: scala.collection.mutable.Map[String, scala.collection.mutable.Map[Int, Long]] = Map.empty
  //private var _rec: scala.collection.mutable.Seq[(String
  private var _previous_phase: Long = _initial_time

  def report(msg: Message): Unit = {
    msg match {
      case BenchmarkingPhase(phase) =>
        val t = System.currentTimeMillis()
        println(s"[Benchmarking] Phase $phase at ${t - _initial_time} ms and took ${t - _previous_phase} ms")
        _previous_phase = t
      case BenchmarkingAccumulator(accum, id, rec) =>
        if (_accumulators contains accum) {
          if (_accumulators(accum) contains id) {
            _accumulators(accum)(-1) += (System.currentTimeMillis() - _accumulators(accum)(id))
            _accumulators(accum)(-2) += 1
            _accumulators(accum) remove id
            _accumulators(accum)(-3) = 1
          } else {
            if (_accumulators(accum)(-3) > 0) {
              _accumulators(accum)(id) = System.currentTimeMillis()
              if (rec)
                _accumulators(accum)(-3) = -1
            } else println(_accumulators(accum).keySet)
          }
        } else {
          if (rec)
            _accumulators(accum) = Map((-3, -1), (-1, 0), (-2, 0), (id, System.currentTimeMillis()))
          else
            _accumulators(accum) = Map((-3, 1), (-1, 0), (-2, 0), (id, System.currentTimeMillis()))
        }
      case BenchmarkingReport(msg, accum) if _accumulators contains accum =>
        println(s"[Benchmarking] Accumulated time for '$msg' took ${_accumulators(accum)(-1)} ms across ${_accumulators(accum)(-2)} instances")
      case _ =>
    }
  }
}

case class PollingReporter(name: String = "polling_reporter", pass_through_reporter: Reporter) extends Reporter {
  // this reporter stores the messages it receives and reports them upon polling
  var messages: Queue[Message] = Queue()

  def report(msg: Message): Unit = this.synchronized {
    messages = messages.enqueue(msg)
    pass_through_reporter.report(msg)
  }

  def getNewMessage(): Message = this.synchronized {
    messages.dequeue()
  }

  def hasNewMessage(): Boolean = this.synchronized {
    messages.length > 0
  }
}
