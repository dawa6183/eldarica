/**
 * Copyright (c) 2022-2024 Zafer Esen, Philipp Ruemmer, Daniel Wallgren. All rights
 * reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package lazabs.horn.symex

import ap.parser.IAtom
import lazabs.horn.Util.Dag
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol}
import lazabs.horn.preprocessor.HornPreprocessor.Solution
import lazabs.horn.symex.Symex.SymexException

import scala.collection.mutable.{HashSet => MHashSet, Queue => MQueue}

/**
 * Implements a breadth-first forward symbolic execution using Symex.
 * @param maxDepth : Search will stop after deriving this many unit clauses
 *                   for a given predicate. Note that setting this value to
 *                   something other than None will yield an under-approximate
 *                   solution but will always terminate (like BMC).
 */
class BreadthFirstBackwardSymex[CC](clauses  : Iterable[CC],
                                    maxDepth : Option[Int] = None)(
    implicit clause2ConstraintClause:       CC => ConstraintClause)
    extends Symex(clauses)
    with SimpleSubsumptionChecker
    with ConstraintSimplifierUsingConjunctEliminator {

  printInfo("Starting breadth-first backward symbolic execution (BFS)...\n")

  // Explore the state graph (the derived unit clauses) breadth-first. At
  // each depth there can be multiple choices for execution from a state
  // (the clauses to resolve with). Hence, we have a queue of states to resolve
  // with, and for each state a queue of branches to explore.
  private val choicesQueue = new MQueue[(NormClause, Seq[UnitClause])]

  /*
   * Initialize the search by adding the facts (the initial states).
   * Each fact corresponds to a source in the search DAG.
   */
  for (fact <- facts) {
    printInfo("Adding fact to unit database")
    printInfo(fact.toString())
    unitClauseDB add (fact, parents = (factToNormClause(fact), Nil))
  }

  for (goal <- goals) {
    printInfo("Adding goal to unit database")
    printInfo(goal.toString())
    unitClauseDB add (goal, parents = (goalToNormClause(goal), Nil))
    handleNewUnitClause(goal)
  }

  final override def getClausesForResolution
    : Option[(NormClause, Seq[UnitClause])] = {
    /*
     * The unitClauseDB is empty if the set of Horn clauses to solve doesn't have any facts
     * The choicesQueue can become empty when the search space has been exhausted
     */
    if (unitClauseDB.isEmpty || choicesQueue.isEmpty) {
      None
    }
    else {
      maxDepth match {
        case None =>
          Some(choicesQueue.dequeue)
        case Some(depth) =>
          var res : Option[(NormClause, Seq[UnitClause])] = None
          var continue = true
          do {
            val candidate = choicesQueue.dequeue()
            val rs        = candidate._1.head._1
            unitClauseDB.inferred(rs) match {
              case Some(cucs) if cucs.length >= depth => ()
              // this is not a good candidate, continue
              case _ => // this is a good candidate, return
                continue = false
                res = Some(candidate)
            }
          } while (choicesQueue.nonEmpty && continue)
          res
      }
    }
  }

  def solve(): Either[Solution, Dag[(IAtom, CC)]] = {
    var result: Either[Solution, Dag[(IAtom, CC)]] = null

    val touched = new MHashSet[NormClause]
    facts.foreach(fact => touched += factToNormClause(fact))

    // start traversal
    var ind = 0
    while (result == null) {
      lazabs.GlobalParameters.get.timeoutChecker()
      ind += 1
      printInfo(ind + ".", false)
      getClausesForResolution match {
        case Some((nucleus, electrons)) => {
          touched += nucleus
          val newElectron = hyperResolve(nucleus, electrons)
          printInfo("\t" + nucleus + "\n  +\n\t" + electrons.mkString("\n\t"))
          printInfo("  =\n\t" + newElectron)
          val proverStatus = checkFeasibility(newElectron.constraint)
          if (hasContradiction(newElectron, proverStatus)) { // false :- true
            unitClauseDB.add(newElectron, (nucleus, electrons))
            result = Right(buildCounterExample(newElectron, forward = false))
          } else {
            if (unitClauseDB.add(newElectron, (nucleus, electrons))) {
              printInfo("\n  (Added to database.)\n")
              handleNewUnitClause(newElectron)
            } else {
              printInfo("\n  (Derived clause already exists in the database.)")
            }
          }
        }
        case None => // nothing left to explore, the clauses are SAT.
          printInfo("\t(Search space exhausted.)\n")

          result = checkUntouchedClauses(touched, forward = false)
        case other =>
          throw new SymexException(
            "Cannot hyper-resolve clauses: " + other.toString)
      }
    }
    result
  }

  override def handleNewUnitClause(electron: UnitClause): Unit = {
    printInfo("In handleNewUnitClause\n")

    val possibleChoices = clausesWithRelationInHead(electron.rs)

    // for each possible choice, fix electron.rs, and resolve against
    // all previous derivations of other body literals
    for (nucleus <- possibleChoices) {
      choicesQueue enqueue ((nucleus, Seq(electron)))
    }
  }
}
