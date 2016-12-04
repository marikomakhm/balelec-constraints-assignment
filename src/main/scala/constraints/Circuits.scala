package constraints

import cafesat.api.Formulas._
import cafesat.api.FormulaBuilder._
import cafesat.api.Solver.solveForSatisfiability

object Circuits {

  /**
   * This function describes and solves a boolean
   * circuit described 
   * [there](https://d396qusza40orc.cloudfront.net/progfun2/assignments/circuit.png)
   */
  def solveExample() : Unit = {
    val p: PropVar = propVar("p")
    val q: PropVar = propVar("q")
    val r: PropVar = propVar("r")

    val p1: PropVar = propVar("p'")
    val q1: PropVar = propVar("q'")

    val c1: PropVar = propVar("c1")
    val c2: PropVar = propVar("c2")

    val circuit = (
      (p1 iff !p) &&
      (q1 iff !q) &&
      (c1 iff (p1 || q)) &&
      (c2 iff (q1 || p)) &&
      (r iff (c1 && c2)) &&
      (r iff !p)
    )

    solveForSatisfiability(circuit) match {
      case None => println("UNSAT! Formula is unsatisfiable and has no solutions!")
      case Some(model) => {
        println("SAT: formula is satisfiable! One solution is")
        println("p = " + model(p))
        println("q = " + model(q))
        println("r = " + model(r))
      }
    }
  }

  def main(args: Array[String]) {
    println("Hello Circuits")
    solveExample()
  }
}
