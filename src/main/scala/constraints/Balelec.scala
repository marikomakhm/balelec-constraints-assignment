package constraints

import cafesat.api.Formulas._
import cafesat.api.FormulaBuilder._
import cafesat.api.Solver._

/**
 * This component implements a constraint solver for assigning time slots to volunteers
 * for various tasks at a festival. A task may require more than one volunteer,
 * and a volunteer can take a limited number of tasks
 */
object Balelec {

  import Arithmetic._

  case class Volunteer(name: String) {
    override def toString = name
  }

  /**
   * A task is represented by its name and
   * its capacity, i.e. the exact number of people
   * required to complete it.
   */
  case class Task(name: String, capacity: Int) {
    override def toString = name
  }

  /**
   * This function schedules volunteers to tasks.
   * It takes as input a list of volunteers and a list of tasks.
   * The `availability` map contains mappings from volunteers to the
   * tasks they are available for.
   * A volunteer can be assigned to several tasks, but only
   * up to a maximum number of task specified by the `maxWorkload` parameter.
   * It is ok to not assign a volunteer to any task.
   *
   * The return value is a list of volunteers assigned to each task. The function only
   * returns a complete valid assignment, if no such assignment exists then the
   * function returns None.
   */
  def schedule(
    volunteers: List[Volunteer],
    tasks: List[Task],
    availability: Map[Volunteer, List[Task]],
    maxWorkload: Int
  ): Option[Map[Task, List[Volunteer]]] = {

    val propVariables: Map[(Volunteer, Task), PropVar] =
      volunteers.flatMap({ case v@Volunteer(name) => tasks.map(t => (v, t) -> propVar(name + " " + t.name))}).toMap

    /**
      * desirableTasks takes the available tasks and puts a logical "or" between each of
      * these tasks and a logical "and" between the "not" of the unavailable tasks, in order
      * to make sure that the volunteer does not do any tasks he/she did not sign up for.
      */

    val desirableTasks: List[Formula] =
      for (v <- volunteers) yield
        (tasks.filter(t => !availability(v).contains(t))).foldLeft[Formula](true)((acc, e) => acc && !propVariables(v, e))

    val eachVolunteerWorkload: List[Formula] =
      volunteers.map(v => atMostMaxTrue((for {t <- tasks} yield propVariables(v, t)), maxWorkload))

    val eachTaskCompleted: List[Formula] =
      tasks.map(t => atCapacity((for {v <- volunteers} yield propVariables(v, t)), t.capacity))

    val allConstraints: List[Formula] =
      eachVolunteerWorkload ++ desirableTasks ++ eachTaskCompleted

    val res = solveForSatisfiability(and(allConstraints:_*))

    res.map(model => {
      tasks.map(t => {
        val assignedVolunteers = volunteers.filter(v => model(propVariables((v, t))))
        (t, assignedVolunteers)
      }).toMap
    })
  }

  //does this work
  private def atCapacity(ns: List[Formula], cap: Int): Formula = {
    val (r, c) = countPositiveBits(ns)
    lessEquals(r, int2binary(cap)) && lessEquals(int2binary(cap), r) && and(c.toSeq:_*)
  }

  /**
   * This function takes a list of constraint, and returns a
   * constraint that is true if and only if at most max
   * of them are true.
   */
  def atMostMaxTrue(ns: List[Formula], max: Int): Formula = {
    val (r, c) = countPositiveBits(ns)
    lessEquals(r, int2binary(max)) && and(c.toSeq:_*)
  }

  /**
   * This function counts the number of positive bits in a number.
   * 
   * It takes a list of formulas, and returns a pair.
   * The first element of the pair is a list of formulas representing the number
   * of ones in `ns`.
   * The second element is a set of additional constraints that have been gathered along
   * the way. Hint: see `adder` for understanding how to use additional constraints
   */
  def countPositiveBits(ns: List[Formula]): (List[Formula], Set[Formula]) = {
    ns.foldLeft((List[Formula](false), Set[Formula]())) { case ((tmpSum, tmpAcc), n) =>
      val (r, c) = adder(tmpSum, List(n))
      (r, tmpAcc ++ c)
    }
  }

}
