package constraints

import cafesat.api.Formulas._
import cafesat.api.FormulaBuilder._
import cafesat.api.Solver._

/**
 * This component implements a constraint solver
 * for assigning time slots to bands at a festival
 */
object ConcertsPlanner {

  case class Band(name: String) {
    override def toString = name
  }

  case class Stage(name: String) {
    override def toString = name
  }

  case class Time(time: String) {
    override def toString = time
  }

  type Slot = (Stage, Time)

  /*
   * This function schedules bands to slots. It takes as input
   * a list of preferences, as a map from bands to the list of 
   * slots the band wishes to play in.
   *
   * The result is an `Option[Map[Band, Slot]]`. The function attemps to
   * assign a unique and different slot to each band. It returns None if
   * no complete valid scheduling exists.
   * If the problem has a complete valid assignment, a map from every
   * band to a slot is returned.
   * No partial solution is returned, if only some of the band can be assigned
   * a slot, then None is returned.
   */
  def plan(preferences: Map[Band, List[Slot]]): Option[Map[Band, Slot]] = {

    val bands: Seq[Band] = preferences.keys.toSeq
    val slots: Seq[Slot] = getAllSlots(preferences).toSeq
  
    //generates one propositional variable per band/slot combination
    val propVariables: Map[(Band, Slot), PropVar] =
      bands.flatMap({ case b@Band(name) =>
        slots.map(s => (b, s) -> propVar(name))
      }).toMap
  
    
    //Set of constraints ensuring each band gets a desired slot
    val desirableSlots: Seq[Formula] =
      for (b <- bands) yield preferences(b).foldLeft[Formula](false)((acc, e) => acc || propVariables(b, e))

    //A set of constraints ensuring that a band gets at most one slot
    val eachBandPlaysOnce: Seq[Formula] =
      bands.map(b => (
        for {s1 <- slots; s2 <- slots; if s1 != s2}
          yield !propVariables(b, s1) || !propVariables(b, s2)).foldLeft[Formula](true)((acc, e) => acc && e)
      )

    //A set of constraints ensuring that each slot is used at most once
    val eachSlotUsedOnce: Seq[Formula] =
      slots.map(s => (
      for {b1 <- bands; b2 <- bands; if b1 != b2}
        yield !propVariables(b1, s) || !propVariables(b2, s)).foldLeft[Formula](true)((acc, e) => acc && e)
      )
  
  
    //combining all the constraints together
    val allConstraints: Seq[Formula] = 
      desirableSlots ++ eachBandPlaysOnce ++ eachSlotUsedOnce
  
    //finding a satisfying assignment to the constraints
    val res = solveForSatisfiability(and(allConstraints:_*))
  
    res.map(model => {
      bands.map(band => {
        val assignedSlot = slots.find(slot => model(propVariables((band, slot))))
        (band, assignedSlot.get)
      }).toMap
    })
  }

  /**
   * This function takes a preference map, and returns all unique slots that are
   * part of the preferences.
   */
  def getAllSlots(preferences: Map[Band, List[Slot]]): Set[Slot] = preferences.flatMap(p => p._2).toSet

}
