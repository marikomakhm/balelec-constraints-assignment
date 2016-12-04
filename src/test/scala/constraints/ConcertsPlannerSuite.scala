package constraints

import org.scalatest.FunSuite

//import org.junit.runner.RunWith
//import org.scalatest.junit.JUnitRunner

//@RunWith(classOf[JUnitRunner])
class ConcertsPlannerSuite extends FunSuite {

  import ConcertsPlanner._

  test("getAllSlots is implemented") {
    val band1 = Band("Band1")
    val slot1 = (Stage("Venue1"), Time(""))
    getAllSlots(Map(band1 -> List(slot1)))
  }

  test("getAllSlots returns the correct slot when given only one band") {
    val band1 = Band("Band1")
    val slot1 = (Stage("Venue1"), Time(""))

    val preferences = Map(
      band1 -> List(slot1)
    )

    assert(getAllSlots(preferences) === Set(slot1))

  }

  test("getAllSlots collects slots among several bands") {
    val band1 = Band("Band1")
    val band2 = Band("Band2")
    val slot1 = (Stage("Venue1"), Time(""))
    val slot2 = (Stage("Venue2"), Time(""))

    val preferences = Map(
      band1 -> List(slot1),
      band2 -> List(slot2)
    )

    assert(getAllSlots(preferences) === Set(slot1, slot2))
  }



  test("plan is implemented") {
    val band1 = Band("Band1")
    val slot1 = (Stage("Venue1"), Time(""))
    ConcertsPlanner.plan(Map(band1 -> List(slot1)))
  }

  test("plan one band on one slot") {
    val band1 = Band("Band1")
    val slot1 = (Stage("Venue1"), Time(""))
    val res = ConcertsPlanner.plan(Map(band1 -> List(slot1)))
    assert(res != None)
    res.foreach(m => assert(m(band1) === slot1))
  }

  test("plan two bands on two slots with no choice") {
    val band1 = Band("Band1")
    val band2 = Band("Band2")
    val slot1 = (Stage("Venue1"), Time(""))
    val slot2 = (Stage("Venue2"), Time(""))

    val preferences = Map(
      band1 -> List(slot1),
      band2 -> List(slot2)
    )
    val goodPlan = ConcertsPlanner.plan(preferences)
    assert(goodPlan.nonEmpty)
    assert(checkAssignment(goodPlan.get, preferences))
  }

  test("plan two bands on two slots when one band can play in the two slots") {
    val band1 = Band("Band1")
    val band2 = Band("Band2")
    val slot1 = (Stage("Venue1"), Time(""))
    val slot2 = (Stage("Venue2"), Time(""))

    val preferences = Map(
      band1 -> List(slot1, slot2),
      band2 -> List(slot2)
    )
    val goodPlan = ConcertsPlanner.plan(preferences)
    assert(goodPlan.nonEmpty)
    assert(checkAssignment(goodPlan.get, preferences))
  }

  test("plan two bands on two slots when the bands can play in any slots") {
    val band1 = Band("Band1")
    val band2 = Band("Band2")
    val slot1 = (Stage("Venue1"), Time(""))
    val slot2 = (Stage("Venue2"), Time(""))

    val preferences = Map(
      band1 -> List(slot1, slot2),
      band2 -> List(slot1, slot2)
    )
    val goodPlan = ConcertsPlanner.plan(preferences)
    assert(goodPlan.nonEmpty)
    assert(checkAssignment(goodPlan.get, preferences))
  }

  test("planning three bands on two slots is impossible") {
    val band1 = Band("Band1")
    val band2 = Band("Band2")
    val band3 = Band("Band3")
    val slot1 = (Stage("Venue1"), Time(""))
    val slot2 = (Stage("Venue2"), Time(""))

    val preferences = Map(
      band1 -> List(slot1, slot2),
      band2 -> List(slot1, slot2),
      band3 -> List(slot1, slot2)
    )
    assert(ConcertsPlanner.plan(preferences).isEmpty)
  }



  private def checkAssignment(
    solution: Map[Band, Slot],
    preferences: Map[Band, List[Slot]]
  ): Boolean = {
    solution.keySet == preferences.keySet &&
    solution.forall(p =>
      preferences(p._1).contains(p._2)
    ) && {
      val values: List[Slot] = solution.values.toList
      values.size == values.toSet.size
    }
  }

}
