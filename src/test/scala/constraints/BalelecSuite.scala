package constraints

import cafesat.api.Formulas._
import cafesat.api.FormulaBuilder._
import cafesat.api.Solver._

import org.scalatest.FunSuite

//import org.junit.runner.RunWith
//import org.scalatest.junit.JUnitRunner

//@RunWith(classOf[JUnitRunner])
class BalelecSuite extends FunSuite {

  import Balelec._


  test("countPositives is implemented") {
    countPositiveBits(List(true))
  }

  test("countPositiveBits of single bit") {
    val bits1: List[Formula] = List(false)
    val (res1, constraints1) = countPositiveBits(bits1)
    assert(checkNumber(res1, constraints1, List(false)))
    assert(!checkNumber(res1, constraints1, List(true)))

    val bits3: List[Formula] = List(true)
    val (res3, constraints3) = countPositiveBits(bits3)
    assert(checkNumber(res3, constraints3, List(true)))
    assert(!checkNumber(res3, constraints3, List(false)))
  }

  test("countPositiveBits is working") {
    val bits2: List[Formula] = List(true, false, true, false, true)
    val (res2, constraints2) = countPositiveBits(bits2)
    assert(checkNumber(res2, constraints2, List(true, true)))
    assert(!checkNumber(res2, constraints2, List(true, true, true)))

    val bits4: List[Formula] = List(false, true)
    val (res4, constraints4) = countPositiveBits(bits4)
    assert(checkNumber(res4, constraints4, List(true)))
  }

  test("countPositiveBits of empty list counts 0") {
    val bits1: List[Formula] = List()
    val (res1, constraints1) = countPositiveBits(bits1)
    assert(checkNumber(res1, constraints1, List(false)))
    assert(!checkNumber(res1, constraints1, List(true)))
  }

  test("atMostMaxTrue works with one bit") {
    assert(solveForSatisfiability(atMostMaxTrue(List(false), 1)) != None)
    assert(solveForSatisfiability(atMostMaxTrue(List(true), 1)) != None)
  }

  test("atMostMaxTrue works with max of zero") {
    assert(solveForSatisfiability(atMostMaxTrue(List(true), 0)) == None)
    assert(solveForSatisfiability(atMostMaxTrue(List(false), 0)) != None)
  }

  test("atMostMaxTrue works on empty list") {
    assert(solveForSatisfiability(atMostMaxTrue(List(), 0)) != None)
    assert(solveForSatisfiability(atMostMaxTrue(List(), 1)) != None)
  }

  test("atMostMaxTrue works with constants") {
    assert(solveForSatisfiability(atMostMaxTrue(List(false, false, false), 1)) != None)
    assert(solveForSatisfiability(atMostMaxTrue(List(true, false, false), 1)) != None)
    assert(solveForSatisfiability(atMostMaxTrue(List(true, false, true), 1)) == None)
    assert(solveForSatisfiability(atMostMaxTrue(List(true, false, true), 2)) != None)
    assert(solveForSatisfiability(atMostMaxTrue(List(true, true, false, true), 2)) == None)
    assert(solveForSatisfiability(atMostMaxTrue(List(true, true, false, true), 5)) != None)
  }

  val v1 = Volunteer("v1")
  val v2 = Volunteer("v2")
  val v3 = Volunteer("v3")
  val v4 = Volunteer("v4")
  val v5 = Volunteer("v5")
  val v6 = Volunteer("v6")
  val v7 = Volunteer("v7")
  val v8 = Volunteer("v8")
  val v9 = Volunteer("v9")
  val t1 = Task("t1", 1)
  val t2 = Task("t2", 1)
  val t3 = Task("t3", 1)
  val t4 = Task("t4", 2)
  val t5 = Task("t5", 2)
  val t6 = Task("t6", 3)
  val t7 = Task("t7", 3)

  test("schedule is implemented") {
    schedule(List(v1), List(t1), Map(v1 -> List(t1)), 1)
  }

  test("schedule is working with one volunteer and one task") {
    val res = schedule(List(v1), List(t1), Map(v1 -> List(t1)), 1)
    assert(res != None)
    res.foreach(m => assert(m(t1) === List(v1)))
  }

  test("schedule is working with two volunteers and two tasks") {
    val r1 = schedule(List(v1, v2), List(t1, t2), Map(v1 -> List(t1), v2 -> List(t2)), 1)
    assert(r1 != None)
    r1.foreach(m => {
      assert(m(t1) === List(v1))
      assert(m(t2) === List(v2))
    })

    val r2 = schedule(List(v1, v2), List(t1, t2), Map(v1 -> List(t2), v2 -> List(t1)), 1)
    assert(r2 != None)
    r2.foreach(m => {
      assert(m(t1) === List(v2))
      assert(m(t2) === List(v1))
    })
  }

  test("schedule volunteer to several tasks under max workload") {
    val res = schedule(List(v1), List(t1, t2), Map(v1 -> List(t1, t2)), 2)
    assert(res != None)
    res.foreach(m => {
      assert(m(t1) === List(v1))
      assert(m(t2) === List(v1))
    })
  }

  test("T0: schedule volunteers to several tasks under max workload") {
    val res = schedule(List(v1, v2), List(t1, t2, t4), Map(v1 -> List(t1, t4), v2 -> List(t2, t4)), 2)
    assert(res != None)
    res.foreach(m => {
      assert(m(t1) === List(v1))
      assert(m(t2) === List(v2))
      assert(m(t4) === List(v1, v2))
    })
  }

  test("T1: schedule volunteers to several tasks under max workload") {
    val res = schedule(List(v1, v2, v3, v4), List(t1, t4, t6),
      Map(
        v1 -> List(t1, t6),
        v2 -> List(t4),
        v3 -> List(t4, t6),
        v4 -> List(t6)), 2)
    assert(res != None)
    res.foreach(m => {
      assert(m(t1) === List(v1))
      assert(m(t4) === List(v2, v3))
      assert(m(t6) === List(v1, v3, v4))
    })
  }

  test("T2: no unnecessary volunteers for task") {
    val res = schedule(List(v1, v2), List(t1), Map(v1 -> List(t1), v2 -> List(t1)), 2)
    assert(res != None)
    res.foreach(m => {
      assert(m(t1) === List(v1) || m(t1) === List(v2))
    })
  }

  test("T3: schedule volunteers to several tasks under max workload") {
    val res = schedule(
      List(v1, v2, v3, v4, v5, v6),
      List(t1, t4, t6, t7),
      Map(
        v1 -> List(t6, t7),
        v2 -> List(t6),
        v3 -> List(t1, t4, t7),
        v4 -> List(t6, t7),
        v5 -> List(t7),
        v6 -> List(t4)), 2)
    assert(res != None)
    res.foreach(m => {
      assert(m(t1) === List(v3))
      assert(m(t4) === List(v3, v6))
      assert(m(t6) === List(v1, v2, v4))
      assert(m(t7) === List(v1, v4, v5))
    })
  }

  test("T4: schedule volunteers to several tasks under max workload") {
    val res = schedule(
      List(v1, v2, v3, v4, v6),
      List(t1, t4, t6, t7),
      Map(
        v1 -> List(t6, t7),
        v2 -> List(t1, t6, t7),
        v3 -> List(t1, t4, t6, t7),
        v4 -> List(t6, t7),
        v6 -> List(t4)), 2)
    assert(res != None)
    res.foreach(m => {
      assert(m(t1) === List(v3) || m(t1) === List(v2))
      assert(m(t4) === List(v3, v6))
      assert(m(t6) === List(v1, v2, v3) || m(t6) === List(v1, v2, v4) ||
        m(t6) === List(v1, v3, v4) || m(t6) === List(v2, v3, v4))
      assert(m(t7) === List(v1, v2, v3) || m(t7) === List(v1, v2, v4) ||
        m(t7) === List(v1, v3, v4) || m(t7) === List(v2, v3, v4))
    })
  }

  test("schedule returns None on an impossible problem") {
    val r1 = schedule(List(v1, v2), List(t1, t2), Map(v1 -> List(t1), v2 -> List(t1)), 1)
    assert(r1 === None)
  }


  def checkBalelecScheduling(
    solution: Map[Task, List[Volunteer]],
    volunteers: List[Volunteer], tasks: List[Task],
    availability: Map[Volunteer, List[Task]], maxWorkload1: Int
  ): Boolean = {
    solution.forall{ case (t, vs) => t.capacity == vs.size } &&
    solution.keys.toSet == tasks.toSet &&
    solution.forall{ case (t, vs) => vs.forall(v => availability(v).contains(t)) }
  }

  def checkAssignment(
    assignment: Array[List[Int]],
    people: Array[List[Int]], slots: Array[Int], max: Int
  ): Unit = {
    val counter = Array.fill(people.size)(0)
    assert(assignment.size === slots.size)
    for(i <- 0 until assignment.size) {
      assert(assignment(i).size === slots(i))
      assignment(i).foreach(p => {
        assert(people(p).contains(i))
        counter(p) = counter(p) + 1
      })
    }
    for(i <- 0 until people.size) {
      assert(counter(i) <= max)
    }
  }

  def checkNumber(res: List[Formula], context: Set[Formula], expected: List[Boolean]): Boolean = {

    val rres = res.reverse

    val digitsOk = and(rres.zip(expected.reverse).map(p => p._1 iff p._2):_*)
    val leadingZeros = !or(rres.drop(expected.size):_*)

    val theorem = digitsOk && leadingZeros && and(context.toSeq:_*)
    expected.size <= res.size && solveForSatisfiability(theorem) != None
  }

/*
  test("checkNumber is testing what it is supposed to") {
    assert(checkNumber(List(true), Set(), List(true)))
    assert(checkNumber(List(false), Set(), List(false)))
    assert(checkNumber(List(true, false), Set(), List(true, false)))
    assert(checkNumber(List(true, true), Set(), List(true, true)))
    assert(checkNumber(List(false, true), Set(), List(true)))
    assert(checkNumber(List(false, false, true), Set(), List(true)))
    assert(!checkNumber(List(true), Set(), List(false)))
    assert(!checkNumber(List(false), Set(), List(true)))
    assert(!checkNumber(List(true), Set(), List(true, true)))
    assert(!checkNumber(List(false), Set(), List(true, false)))
  }
  */

}
