package constraints

import cafesat.api.FormulaBuilder._
import cafesat.api.Formulas._
import cafesat.api.Solver._

import scala.annotation.tailrec

/**
  * This object contains utility functions for encoding
  * some arithmetic constraints as boolean ones
  */
object Arithmetic {

  /**
   * Transforms a positive integer in binary form into its integer representation.
   * The `head` element of the input list contains the most
   * significant bit (the list is in big-endian form).
   */
  def binary2int(n: List[Boolean]): Int =
    n.foldLeft(0)((acc, e) => (if (e) 1 else 0) + 2 * acc)

  /**
   * Encodes a positive integer number into base 2.
   * The `head` element of the resulting list contains the most significant
   * bit. This function should not return unnecessary leading zeros.
   */
  def int2binary(n: Int): List[Boolean] = {
    def loop(num: Int, acc: List[Boolean]): List[Boolean] =
        if (num == 0) acc
        else loop(num >> 1, (if ((num & 1) == 1) true else false) :: acc)
    if (n == 0) List(false) else loop(n, List())
  }

  /**
   * This function takes two arguments, both representing positive
   * integers encoded in binary as lists of propositional formulas
   * (true for 1, false for 0). It returns
   * a formula that represents a boolean circuit that constraints
   * `n1` to be less than or equal to `n2`
   */
  private def xor(a: Formula, b: Formula): Formula = (a && !b) || (!a && b)

  /**
    * This function modifies the lengths of two lists of formulae, such that the
    * lengths are equal by adding the needed number of "false" propositions on
    * the left side of the shorter list.
    */
  private def adaptLength(fir: List[Formula], sec: List[Formula]): (List[Formula], List[Formula]) =
    fir.reverse.zipAll(sec.reverse, false: Formula, false: Formula).reverse.unzip

  def lessEquals(n1: List[Formula], n2: List[Formula]): Formula = {
    require((n1 != List()) && (n2 != List()))                           //cannot run function on empty lists
    def greaterThan(ls: List[(Formula, Formula)]): Formula = ls match { //wikipedia: digital comparator
      case (a, b) :: Nil => a && !b
      case (a, b) :: cs => (a && !b) || (!xor(a, b) && greaterThan(cs))
      case _ => sys.error("Unexpected case")
    }
    val (first, second) = adaptLength(n1, n2)
    !greaterThan(first zip second)
    //if the second value is not greater than the first, then the first is less than/equal to the second value
  }

  /**
   * A full adder is a circuit that takes 3 one bit numbers, and returns the
   * result encoded over two bits: (cOut, s)
   */
  def fullAdder(a: Formula, b: Formula, cIn: Formula): (Formula, Formula) =
    ((a && b) || (xor(a, b) && cIn), xor(xor(a, b), cIn) || (a && b && cIn))

  /**
   * This function takes two arguments, both representing positive integers
   * encoded as lists of propositional variables. It returns a pair.
   *
   * The first element of the pair is a `List[Formula]`, and it represents
   * the resulting binary number.
   * The second element is a set of intermediate constraints that are created
   * along the way.
   *
   */
  def adder(n1: List[Formula], n2: List[Formula]): (List[Formula], Set[Formula]) = {
    def loop(ls1: List[Formula], ls2: List[Formula]): (List[Formula], Set[Formula]) = (ls1, ls2) match {
      case (x :: Nil, y :: Nil) => {
        val (head, last) = fullAdder(x, y, false)
        val h, l = propVar()
        (h :: l :: Nil, Set(h iff head, l iff last))
      }
      case(x :: xs, y :: ys) => {
        val (z :: zs, vars) = loop(xs, ys)
        val (head, second) = fullAdder(x, y, z)
        val h, s = propVar()
        (h :: s :: zs, vars + (h iff head) +(s iff second))
        //the list takes h unconditionally because it is used as a carry in outer iteration
      }
      case _ => sys.error("Unexpected case")
    }
    val (l1, l2) = adaptLength(n1, n2)
    loop(l1, l2)
  }

  /**
   * A helper function that creates a less-equals formula
   * taking an integer and a formula as parameters
   */
  def lessEqualsConst(cst: Int, n: List[Formula]): Formula = {
    lessEquals(int2binary(cst), n)
  }

  /**
   * A helper function that creates a less-equals formula
   * taking a formula and an integer as parameters
   */
  def lessEqualsConst(n: List[Formula], cst: Int): Formula = {
    lessEquals(n, int2binary(cst))
  }


}
