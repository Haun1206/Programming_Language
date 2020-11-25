package cs320

import cs320._

package object hw02 extends Homework02 {
  // applies a binary numeric function on all combinations of numbers from
  // the two input lists, and return the list of all of the results
  def binOp(
    op: (Int, Int) => Int,
    ls: List[Int],
    rs: List[Int]
  ): List[Int] = ls match {
    case Nil => Nil
    case l :: rest =>
      def f(r: Int): Int = op(l, r)
      rs.map(f) ++ binOp(op, rest, rs)
  }

  def run(str: String): List[Int] = {
    def lookup(name : String, env : Map[String, List[Int]]):List[Int] = env.get(name) match{
        case Some(v) => v
        case None => error(s"free identifier: $name")
    }
    def max(x:Int, y:Int) : Int = if (x>y) x else y

    def min(x:Int, y:Int) : Int = if (x>y) y else x

    def interp(mua : MUWAE, env: Map[String, List[Int]]) : List[Int] = mua match{
        case Num(n) => n
        case Add(l, r) => binOp(_+_, interp(l, env), interp(r, env))
        case Sub(l, r) => binOp(_-_, interp(l, env), interp(r, env))
        case With(x, i, b) => interp(b, env + (x-> interp(i, env)))
        case Id(x) => lookup(x, env)
        case Max(l,m,r) => binOp(max, binOp(max, interp(l, env), interp(m, env)), interp(r, env))
        case Min(l,m,r) => binOp(min, binOp(min, interp(l, env), interp(m, env)), interp(r, env))
    }
    interp(MUWAE(str), Map())
   }

  def tests: Unit = {
    test(run("{+ 3 7}"), List(10))
    test(run("{- 10 {3 5}}"), List(7, 5))
    test(run("{with {x {+ 5 5}} {+ x x}}"), List(20))
    test(run("{min 3 4 5}"), List(3))
    test(run("{max {+ 1 2} 4 5}"), List(5))
    test(run("{min {1 4} {2 9} 3}"), List(1, 1, 2, 3))
    test(run("{max {1 6} {2 5} {3 4}}"), List(3, 4, 5, 5, 6, 6, 6, 6))

    /* Write your own tests */
    test(run("{+ {1 2} {1 2}}"), List(2, 3, 3, 4))
    test(run("{+ 3 {with {x {+ 1 2}} {+ x {2 4 6}}}}"), List(8, 10, 12))
    test(run("{with {x {+ 0 2}} {with {x 5} {+ x x}}}"), List(10))
    test(run("{min {} {1 2} {3 4}}"), List())
    test(run("{+ {} 2}"), List())
    test(run("{min 0 {max {0 1} {1 2} 1} 1}"), List(0,0,0,0))
    test(run("{max 1 {max {0 1} {1 2} 1} {1 2}}"), List(1,2,2,2,1,2,2,2))
    test(run("{with {x {1 2}} {+ x x}}"), List(2,3,3,4))

  }
}
