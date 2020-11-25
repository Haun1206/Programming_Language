package cs320

package object hw07 extends Homework07 {
  def run(str: String): String = {
    trait KXCFAEValue
    case class NumV(n: Int) extends KXCFAEValue
    case class CloV(params: List[String], body: KXCFAE, env: Env) extends KXCFAEValue
    case class ContV(proc: Cont) extends KXCFAEValue
    case object ThrowV extends KXCFAEValue
    type Env = Map[String, KXCFAEValue]
    type Cont = KXCFAEValue => KXCFAEValue

    def numVAdd(x:KXCFAEValue, y:KXCFAEValue):KXCFAEValue = (x, y) match {
      case (NumV(n), NumV(m)) => NumV(n+m)
      case (x, y) => error(s"not both numbers: $x, $y")
    }

    def numVSub(x:KXCFAEValue, y:KXCFAEValue):KXCFAEValue = (x, y) match {
      case (NumV(n), NumV(m)) => NumV(n-m)
      case (x, y) => error(s"not both numbers: $x, $y")
    }
    def calculate (x:List[String], a:List[KXCFAE], b: KXCFAE, e:Env, fe:Env, k:Cont):KXCFAEValue = (x, a)match{
      case (xh::xt, ah::at) =>interp(ah, e, ahv=>ahv match {
          case ThrowV => k(ThrowV)
          case _ => calculate(xt, at, b, e, fe+(xh->ahv),k)
        })
      case (Nil, Nil) => interp(b, fe, k)
    }
    def interp(kxcfae: KXCFAE, env: Env, k: Cont): KXCFAEValue = kxcfae match{
      case Num(n) => k(NumV(n))
      case Add(l, r) => interp(l, env, lv => if(lv == ThrowV) k(ThrowV) else interp(r, env, rv => if(rv ==ThrowV) k(ThrowV) else k(numVAdd(lv, rv))))
      case Sub(l, r) => interp(l, env, lv => if(lv == ThrowV) k(ThrowV) else interp(r, env, rv => if(rv == ThrowV) k(ThrowV) else k(numVSub(lv, rv))))
      case Id(x) => k(env.getOrElse(x, error(s"free identifier: $x")))
      case Fun(ps, b) => k(CloV(ps, b, env))
      case App(f, a) => interp(f, env, fv => fv match{
                            case CloV(x, b, fenv) => if (x.length == a.length) calculate(x, a, b, env, fenv, k) else error("wrong arity")
                            case ContV(kv) => interp(a.head, env, av => if (av ==ThrowV) k(ThrowV) else kv(av))
                            case ThrowV => k(ThrowV)
                            case v => error(s"not a closure: $v")
                          })
      case If0(c, t, e) => interp(c, env, cv => if(cv == ThrowV) k(ThrowV) else{if(cv == NumV(0)) interp(t, env, k) else interp(e, env, k)})
      case Withcc(x, b) => interp(b, env + (x -> ContV(k)), k)
      case Try(t, c) => interp(t, env, tv=> if (tv==ThrowV) interp(c, env, k) else k(tv))
      case Throw => k(ThrowV)
    }

    def changeType(e:KXCFAEValue):String = e match {
      case NumV(n) => n.toString
      case CloV(p, b, env) => "function"
      case ContV(a) => "continuation"
      case ThrowV =>error( "no enclosing try-catch")
    }
    changeType(interp(KXCFAE(str), Map(), x=>x))

  }

  def tests: Unit = {
    test(run("{{fun {x y} {- y x}} 10 12}"), "2")
    test(run("{fun {} 12}"), "function")
    testExc(run("{{fun {x y} 1} 2}"), "wrong arity")
    test(run("{withcc esc {{fun {x y} x} 1 {esc 3}}}"), "3")
    test(run("{try 1 catch 2}"), "1")
    test(run("{try {throw} catch 2}"), "2")
    test(run("{try {+ 1 {throw}} catch 2}"), "2")
    test(run("{{fun {f} {try {f} catch 1}} {fun {} {throw}}}"), "1")
    testExc(run("{throw}"), "no enclosing try-catch")


    /* Write your own tests */
      // 1. some try catch
        // 1. some try catch
        test(run("{try 1 catch 2}"), "1")
        test(run("{try {throw} catch 2}"), "2")
        test(run("{try {+ 1 {+ 1 {+ 1 {throw}}}} catch 2}"), "2")
        test(run("{try {+ 1 {+ 1 {+ 1 {throw}}}} catch {try {throw} catch 3}}"), "3")

        // 2. multiple argument functions
        test(run("{{fun {x y z} {+ {+ x y} z}} 1 2 3}"), "6")

        // 3. given tests which makes the catch part to be evaluated and saved.
        test(run("{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}"), "54") // equal? for multiple recursive try-catch
        test(run("{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}"), "2")

        // given tests
        test(run("{try 7 catch 8}"), "7")
        test(run("{try {throw} catch 8}"), "8")
        test(run("{try {+ 1 {throw}} catch 8}"), "8")
        test(run("{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}"), "8")
        test(run("{try {try {throw} catch 8} catch 9}"), "8")
        test(run("{try {try {throw} catch {throw}} catch 9}"), "9")
        test(run("{try {try 7 catch {throw}} catch 9}"), "7")
        test(run("{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}"), "8")

        // multiple arguments [5]
        test(run("{{fun {x y} {- y x}} 10 12}"), "2")
        test(run("{fun {} 12}"), "function")
        test(run("{fun {x} {fun {} x}}"), "function")
        test(run("{{{fun {x} {fun {} x}} 13}}"), "13")
        test(run("{withcc esc {{fun {x y} x} 1 {esc 3}}}"), "3")

        // exceptions [35]
        test(run("{+ {withcc k {k 5}} 4}"), "9")
        test(run("{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}"), "55") // recursive function
        test(run("{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}"), "100") // exit from recursive function using continuation
        test(run("{withcc k {- 0 {k 100}}}"), "100")
        test(run("{withcc k {k {- 0 100}}}"), "-100")
        test(run("{withcc k {k {+ 100 11}}}"), "111")
        test(run("{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}"), "0")
        test(run("{withcc esc {{fun {x y} x} 1 {esc 3}}}"), "3")
        test(run("{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}"), "20")
        test(run("{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}"), "110") // exit from recursive function using try-catch
        test(run("{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}"), "20110464") // recursive try-catch throwing ("1")
        test(run("{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}"), "0")
        test(run("{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}"), "8")
        test(run("{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}"), "89")
        test(run("{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}"), "11")
        test(run("{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}"), "5")
        test(run("{+ {try {- 10 {throw}} catch 3} 10}"), "13")
        test(run("{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}"), "54")
        test(run("{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}"), "10")
        test(run("{try {- 0 {throw}} catch 5}"), "5")
        test(run("{try {if0 {throw} 3 4} catch 5}"), "5")
        test(run("{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}"), "-1")
        test(run("{try {try {throw} catch {throw}} catch 9}"), "9")
        test(run("{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}"), "8")
        test(run("{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}"), "8")
        test(run("{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}"), "5")
        test(run("{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}"), "10")
        test(run("{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}"), "42")
        test(run("{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}"), "3")
        test(run("{withcc esc {try {+ {throw} {esc 3}} catch 4}}"), "4")
        test(run("{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}"), "15")
        test(run("{try {withcc x {+ {x 1} {throw}}} catch 0}"), "1")
        test(run("{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}"), "19")

        // multiple arguments [6]
        test(run("{+ 999 {withcc done {{fun {f x} {f f x done}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}"), "1099")
        test(run("{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}"), "11053")
        test(run("{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {+ y {g g {- y 1} z}}}} 10}}}"), "0")
        test(run("{withcc done {{fun {f x} {f f x {fun {x} {if0 x {fun {y} {fun {x} {+ x y}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}}"), "64")
        test(run("{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}} 5}"), "continuation")
        test(run("{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}}"), "42")

        // exceptions [4]
        test(run("{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}} catch 4242}"), "4242")
        test(run("{withcc esc {{try {withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} catch esc} 33}}"), "33")
        test(run("{try {try {throw} catch {try {throw} catch {try {throw} catch {+ {withcc k {try {throw} catch {k 0}}} {throw}}}}} catch 0}"), "0")
        test(run("{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {throw}}}}} catch 4242}"), "4242")

  }
}
