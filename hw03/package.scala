package cs320

package object hw03 extends Homework03 {
  def run(str: String): String = {
    trait MRFWAEValue
    case class NumV(n:Int) extends MRFWAEValue
    case class CloV(param:List[String], body:MRFWAE, env:Env) extends MRFWAEValue
    case class RecV(rec:Map[String, MRFWAEValue]) extends MRFWAEValue
    type Env = Map[String, MRFWAEValue]

    def numAdd(x:MRFWAEValue, y:MRFWAEValue):MRFWAEValue = (x, y) match{
     case (NumV(n), NumV(m)) => NumV(n+m)
     case _ => error("wrong arity")
     }

    def numSub(x:MRFWAEValue, y:MRFWAEValue):MRFWAEValue = (x, y) match{
     case (NumV(n), NumV(m)) => NumV(n-m)
     case _ => error("wrong arity")
     }

    def lookup(x: String, env:Env):MRFWAEValue = env.get(x) match{
        case Some(v) => v
        case None => error("wrong arity")
        }

    def lookupRec(x: String, env:Env):MRFWAEValue = env.get(x) match{
        case Some(v) => v
        case None => error("no such field")
        }

    def findMap(ls:List[String], rs:List[MRFWAEValue], env:Env):Env = (ls, rs) match{
        case (Nil, Nil) => env
        case (lh::lt, rh::rt) => findMap(lt, rt, env) + (lh -> rh)
        case _ => error("wrong arity")
        }


    def interp(e:MRFWAE, env:Env):MRFWAEValue = e match{
        case Num(n) => NumV(n)
        case Add(l, r) => numAdd(interp(l, env), interp(r, env))
        case Sub(l, r) => numSub(interp(l, env), interp(r, env))
        case With(x, i, b) => interp(b, env + (x->interp(i, env)))
        case Id(x) => lookup(x, env)
        case App(f, a) => interp(f, env) match{
            case CloV(p, b, menv) => interp(b, findMap(p, a.map(interp(_,env)), menv))
            case _ => error("wrong arity")
        }
        case Fun(p, b) => CloV(p, b, env)
        case Rec(r) => RecV(r.transform((k,v)=>interp(v, env)))
        case Acc(e, n) => interp(e, env) match{
            case RecV(r) => lookupRec(n, r)
            case _ => error("wrong arity")
        }
       }

    def changeType(e:MRFWAEValue):String = e match{
        case NumV(n) => n.toString()
        case CloV(p, b, env) => "function"
        case RecV(r) => "record"
      }
    val env:Env=Map()
    changeType(interp(MRFWAE(str), env))
  }

  def tests: Unit = {
    test(run("{{fun {x y} {+ x y}} 1 2}"), "3")
    test(run("{{fun {} {+ 3 4}}}"), "7")
    testExc(run("{{fun {x y} {+ x y}} 1}"), "wrong arity")
    test(run("{access {record {x 1} {y 2}} x}"), "1")
    testExc(run("{access {record {x 1} {y 2}} z}"), "no such field")
    testExc(run("{record {x {access {record {y 1}} z}}}"), "no such field")
    test(run("42"), "42")
    test(run("{fun {x} x}"), "function")
    test(run("{record {x 1}}"), "record")

    /* Write your own tests */
    test(run("{fun {x} {fun {y} {+ x y}}}"),"function")
    test(run("{{fun {x} {{fun {y} {+ x y}}3}}2}"),"5")
    test(run("{{fun{x y z} {+ x {with {w y} {+ w z}}}} 1 2 3}"), "6")


  }
}
