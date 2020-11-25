package cs320

package object hw06 extends Homework06 {
  def run(str: String): String ={

    trait SRBFAEValue
    case class NumV(n:Int) extends SRBFAEValue
    case class CloV(x: String, b: SRBFAE, env: Env) extends SRBFAEValue
    case class BoxV(addr: Addr) extends SRBFAEValue
    case class RecV(reco: Reco) extends SRBFAEValue

    type Addr = Int
    type Reco = List[String]
    type Env = Map[String, SRBFAEValue]
    type Sto = Map[Addr, SRBFAEValue]
    type Fie = Map[String, SRBFAEValue]

    def lookup(name: String, env: Env): SRBFAEValue = env.get(name) match{
        case Some(v) => v
        case None => error(s"free identifier: $name")
    }

    def storeLookup(addr: Addr, sto: Sto):SRBFAEValue = sto.get(addr) match{
        case Some(v) => v
        case None => error(s"free identifier: $addr")
    }

    def numOp(op: (Int, Int) => Int): (SRBFAEValue, SRBFAEValue) => SRBFAEValue = (_, _) match{
        case (NumV(x), NumV(y)) => NumV(op(x, y))
        case (x, y) => error(s"not both numbers: $x $y")
    }
    val numVAdd = numOp(_+_)
    val numVSub = numOp(_-_)

    def malloc(sto: Sto): Addr =
        sto.foldLeft(0){ case (max, (addr, _)) => math.max(max, addr) } + 1

    def interp(srbfae: SRBFAE, env: Env, sto: Sto, fie:Fie, list: Reco): (SRBFAEValue, Sto, Fie, Reco) = srbfae match{

        case Num(n) => (NumV(n), sto, fie, list)
        case Add(l, r) =>
            val (lv, ls, lf, ll) = interp(l, env, sto, fie, list)
            val (rv, rs, rf, rl) = interp(r, env, ls, lf, ll)
            (numVAdd(lv, rv), rs, rf, rl)
        case Sub(l, r) =>
            val (lv, ls, lf, ll) = interp(l, env, sto, fie, list)
            val (rv, rs, rf, rl) = interp(r, env, ls, lf, ll)
            (numVSub(lv, rv), rs, rf, rl)
        case Id(n) => (lookup(n, env), sto, fie, list)
        case Fun(p, b) => (CloV(p, b, env), sto, fie, list)
        case App(f, a) =>
            val (fv, fs, ff, fl) = interp(f, env, sto, fie, list)
            fv match{
                case CloV(p, b, fenv) =>
                    val (av, as, af, al) = interp(a, env, fs, ff ,fl)
                    interp(b, fenv + (p -> av), as, af, al)
                case v => error(s"not a closure: $v")
            }
        case NewBox(e) =>
            val (ev, es, ef, el) = interp(e, env, sto, fie, list)
            val addr = malloc(es)
            (BoxV(addr), es+(addr -> ev), ef, el)
        case SetBox(b, e) =>
            val (bv, bs, bf, bl) = interp(b, env, sto, fie, list)
            bv match{
                case BoxV(addr) =>
                    val (ev, es, ef, el) = interp(e, env, bs, bf, bl)
                    (ev, es + (addr -> ev), ef, el)
                case _ => error(s"not a box: $bv")
            }
        case OpenBox(b) =>
            val (bv, bs, bf, bl) = interp(b, env, sto, fie, list)
            bv match{
                case BoxV(addr) => (storeLookup(addr, bs), bs, bf, bl)
                case _ => error(s"not a box: $bv")
            }
        case Seqn(l, r) =>
            val (lv, ls, lf, ll) = interp(l, env, sto, fie, list)
            r match{
                case h::t => interp(Seqn(h, t), env, ls, lf, ll)
                case Nil => (lv, ls, lf, ll)
            }
        case Rec(f) =>
            f match{
            case (x, e)::t =>
                val (ev, es, ef, el) = interp(e, env, sto, fie, list)
                interp(Rec(t), env, es, ef + (x -> ev), x::list)
            case Nil => (RecV(list), sto, fie, List())
            }
        case Get(r, f) =>
            val (rv, rs, rf, rl) = interp(r, env, sto, fie, list)
            rv match{
                case RecV(fi) =>
                  if (fi.contains(f)) rf.get(f) match{
                    case Some(v) => (v, rs, rf, rl)
                    case None => error("no such field")
                  }
                  else error("no such field")
                case _ => error(s"not a record: $rv")
            }
        case Set(r, f, e) =>
            val (rv, rs, rf, rl) = interp(r, env, sto, fie, list)
            rv match{
                case RecV(fi) =>
                  if (fi.contains(f)) {
                    val (ev, es, ef, el) = interp(e, env, rs, rf, rl)
                    (ev, es, ef+(f -> ev), el)
                  }
                  else error("no such field")
                case _ => error(s"not a record: $rv")
            }
        }

    def changeType(e:SRBFAEValue):String = e match{
            case NumV(n) => n.toString
            case CloV(p, b, env) => "function"
            case BoxV(a) => "box"
            case RecV(r) => "record"
    }
    val (v, s, f, l) = interp(SRBFAE(str), Map(), Map(), Map(), List())
    changeType(v)

    }


  def tests: Unit = {
    test(run("""{{fun {b} {seqn {setbox b {+ 2 {openbox b}}}
                          {setbox b {+ 3 {openbox b}}}
                          {setbox b {+ 4 {openbox b}}}
                          {openbox b}}}
                {newbox 1}}"""), "10")
    testExc(run("{get {rec {x 1}} y}"), "no such field")
    test(run("{{fun {r} {seqn {set r x 5} {get r x}}} {rec {x 1}}}"), "5")
    test(run("42"), "42")
    test(run("{fun {x} x}"), "function")
    test(run("{newbox 1}"), "box")
    test(run("{rec}"), "record")

    /* Write your own tests */
    test(run("""{get {rec {x 1} {y 2} {z 3}} y}"""), "2")
    testExc(run("""{seqn {rec {a 1}} {get {rec {b 2}} a}}"""), "no such field")
  }
}
