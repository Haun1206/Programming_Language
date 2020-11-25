package cs320

package object hw09 extends Homework09 {
  def mustSame(left:Type, right:Type):Type =
    if (same(left, right)) left
    else error(s"$left is not equal to $right")

  def same(left:Type, right:Type) : Boolean = (left, right) match{
    case (NumT, NumT) => true
    case (BoolT, BoolT) => true
    case (ArrowT(ph1::pt1, r1), ArrowT(ph2::pt2, r2)) => (pt1, pt2) match {
      case (Nil, Nil) => same(ph1, ph2) && same(r1, r2)
      case _ => same(ArrowT(pt1, r1), ArrowT(pt2, r2))
    }
    case (IdT(x1), IdT(x2)) => true
    case _ => false
  }

  def mustSameList(t:Type, l:List[Type], b:Boolean):Type =
    if(b) {
      l match{
        case Nil => t
        case lh::lt => mustSameList(t, lt, b&&same(t, lh))
      }
    }
    else error(s"$l's elements are not same")

  def parameterTotype(p:List[(String, Type)], l:List[Type]):List[Type] = p match{
    case Nil => l.reverse
    case (s, t)::pt => parameterTotype(pt, t::l)
  }

  def parameterTostring(p:List[(String, Type)], l:List[String]):List[String] = p match{
    case Nil => l.reverse
    case (s, t)::pt => parameterTostring(pt, s::l)
  }

  def addEnv(l:List[(String, Type)], tyEnv:TyEnv):TyEnv = l match{
    case Nil => tyEnv
    case (s, t)::lt => addEnv(lt, tyEnv.addVar(s, t, mutable=false))
  }

  def vaildType(ty:Type, tyEnv:TyEnv): Type = ty match{
    case NumT => ty
    case BoolT => ty
    case ArrowT(p, r) => ArrowT(vaildlistType(p, tyEnv, List()), vaildType(r, tyEnv))
    case IdT(x) =>
      if (tyEnv.tbinds.contains(x)) ty
      else error(s"$x is a free type")
  }

  def vaildlistType(p:List[Type], tyEnv:TyEnv, r:List[Type]) : List[Type] = p match {
    case Nil => r.reverse
    case ph::pt =>
      vaildType(ph, tyEnv)
      vaildlistType(pt, tyEnv, ph::r)
  }

  def traitEnv(n:String, c:Map[String, List[Type]], tyEnv:TyEnv):TyEnv = {
    if (c.isEmpty) tyEnv
    else {
      val styEnv = tyEnv.addVar(c.head._1, ArrowT(c.head._2, IdT(n)), mutable = false)
      val sc = c-c.head._1
      traitEnv(n, sc, styEnv)
    }
  }

  def CheckTypeList(c:Map[String, List[Type]], l:List[Type]):List[Type] = {
    if(c.isEmpty) l
    else {
      val list = c.head._2
      CheckTypeList(c-c.head._1, list++l)
    }
  }

  def lookup(x:String, tyEnv:TyEnv):Type = tyEnv.varMap.get(x) match{
    case None => tyEnv.tbinds.get(x) match{
      case None => error(s"free identifier: $x")
      case Some(v) => IdT(x)
    }
    case Some(v) => v
  }

  def lookupEnv(x:String, env:Env):Value = env.get(x) match{
    case Some(v) => v
  }
  def lookupSto(n:Addr, sto:Sto):Value = sto.get(n) match{
    case Some(v) => v
  }

  def lookupCase(n:String, m:Map[String, (List[String], Expr)]):(List[String], Expr) = m.get(n) match{
    case Some(v) => v
  }

  def typeChecklist(l:List[Expr], tyEnv:TyEnv, ltype:List[Type]):List[Type] = l match{
    case Nil => ltype.reverse
    case lh::lt => typeChecklist(lt, tyEnv, typeCheck(lh, tyEnv)::ltype)
  }

  def malloc(sto: Sto): Addr =
    sto.foldLeft(0){case (max, (addr,_)) => math.max(max, addr)} +1

  def isIdT(t:Type):String = t match{
    case IdT(n) => n
    case _ => error(s"$t is not IdT")
  }

  def makeTypeList(cs:Map[String, List[Type]], c:Map[String, (List[String], Expr)], tyEnv:TyEnv, l:List[Type]): List[Type] = {
    if (c.isEmpty) l.reverse
    else {
      val et = typeCheck(c.head._2._2, addMapintoTyEnv(maketyEnv(c.head._2._1, cs.getOrElse(c.head._1, error("match fail")), Map()), tyEnv))
      makeTypeList(cs, c-c.head._1, tyEnv, et::l)
    }
  }

  def maketyEnv(l:List[String], r:List[Type], te:Map[String, Type]):Map[String, Type] =
    if (l.size == r.size){
      (l, r) match {
      case (Nil, Nil) => te
      case (lh :: lt, rh :: rt) => maketyEnv(lt, rt, te + (lh -> rh))
      }
    }
    else error(s"error")

  def makeEnv(l:List[String], r:List[Value], m:Map[String, Value]):Map[String, Value] = (l, r) match{
    case (Nil, Nil) => m
    case (lh::lt, rh::rt) => makeEnv(lt, rt, m+(lh -> rh))
  }

  def addMapintoTyEnv(m:Map[String, Type], tyEnv:TyEnv):TyEnv = {
    if(m.isEmpty) tyEnv
    else{
      val h = m.head
      addMapintoTyEnv(m-h._1, tyEnv.addVar(h._1, h._2, mutable = false))
    }
  }

  def addConVinEnv(c:Map[String, List[Type]], env:Env):Env = {
    if (c.isEmpty) env
    else{
      val ch = c.head
      addConVinEnv(c-ch._1, env + (ch._1 -> ConstructorV(ch._1)))
    }
  }

  def numAdd(x: Value, y:Value):Value = (x, y) match{
    case (NumV(n), NumV(m)) => NumV(n + m)
    case _ => error(s"not both numbers: $x, $y")
  }

  def numSub(x: Value, y:Value):Value = (x, y) match{
    case (NumV(n), NumV(m)) => NumV(n - m)
    case _ => error(s"not both numbers: $x, $y")
  }

  def numEq(x: Value, y:Value):Boolean = (x, y) match{
    case (NumV(n), NumV(m)) => n==m
  }

  def numLt(x: Value, y:Value):Boolean = (x, y) match{
    case (NumV(n), NumV(m)) => n < m
  }

  def isAddrV(v: Value):Boolean = v match{
    case AddrV(n) => true
    case _ => false
  }

  def isExprV(v: Value):Boolean = v match{
    case ExprV(e, env) => true
    case _ => false
  }

  def isCloV(v:Value):Boolean = v match{
    case CloV(p, b, e) => true
    case _ => false
  }

  def getAddr(v: Value):Addr = v match{
    case AddrV(n) => n
  }

  def getExprV(v: Value):(Expr, Env) = v match{
    case ExprV(e, env) => (e, env)
  }

  def getCloV(v:Value):(List[String], Expr, Env)= v match{
    case CloV(p, b, e) => (p, b, e)
  }

  def getConstructorV(v: Value):String = v match{
    case ConstructorV(n) => n
  }

  def getBool(v:Value):Boolean = v match{
    case BoolV(b) => b
  }

  def getVariantV(v:Value):(String, List[Value]) = v match{
    case VariantV(n, v) => (n, v)
  }

  def interpList(a:List[Expr], env:Env, sto:Sto, l:List[Value]):(List[Value], Sto) = a match{
    case ah::at=> at match{
      case Nil =>
        val (ahv, ahs) = interp(ah, env, sto)
        val list = ahv :: l
        (list.reverse, ahs)
      case ath::att =>
        val (ahv, ahs) = interp(ah, env, sto)
        interpList(at, env, ahs, ahv::l)
    }
    case Nil => (l, sto)
  }

  def typeCheck(e: Expr, tyEnv: TyEnv): Type = e match{
    case Num(n) => NumT
    case Bool(b) => BoolT
    case Add(l, r) =>
      mustSame(typeCheck(l, tyEnv), NumT)
      mustSame(typeCheck(r, tyEnv), NumT)
      NumT
    case Sub(l, r) =>
      mustSame(typeCheck(l, tyEnv), NumT)
      mustSame(typeCheck(r, tyEnv), NumT)
      NumT
    case Eq(l, r) =>
      mustSame(typeCheck(l, tyEnv), NumT)
      mustSame(typeCheck(r, tyEnv), NumT)
      BoolT
    case Lt(l, r) =>
      mustSame(typeCheck(l, tyEnv), NumT)
      mustSame(typeCheck(r, tyEnv), NumT)
      BoolT
    case Id(n) =>lookup(n, tyEnv)
    case Fun(p, b) =>
      vaildlistType(parameterTotype(p, List()), tyEnv, List())
      ArrowT(parameterTotype(p, List()), typeCheck(b, addEnv(p, tyEnv)))
    case App(f, a) =>
      val funT = typeCheck(f, tyEnv)
      val argT = typeChecklist(a, tyEnv, List())
      funT match{
        case ArrowT(p, r) => if(p==argT) r else error(s"$p is not equal to $argT")
        case _ => error(s"apply $argT to $funT")
      }
    case Block(s, e) =>
      typeCheck(e, (tyEnv /: s)(typeCheck))
    case Assign(n, e) =>
      val nameT = typeCheck(Id(n), tyEnv)
      if (tyEnv.mutables.contains(n)) mustSame(typeCheck(e, tyEnv), nameT)
      else error(s"$n is not mutable")
      nameT
    case Match(e, c) =>
      val es = isIdT(typeCheck(e, tyEnv))
      val cs = tyEnv.tbinds.getOrElse(es, error(s"$es is a free type"))
      val typelist = makeTypeList(cs, c, tyEnv, List())
      mustSameList(typelist.head, typelist, true)
    case IfThenElse(c, t, e) =>
      mustSame(typeCheck(c, tyEnv), BoolT)
      mustSame(typeCheck(t, tyEnv), typeCheck(e, tyEnv))
  }
  def typeCheck(tyEnv: TyEnv, stmt: Stmt): TyEnv = stmt match{
    case Val(iL, n, t, e) =>
      vaildType(t, tyEnv)
      mustSame(t, typeCheck(e, tyEnv))
      tyEnv.addVar(n, t, mutable=false)
    case Var(n, t, e) =>
      vaildType(t, tyEnv)
      mustSame(t, typeCheck(e, tyEnv))
      tyEnv.addVar(n, t, mutable =true)
    case Def(n, p, rT, b) =>
      vaildlistType(rT::parameterTotype(p, List()), tyEnv, List())
      val styEnv = tyEnv.addVar(n, ArrowT(parameterTotype(p, List()), rT), mutable=false)
      mustSame(rT, typeCheck(b, addEnv(p, styEnv)))
      styEnv
    case Trait(n, c) =>
      val styEnv = tyEnv.addTBind(n, c)
      val ttyEnv = traitEnv(n, c, styEnv)
      vaildlistType(CheckTypeList(c, List()), ttyEnv, List())
      ttyEnv
  }
  def interp(e: Expr, env: Env, sto: Sto): (Value, Sto) = e match{
    case Num(n) => (NumV(n), sto)
    case Bool(b) => (BoolV(b), sto)
    case Add(l, r) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (numAdd(lv, rv), rs)
    case Sub(l, r) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (numSub(lv, rv), rs)
    case Eq(l, r) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (BoolV(numEq(lv, rv)), rs)
    case Lt(l, r) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (BoolV(numLt(lv, rv)), rs)
    case Id(n) => {
      val v = lookupEnv(n, env)
      if (isAddrV(v)) {
        val ev = lookupSto(getAddr(v), sto)
        if(isExprV(ev)) {
          val (ex, exenv) = getExprV(ev)
          val (fv, fs) = interp(ex, exenv, sto)
          (fv, fs + (getAddr(v) -> fv))
        }
        else (ev, sto)
      }
      else (v, sto)
    }
    case Fun(p, b) => (CloV(parameterTostring(p, List()), e, env), sto)
    case App(f, a) =>
      val (fv, fs) = interp(f, env, sto)
      if(isCloV(fv)) {
        val (p, b, e) = getCloV(fv)
        val (av, as) = interpList(a, env, fs, List())
        interp(b, e ++ makeEnv(p, av, Map()), as)
      }
      else{
        val x = getConstructorV(fv)
        val (av, as) = interpList(a, env, fs, List())
        (VariantV(x, av), as)
      }
    case Block(s, e) =>
      val (senv, ssto) = ((env, sto) /: s)(interp)
      interp(e, senv, ssto)
    case Assign(n, e) =>
      val addr = lookupEnv(n, env)
      val (ev, es) = interp(e, env, sto)
      (ev, es + (getAddr(addr) -> ev))
    case Match(e, c) =>
      val (ev, es) = interp(e, env, sto)
      val (s, l) = getVariantV(ev)
      val (list, expr) = lookupCase(s, c)
      interp(expr, env ++ makeEnv(list, l, Map()), es)
    case IfThenElse(c, t, e) =>
      val (cv, cs) = interp(c, env, sto)
      if(getBool(cv)) interp(t, env, cs)
      else interp(e, env, cs)
  }
  def interp(pair: (Env, Sto), stmt: Stmt): (Env, Sto) = stmt match{
    case Val(iL, n, ty, e) =>
      if(iL){
        val a = malloc(pair._2)
        (pair._1 + (n -> AddrV(a)), pair._2 + (a -> ExprV(e, pair._1)))
      }
      else {
        val (v, s) = interp(e, pair._1, pair._2)
        (pair._1 + (n -> v), s)
      }
    case Var(n, ty, e) =>
      val (v, s) = interp(e, pair._1, pair._2)
      val a = malloc(s)
      (pair._1 + (n -> AddrV(a)), s + (a -> v))
    case Def(n, p, rT, b) =>
      val cloV = CloV(parameterTostring(p, List()), b, pair._1)
      cloV.env = pair._1 + (n -> cloV)
      (cloV.env, pair._2)
    case Trait(n, c) =>
      (addConVinEnv(c, pair._1), pair._2)
  }
  def tests: Unit = {
    test(run("""
      var x: Int = 1
      val y: Int = (x = 3)
      x + y
    """), "6")
    test(run("""
      var x: Int = 1
      lazy val y: Int = (x = 3)
      x + y + x
    """), "7")
    test(run("""
      var x: Int = 0
      lazy val y: Int = (x = x + 1)
      val z: Int = y + y + y + y
      z"""), "4")
    testExc(run("""val x: Int = 42; x = 24"""), "")
    testExc(run("""
      def interp(e: AE): Int = e match {
        case Num(n) => n
        case Add(l, r) => interp(l) + interp(r)
        case Sub(l, r) => interp(l) - interp(r)
      }
      interp(Add(Num(2), Sub(Num(3), Num(1))))
    """), "")
    test(run("""
      trait AE
      case class Num(Int)
      case class Add(AE, AE)
      case class Sub(AE, AE)

      def interp(e: AE): Int = e match {
        case Num(n) => n
        case Add(l, r) => interp(l) + interp(r)
        case Sub(l, r) => interp(l) - interp(r)
      }

      interp(Add(Num(2), Sub(Num(3), Num(1))))
    """), "4")


  }
}
