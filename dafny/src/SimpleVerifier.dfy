module Ints {
  const U32_BOUND: nat := 0x1_0000_0000
  newtype u32 = x:int | 0 <= x < 0x1_0000_0000
  newtype i32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
}

module Lang {
  import opened Ints

  datatype Reg = R0 | R1 | R2 | R3

  datatype Expr =
    | Const(n: u32)
      // overflow during addition is an error
    | Add(r1: Reg, r2: Reg)
      // this is saturating subtraction (to allow comparing numbers)
    | Sub(r1: Reg, r2: Reg)

  datatype Stmt =
    | Assign(r: Reg, e: Expr)
      // Jump by offset if condition is true
    | JmpZero(r: Reg, offset: i32)

  datatype Program = Program(stmts: seq<Stmt>)

}

/* Well-formed check: offsets are all within the program */
/* Main safety property: additions do not overflow */

/* First, we give the concrete semantics of programs. */

module ConcreteEval {
  import opened Ints
  import opened Lang

  type State = Reg -> u32

  function update_state(s: State, r0: Reg, v: u32): State {
    ((r: Reg) => if r == r0 then v else s(r))
  }

  datatype Option<T> = Some(v: T) | None

  function expr_eval(env: State, e: Expr): Option<u32>
  {
    match e {
      case Const(n) => Some(n)
      case Add(r1, r2) =>
        (if (env(r1) as int + env(r2) as int >= U32_BOUND) then None
         else Some(env(r1) + env(r2)))
      case Sub(r1, r2) =>
        (if env(r1) as int - env(r2) as int < 0 then Some(0)
         else Some(env(r1) - env(r2)))
    }
  }

  // stmt_step executes a single statement
  //
  // Returns a new state and a relative PC offset (which is 1 for non-jump
  // statements).
  function stmt_step(env: State, s: Stmt): Option<(State, int)> {
    match s {
      case Assign(r, e) =>
        var e' := expr_eval(env, e);
        match e' {
          case Some(v) => Some((update_state(env, r, v), 1))
          case None => None
        }
      case JmpZero(r: Reg, offset: u32) =>
        Some((env, (if env(r) == 0 then offset else 1) as int))
    }
  }

  datatype ExecResult = Ok(env: State) | NoFuel | Error

  // Run a program starting at pc.
  //
  // The sequence of statements is constant, meant to reflect a static program.
  // Termination occurs if the pc ever reaches exactly the end.
  //
  // Errors can come from either executing statements (see stmt_step for those
  // errors), or from an out-of-bounds pc (negative or not past the end of ss).
  //
  // fuel is needed to make this function terminate; the idea is that if there
  // exists some fuel that makes the program terminate, that is it's complete
  // execution, and if it always runs out of fuel it has an infinite loop.
  function stmts_step(env: State, ss: seq<Stmt>, pc: nat, fuel: nat): ExecResult
    requires pc <= |ss|
    decreases fuel
  {
    if fuel == 0 then NoFuel
    else if pc == |ss| then Ok(env)
    else match stmt_step(env, ss[pc]) {
           case None => Error
           case Some((env', offset)) =>
             if !(0 <= pc + offset <= |ss|) then Error
             else stmts_step(env', ss, pc + offset, fuel - 1)
         }
  }

}

/* Now we turn to analyzing programs */

module AbstractEval {
  import opened Ints
  import opened Lang

  datatype Val = Interval(lo: int, hi: int)

  datatype AbstractState = AbstractState(rs: Reg -> Val)

  function expr_eval(env: AbstractState, e: Expr): Val {
    match e {
      case Const(n) => Interval(n as int, n as int)
      case Add(r1, r2) =>
        var v1 := env.rs(r1);
        var v2 := env.rs(r2);
        Interval(v1.lo + v2.lo, v1.hi + v2.hi)
      case Sub(r1, r2) =>
        var v1 := env.rs(r1);
        var v2 := env.rs(r2);
        Interval(v1.lo - v2.hi, v1.hi - v2.lo)
    }
  }

}
