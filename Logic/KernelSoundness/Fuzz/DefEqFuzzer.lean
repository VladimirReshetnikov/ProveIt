import Lean
/-!
DEFEQ / WHNF CONSISTENCY FUZZER.
For closed `a b : Bool`, if `Kernel.isDefEq a b` but the kernel's own `whnf`
gives different Bool constants, then `rfl : a = true` and `rfl : b = false`
both typecheck while `a ≡ b`, i.e. `true = false`.
-/
open Lean Elab Command Meta

structure P where
  a : Nat
  b : Bool

structure Q where
  a : Bool
  b : Nat

structure UnitLike where

structure Wrap (α : Type) where
  val : α

inductive Ix : Nat → Type where
  | mk : (a b : Nat) → Ix (a + b)

def qrel (_ _ : Bool) : Prop := True

def idB (b : Bool) : Bool := b
def notB : Bool → Bool
  | true => false
  | false => true

private def mkPool : MetaM (Array Expr) := do
  let tt := mkConst ``Bool.true
  let ff := mkConst ``Bool.false
  let bl := mkConst ``Bool
  let mkP (n : Nat) (b : Expr) := mkApp2 (mkConst ``P.mk) (mkNatLit n) b
  let mkQ (b : Expr) (n : Nat) := mkApp2 (mkConst ``Q.mk) b (mkNatLit n)
  let mkW (b : Expr) := mkApp2 (mkConst ``Wrap.mk [levelOne]) bl b
  let mut pool : Array Expr := #[tt, ff]
  for b in [tt, ff] do
    for n in [0, 1, 7] do
      -- honest projections
      pool := pool.push (.proj ``P 1 (mkP n b))
      pool := pool.push (.proj ``Q 0 (mkQ b n))
      pool := pool.push (.proj ``Wrap 0 (mkW b))
      -- 32-bit-truncating projection indices (lean4#12746)
      pool := pool.push (.proj ``P (2^32 + 1) (mkP n b))
      pool := pool.push (.proj ``Q (2^32) (mkQ b n))
      pool := pool.push (.proj ``Wrap (2^32) (mkW b))
      -- structure-name mismatch: kernel `reduce_proj_core` ignores the sname
      pool := pool.push (.proj ``Q 0 (mkP n b))
      pool := pool.push (.proj ``P 1 (mkQ b n))
      pool := pool.push (.proj ``Wrap 0 (mkP n b))
      pool := pool.push (.proj ``UnitLike 0 (mkW b))
      -- through definitions
      pool := pool.push (mkApp (mkConst ``idB) b)
      pool := pool.push (mkApp (mkConst ``notB) b)
      pool := pool.push (mkApp (mkConst ``notB) (mkApp (mkConst ``notB) b))
  -- Nat accelerators
  for (x, y) in [(0,0), (0,1), (2^32, 2^32), (2^32, 2^32+1), (2^64, 2^64), (2^64, 2^63)] do
    pool := pool.push (mkApp2 (mkConst ``Nat.beq) (mkNatLit x) (mkNatLit y))
    pool := pool.push (mkApp2 (mkConst ``Nat.ble) (mkNatLit x) (mkNatLit y))
  -- Quot
  let rel := mkConst ``qrel
  for b in [tt, ff] do
    let q := mkApp3 (mkConst ``Quot.mk [levelOne]) bl rel b
    let idf := Expr.lam `x bl (.bvar 0) .default
    let hyp := Expr.lam `x bl (.lam `y bl (.lam `h (mkApp2 rel (.bvar 1) (.bvar 0))
                 (mkApp2 (mkConst ``rfl [levelOne]) bl (.bvar 2)) .default) .default) .default
    pool := pool.push (mkApp6 (mkConst ``Quot.lift [levelOne, levelOne]) bl rel bl idf hyp q)
  -- Bool.rec
  for b in [tt, ff] do
    pool := pool.push (mkApp4 (mkConst ``Bool.rec [levelOne])
      (Expr.lam `x bl bl .default) ff tt b)
  -- Eq.rec / K-like reduction on Eq
  for b in [tt, ff] do
    for m in [tt, ff] do
      let h := mkApp2 (mkConst ``rfl [levelOne]) bl b
      let motive := Expr.lam `x bl
        (.lam `hh (mkApp3 (mkConst ``Eq [levelOne]) bl b (.bvar 0)) bl .default) .default
      pool := pool.push (mkAppN (mkConst ``Eq.rec [levelOne, levelOne]) #[bl, b, motive, m, b, h])
  return pool

run_cmd do
  let env ← getEnv
  let pool ← liftTermElabM mkPool
  let vals : Array (Option Bool) := pool.map fun e =>
    match Lean.Kernel.whnf env {} e with
    | .ok r => if r.isConstOf ``Bool.true then some true
               else if r.isConstOf ``Bool.false then some false else none
    | .error _ => none
  let mut bad : Nat := 0
  let mut pairs : Nat := 0
  let mut stuck : Nat := 0
  for v in vals do
    if v.isNone then stuck := stuck + 1
  for i in [0:pool.size] do
    for j in [0:pool.size] do
      match vals[i]!, vals[j]! with
      | some x, some y =>
        if x != y then
          pairs := pairs + 1
          match Lean.Kernel.isDefEq env {} pool[i]! pool[j]! with
          | .ok true =>
              bad := bad + 1
              if bad ≤ (10 : Nat) then
                logError m!"*** DEFEQ UNSOUNDNESS ***\n  {pool[i]!}  (whnf {x})\n  ===\n  {pool[j]!}  (whnf {y})"
          | _ => pure ()
      | _, _ => pure ()
  logInfo m!"[defeq] pool={pool.size} stuck={stuck} differingPairs={pairs} UNSOUND={bad}"
