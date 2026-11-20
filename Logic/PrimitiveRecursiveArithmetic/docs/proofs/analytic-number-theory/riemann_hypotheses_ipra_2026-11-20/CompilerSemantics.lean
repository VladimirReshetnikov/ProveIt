import PacketLanguage

/-! Semantics in the standard natural numbers. The compiler theorem checks
    the indexing of nested loops against an independent interpretation of
    the source expressions. It is a theorem about syntax and evaluation. -/
namespace PacketLanguage
open LeanProofs.ConciseIPRA

/-- Interpretation of a fixed, well-founded PR syntax tree. This Lean
    metatheoretic function is not a primitive recursive universal evaluator. -/
def value : {k : Nat} → PR k → (Fin k → Nat) → Nat
  | _, .zero, _ => 0
  | _, .succ, e => e 0 + 1
  | _, .proj i, e => e i
  | _, .comp f gs, e => value f (fun i => value (gs i) e)
  | _, .prec f g, e =>
    let params := fun i => e i.succ
    Nat.rec (value f params)
      (fun j a => value g (Fin.cases j (Fin.cases a params))) (e 0)

private theorem value_comp {m k} (f : R m) (g : Fin m → R k) (e : Fin k → Nat) :
    value (.comp f g) e = value f (fun i => value (g i) e) := by rw [value]

private theorem value_prec {k} (f : R k) (g : R (k+2)) (e : Fin (k+1) → Nat) :
    value (.prec f g) e = Nat.rec (value f (fun i => e i.succ))
      (fun j a => value g (Fin.cases j (Fin.cases a (fun i => e i.succ)))) (e 0) := by rw [value]

@[simp] theorem value_proj {k} (i : Fin k) (e : Fin k → Nat) : value (.proj i) e = e i := by rw [value]
@[simp] theorem value_zeroR {k} (e : Fin k → Nat) : value zeroR e = 0 := by simp [zeroR, value_comp, value]
@[simp] theorem value_sucR {k} (f : R k) (e : Fin k → Nat) : value (sucR f) e = value f e + 1 := by
  simp [sucR, value_comp, value]
@[simp] theorem value_numeral {k} (n : Nat) (e : Fin k → Nat) :
    value (numeral n) e = n := by induction n <;> simp [numeral, *]

private def pairEnv (a b : Nat) : Fin 2 → Nat := Fin.cases a (fun _ => b)

private theorem value_binary {n} (f : R 2) (x y : R n) (e : Fin n → Nat) :
    value (binary f x y) e = value f (pairEnv (value x e) (value y e)) := by
  rw [binary, value_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

@[simp] private theorem pairEnv_zero (a b : Nat) : pairEnv a b 0 = a := rfl
@[simp] private theorem pairEnv_one (a b : Nat) : pairEnv a b 1 = b := rfl

private theorem twoCases {α : Sort _} {n : Nat} (a : α) (g : Fin (n+2) → α) :
    (Fin.cases a g : Fin (n+3) → α) 2 = g 1 := rfl

theorem value_addR (e : Fin 2 → Nat) : value addR e = e 0 + e 1 := by
  simp only [addR, value_prec, value_proj, value_sucR, finCases_one, Fin.cases_zero]
  generalize e 0 = x
  induction x with
  | zero => simp
  | succ j ih => simpa [Nat.succ_add] using congrArg Nat.succ ih

theorem value_mulR (e : Fin 2 → Nat) : value mulR e = e 0 * e 1 := by
  simp only [mulR, value_prec, value_zeroR, value_binary, value_addR, pairEnv_zero, pairEnv_one,
    value_proj, twoCases, finCases_one, Fin.cases_zero]
  change Nat.rec (motive := fun _ => Nat) 0 (fun _ a => a + e 1) (e 0) = _
  generalize e 0 = x
  induction x with
  | zero => simp
  | succ j ih => exact (congrArg (· + e 1) ih).trans (Nat.succ_mul j (e 1)).symm

theorem value_predR (e : Fin 1 → Nat) : value predR e = (e 0).pred := by
  simp only [predR, value_prec, value_proj, Fin.cases_zero]
  cases e 0 <;> rfl

private theorem value_revSub (e : Fin 2 → Nat) : value reversedSub e = e 1 - e 0 := by
  simp only [reversedSub, value_prec, value_comp, value_proj, value_predR, finCases_one]
  change Nat.rec (motive := fun _ => Nat) (e 1) (fun _ a => a.pred) (e 0) = _
  generalize e 0 = x
  induction x with
  | zero => rfl
  | succ j ih => change (Nat.rec (motive := fun _ => Nat) (e 1) (fun _ a => a.pred) j).pred = e 1 - (j + 1)
                 rw [ih, Nat.pred_eq_sub_one, Nat.sub_sub]

theorem value_subR (e : Fin 2 → Nat) : value subR e = e 0 - e 1 := by
  simp [subR, value_binary, value_revSub]

theorem value_powR (e : Fin 2 → Nat) : value powR e = e 0 ^ e 1 := by
  simp only [powR, value_binary, pairEnv_zero, pairEnv_one, value_prec, value_numeral,
    value_mulR, value_proj, twoCases, finCases_one, Fin.cases_zero]
  change Nat.rec (motive := fun _ => Nat) 1 (fun _ a => a * e 0) (e 1) = _
  generalize e 1 = x
  induction x with
  | zero => rfl
  | succ j ih => exact (congrArg (· * e 0) ih).trans (Nat.pow_succ (e 0) j).symm

def bit (x : Nat) := if x = 0 then 0 else 1

theorem value_clipR (e : Fin 1 → Nat) : value clipR e = bit (e 0) := by
  rw [clipR, value_prec]
  cases e 0 <;> simp [bit, value]

theorem value_isZeroR (e : Fin 1 → Nat) : value isZeroR e = (if e 0 = 0 then 1 else 0) := by
  rw [isZeroR, value_prec]
  cases e 0 <;> simp

theorem value_maxR (e : Fin 2 → Nat) : value maxR e = max (e 0) (e 1) := by
  simp only [maxR, value_binary, value_addR, value_subR, value_proj, pairEnv_zero, pairEnv_one]
  omega

/-- Left fold over 0,1,...,n−1. -/
def overRange (initial : Nat) (update : Nat → Nat → Nat) (n : Nat) : Nat :=
  Nat.rec initial (fun j a => update j a) n

def Aggregate.initial : Aggregate → Nat
  | .product | .everyBit => 1
  | _ => 0

def Aggregate.combine : Aggregate → Nat → Nat → Nat
  | .total, a, b => a+b
  | .product, a, b => a*b
  | .maximum, a, b => max a b
  | .someBit, a, b => bit (a+b)
  | .everyBit, a, b => a * bit b

/-- A direct interpreter of the source language. Its loop body sees the
    counter followed by the old environment; it never sees the accumulator. -/
def denote {ctx : List String} : E ctx → (Fin ctx.length → Nat) → Nat
  | .var i, e => e i
  | .num n, _ => n
  | .app f args, e => value f (fun i => denote (args i) e)
  | .agg k _ b s, e =>
    overRange k.initial (fun i a => k.combine a (denote s (Fin.cases i e))) (denote b e)

private theorem value_cons {n k : Nat} (r : R n) (rs : Fin k → R n) (e : Fin n → Nat) :
    (fun i => value (Fin.cases r rs i) e) = Fin.cases (value r e) (fun i => value (rs i) e) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private def aggInit {n : Nat} : Aggregate → R n
  | .product | .everyBit => numeral 1
  | _ => zeroR

private def aggStep {n : Nat} (kind : Aggregate) (body : R (n+1)) : R (n+2) :=
  let arg : R (n+2) := .comp body (Fin.cases (.proj 0) (fun i => .proj i.succ.succ))
  let acc : R (n+2) := .proj 1
  match kind with
  | .total => binary addR acc arg
  | .product => binary mulR acc arg
  | .maximum => binary maxR acc arg
  | .someBit => .comp clipR (fun _ => binary addR acc arg)
  | .everyBit => binary mulR acc (.comp clipR (fun _ => arg))

private theorem program_agg {ctx} (k : Aggregate) (name : String)
    (b : E ctx) (s : E (name::ctx)) :
    program ctx (.agg k name b s) =
      .comp (.prec (aggInit k) (aggStep k (program _ s)))
        (Fin.cases (program _ b) (fun i => .proj i)) := by cases k <;> rfl

private theorem aggInit_ok {n} (k : Aggregate) (e : Fin n → Nat) :
    value (aggInit k) e = k.initial := by cases k <;> simp [aggInit, Aggregate.initial]

private theorem aggStep_ok {n} (k : Aggregate) (b : R (n+1)) (i a : Nat) (e : Fin n → Nat) :
    value (aggStep k b) (Fin.cases i (Fin.cases a e)) =
      k.combine a (value b (Fin.cases i e)) := by
  cases k <;> simp only [aggStep, Aggregate.combine, value_binary, value_addR, value_mulR,
    value_maxR, value_clipR, pairEnv_zero, pairEnv_one, value_proj, finCases_one,
    Fin.cases_zero, value_comp, value_cons, Fin.cases_succ]

/-- Compilation preserves the value at every assignment and for any nesting
    of the five bounded aggregates. -/
theorem value_program {ctx : List String} (s : E ctx) (e : Fin ctx.length → Nat) :
    value (program ctx s) e = denote s e := by
  induction s with
  | var i => exact value_proj i e
  | num n => exact value_numeral n e
  | app f args ih =>
    change value (.comp f (fun i => program _ (args i))) e = _
    simp only [value_comp, denote, ih]
  | agg k name b s hb hs =>
    rw [program_agg, value_comp, value_cons, value_prec]
    simp only [value_proj, Fin.cases_succ, Fin.cases_zero, hb, denote, overRange,
      aggInit_ok, aggStep_ok, hs]

end PacketLanguage
