import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Foundation.FirstOrder.Arithmetic.HFS.Vec
import Mathlib.Tactic.Ring

/-! Represented binomial coefficients at arbitrary internal indices.
A Pascal row is an internal Foundation vector (`x ∷ xs`); the next row is
`v.[0] ∷ adjacent v`, where `adjacent` is a genuine list recursion.
`binom n k` is the `k`-th entry of row `n`, hence zero beyond the row.
No external `Nat.choose`, `List` or `Fin n` with `n : V` is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticBinomPascal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Adjacent sums of an internal vector -/

namespace Adjacent

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y=0”
  adjoin := .mkSigma “y x xs ih. ∃ h, !nthDef h xs 0 ∧ !adjoinDef y (x+h) ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x xs ih := (x+xs.[0]) ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end Adjacent

/-- `adjacent [a₀,…,aₙ] = [a₀+a₁,…,aₙ₋₁+aₙ,aₙ]`. -/
noncomputable def adjacent (v : V) : V := Adjacent.construction.result ![] v

@[simp] theorem adjacent_nil : adjacent (0:V)=0 := by simp [adjacent,Adjacent.construction]
@[simp] theorem adjacent_adjoin (x v : V) : adjacent (x ∷ v)=(x+v.[0]) ∷ adjacent v := by
  simp [adjacent,Adjacent.construction]

def adjacentDef : 𝚺₁.Semisentence 2 := Adjacent.blueprint.resultDef
instance adjacent_defined : 𝚺₁-Function₁[V] adjacent via adjacentDef :=
  Adjacent.construction.result_defined
instance adjacent_definable : 𝚺₁-Function₁[V] adjacent := adjacent_defined.to_definable

@[simp] theorem len_adjacent (v : V) : len (adjacent v)=len v := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih => simp [ih]

theorem adjacent_nth (v i : V) : (adjacent v).[i]=v.[i]+v.[i+1] := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp
  case adjoin x v ih =>
    rcases zero_or_succ i with rfl|⟨i,rfl⟩
    · simp
    · rw [adjacent_adjoin,nth_adjoin_succ,ih,nth_adjoin_succ,nth_adjoin_succ]

/-! ### Pascal rows -/

/-- One Pascal step. -/
noncomputable def nextRow (v : V) : V := v.[0] ∷ adjacent v

def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “out. !adjoinDef out 1 0”
def succDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out previous index. ∃ h, !nthDef h previous 0 ∧ ∃ g, !adjacentDef g previous ∧ !adjoinDef out h g”
def blueprint : PR.Blueprint 0 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := ?[1]
  succ _ _ previous := nextRow previous
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef,nextRow]

/-- The internal Pascal row `n`, a vector of length `n+1`. -/
noncomputable def row (n : V) : V := construction.result ![] n
def rowDef : 𝚺₁.Semisentence 2 := blueprint.resultDef
instance row_defined : 𝚺₁-Function₁[V] row via rowDef := construction.result_defined
instance row_definable : 𝚺₁-Function₁[V] row := row_defined.to_definable

@[simp] theorem row_zero : row (0:V)=?[1] := by simp [row,construction]
theorem row_succ (n : V) : row (n+1)=nextRow (row n) := by
  simp [row,construction]

/-- The represented binomial coefficient. -/
noncomputable def binom (n k : V) : V := (row n).[k]
def binomDef : 𝚺₁.Semisentence 3 := .mkSigma “out n k. ∃ w, !rowDef w n ∧ !nthDef out w k”
def binomDeltaDef : 𝚫₁.Semisentence 3 := binomDef.graphDelta
instance binom_defined : 𝚺₁-Function₂[V] binom via binomDef := .mk fun e => by
  simp [binomDef,binom]
instance binom_defined_delta : 𝚫₁-Function₂[V] binom via binomDeltaDef := binom_defined.graph_delta
instance binom_definable : 𝚺₁-Function₂[V] binom := binom_defined.to_definable

theorem binom_total (n k : V) : ∃! out, binomDef.val.Evalb ![out,n,k] := by simp

@[simp] theorem binom_zero_zero : binom (0:V) 0=1 := by simp [binom]
@[simp] theorem binom_zero_succ (k : V) : binom (0:V) (k+1)=0 := by simp [binom]

theorem binom_succ_zero (n : V) : binom (n+1) 0=binom n 0 := by
  simp [binom,row_succ,nextRow]

/-- Pascal's rule, unconditionally in the column. -/
theorem binom_succ_succ (n k : V) : binom (n+1) (k+1)=binom n k+binom n (k+1) := by
  simp only [binom,row_succ,nextRow,nth_adjoin_succ,adjacent_nth]

@[simp] theorem binom_zero_right (n : V) : binom n 0=1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [binom_succ_zero,ih]

@[simp] theorem len_row (n : V) : len (row n)=n+1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [row_succ,nextRow,ih]

theorem binom_eq_zero_of_lt (n k : V) (h : n<k) : binom n k=0 :=
  nth_lt_len (by simpa [len_row] using lt_iff_succ_le.mp h)

@[simp] theorem binom_self (n : V) : binom n n=1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [binom_succ_succ,ih,binom_eq_zero_of_lt n (n+1) (by simp),add_zero]

theorem binom_one_right (n : V) : binom n 1=n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using binom_zero_succ (0:V)
  case succ n ih =>
    simpa only [zero_add, ih, binom_zero_right, add_comm] using binom_succ_succ n 0

theorem binom_pos (n k : V) (h : k≤n) : 0<binom n k := by
  induction n using ISigma1.sigma1_succ_induction generalizing k with
  | hP => definability
  | zero =>
    have : k=0 := le_antisymm h (by simp)
    simp [this]
  | succ n ih =>
    rcases zero_or_succ k with rfl|⟨k,rfl⟩
    · simp
    · rw [binom_succ_succ]
      exact lt_of_lt_of_le (ih k (by simpa using h)) (by simp)

end DiophantineConsistency.ArithmeticBinomPascal
