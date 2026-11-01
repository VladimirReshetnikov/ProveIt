import DiophantineConsistency.AdaptiveDirectOrdinate86Units
import DiophantineConsistency.ArithmeticSignedPairExpressions
/-! A degree-oriented alternative to the 86-operation polynomial.

Its four terms square the deviations of the actual literal factors from one.
The zero equivalence is proved in every model of IΣ₁, with the same valuation;
no claim about the operation count or iPRA proof transfer is made here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinateSquareSums
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticSignedPairExpressions AdaptiveDirectOrdinate86Units AdaptiveDirectOrdinate86Factors
open AdaptiveDirectOrdinate86Literal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def deviation {σ : Type*} (e : Expr σ) : Expr σ := e-1

def square {σ : Type*} (e : Expr σ) : Expr σ := deviation e * deviation e

def squareSum (p : Fin 4 → ℤ) : Expr (Fin 13) :=
 let f := factors86 p
 square f.1 + square f.2.1 + square f.2.2.1 + square f.2.2.2

def diffPair {σ : Type*} (e : Expr σ) (v : σ → V) : Pair V :=
 minus (pairEval e v) (natural (1:V))

theorem square_rep {σ : Type*} (e : Expr σ) (v : σ → V) :
    SignedRep (square e) v (natural (magnitude (diffPair e v) * magnitude (diffPair e v))) := by
  have hd : SignedRep (deviation e) v (diffPair e v) := by
    exact rep_sub (equivalent_refl (pairEval e v)) (rep_one v)
  exact equivalent_trans (rep_mul hd hd) (square_magnitude (diffPair e v))

theorem magnitude_zero_iff {p : Pair V} : magnitude p = 0 ↔ p.1 = p.2 := by
  constructor
  · intro h
    change (p.1-p.2)+(p.2-p.1)=0 at h
    have h1 : p.1-p.2=0 := le_antisymm (calc
      p.1-p.2 ≤ (p.1-p.2)+(p.2-p.1) := by simp
      _ = 0 := h) (Arithmetic.zero_le _)
    have h2 : p.2-p.1=0 := le_antisymm (calc
      p.2-p.1 ≤ (p.1-p.2)+(p.2-p.1) := by simp
      _ = 0 := h) (Arithmetic.zero_le _)
    exact le_antisymm (tsub_eq_zero_iff_le.mp h1) (tsub_eq_zero_iff_le.mp h2)
  · intro h
    simp [magnitude,h]

theorem diff_magnitude_zero_iff {σ : Type*} (e : Expr σ) (v : σ → V) :
    magnitude (diffPair e v) = 0 ↔ (pairEval e v).1 = (pairEval e v).2+1 := by
  rw [magnitude_zero_iff]
  simp [diffPair,minus,natural]

theorem rep_zero_iff {σ : Type*} {e : Expr σ} {v : σ → V} {n : V}
    (h : SignedRep e v (natural n)) : InternalZero e v ↔ n=0 := by
  change (pairEval e v).1 = (pairEval e v).2 ↔ n=0
  change (pairEval e v).1+0 = (pairEval e v).2+n at h
  simp only [add_zero] at h
  constructor
  · intro he
    rw [he] at h
    apply add_left_cancel (a:=(pairEval e v).2)
    simpa only [add_zero] using h.symm
  · intro hn
    simpa only [hn,add_zero] using h

theorem squareSum_rep (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    SignedRep (squareSum p) v
      (natural (magnitude (diffPair (factors86 p).1 v)*magnitude (diffPair (factors86 p).1 v) +
                magnitude (diffPair (factors86 p).2.1 v)*magnitude (diffPair (factors86 p).2.1 v) +
                magnitude (diffPair (factors86 p).2.2.1 v)*magnitude (diffPair (factors86 p).2.2.1 v) +
                magnitude (diffPair (factors86 p).2.2.2 v)*magnitude (diffPair (factors86 p).2.2.2 v))) := by
  exact rep_add_nat (rep_add_nat (rep_add_nat (square_rep _ v) (square_rep _ v)) (square_rep _ v)) (square_rep _ v)

theorem sum_eq_zero_iff (a b : V) : a+b=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro h
    constructor
    · exact le_antisymm (calc
        a ≤ a+b := by simp
        _ = 0 := h) (Arithmetic.zero_le _)
    · exact le_antisymm (calc
        b ≤ a+b := by simp
        _ = 0 := h) (Arithmetic.zero_le _)
  · rintro ⟨rfl,rfl⟩
    simp

theorem squareSum_zero_iff_units (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (squareSum p) v ↔
    (pairEval (factors86 p).1 v).1=(pairEval (factors86 p).1 v).2+1 ∧
    (pairEval (factors86 p).2.1 v).1=(pairEval (factors86 p).2.1 v).2+1 ∧
    (pairEval (factors86 p).2.2.1 v).1=(pairEval (factors86 p).2.2.1 v).2+1 ∧
    (pairEval (factors86 p).2.2.2 v).1=(pairEval (factors86 p).2.2.2 v).2+1 := by
  rw [rep_zero_iff (squareSum_rep p v)]
  simp only [sum_eq_zero_iff, mul_self_eq_zero, diff_magnitude_zero_iff, and_assoc]

theorem internalZero_sub_one_iff {σ : Type*} (e : Expr σ) (v : σ → V) :
    InternalZero (e-1) v ↔ Equivalent (pairEval e v) (natural (1:V)) := by
  change (Expr.sub e (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub e (Expr.constant 1)).splitNatural.2.evalSemiring v ↔ _
  simp [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]

theorem units_imply_original_zero (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (h : (pairEval (factors86 p).1 v).1=(pairEval (factors86 p).1 v).2+1 ∧
    (pairEval (factors86 p).2.1 v).1=(pairEval (factors86 p).2.1 v).2+1 ∧
    (pairEval (factors86 p).2.2.1 v).1=(pairEval (factors86 p).2.2.1 v).2+1 ∧
    (pairEval (factors86 p).2.2.2 v).1=(pairEval (factors86 p).2.2.2 v).2+1) :
    InternalZero (expressionAt86 p) v := by
  obtain ⟨ha,hb,hc,hd⟩ := h
  have h := equivalent_multiply (equivalent_one.mpr hd) (equivalent_multiply
    (equivalent_one.mpr hc) (equivalent_multiply (equivalent_one.mpr ha) (equivalent_one.mpr hb)))
  simp only [one_multiply] at h
  rw [literal_factors, internalZero_sub_one_iff]
  exact h

theorem squareSum_iff_original (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (squareSum p) v ↔ InternalZero (expressionAt86 p) v := by
  rw [squareSum_zero_iff_units]
  exact ⟨units_imply_original_zero p v, expressionAt_factor_units86 p v⟩


/-- Extract the three residuals from factors built as `1 + residual`. -/
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  match (factors86 p).1 with
  | .add _ a => a
  | _ => 0

def mainResidual (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  match (factors86 p).2.1 with
  | .add _ a => a
  | _ => 0

def strongResidual (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  match (factors86 p).2.2.2 with
  | .add _ a => a
  | _ => 0

def optimized (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let a := firstResidual p
  let b := mainResidual p
  let c := (factors86 p).2.2.1 - 1
  let d := strongResidual p
  a*a + b*b + c*c + d*d

theorem deviation_one_plus {σ : Type*} (e : Expr σ) (v : σ → V) :
    SignedRep (deviation (1+e)) v (pairEval e v) := by
  change Equivalent (pairEval (Expr.sub (Expr.add (Expr.constant 1) e) (Expr.constant 1)) v) (pairEval e v)
  simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent]
  ring

theorem square_one_plus {σ : Type*} (e : Expr σ) (v : σ → V) :
    Equivalent (pairEval (square (1+e)) v) (pairEval (e*e) v) := by
  exact rep_mul (deviation_one_plus e v) (deviation_one_plus e v)

theorem optimized_pair_equiv (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    Equivalent (pairEval (squareSum p) v) (pairEval (optimized p) v) := by
  have h0 : (factors86 p).1 = 1 + firstResidual p := rfl
  have h1 : (factors86 p).2.1 = 1 + mainResidual p := rfl
  have h3 : (factors86 p).2.2.2 = 1 + strongResidual p := rfl
  change Equivalent (plus (plus (plus (pairEval (square (factors86 p).1) v)
    (pairEval (square (factors86 p).2.1) v))
    (pairEval (square (factors86 p).2.2.1) v))
    (pairEval (square (factors86 p).2.2.2) v))
    (plus (plus (plus (pairEval (firstResidual p * firstResidual p) v)
      (pairEval (mainResidual p * mainResidual p) v))
      (pairEval (((factors86 p).2.2.1-1) * ((factors86 p).2.2.1-1)) v))
      (pairEval (strongResidual p * strongResidual p) v))
  rw [h0,h1,h3]
  exact plus_equiv (plus_equiv (plus_equiv (square_one_plus _ v) (square_one_plus _ v))
    (equivalent_refl _)) (square_one_plus _ v)

theorem internalZero_iff_pair_zero {σ : Type*} (e : Expr σ) (v : σ → V) :
    InternalZero e v ↔ Equivalent (pairEval e v) (natural (0:V)) := by
  simp [InternalZero,pairEval,Equivalent,natural]

theorem optimized_zero_iff_original (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (optimized p) v ↔ InternalZero (expressionAt86 p) v := by
  have h := optimized_pair_equiv p v
  have hz : InternalZero (optimized p) v ↔ InternalZero (squareSum p) v := by
    rw [internalZero_iff_pair_zero, internalZero_iff_pair_zero]
    exact ⟨fun hq => equivalent_trans h hq,
      fun hp => equivalent_trans (equivalent_symm h) hp⟩
  exact hz.trans (squareSum_iff_original p v)

/-- Shift positive coordinates in both candidates using exactly the same valuation. -/
theorem shifted_zero_iff_original (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (positiveShift (squareSum p)) v ↔
      InternalZero (positiveShift (expressionAt86 p)) v := by
  rw [internalZero_positiveShift, internalZero_positiveShift]
  exact squareSum_iff_original p (fun i => v i + 1)

/-- The three canceled residuals preserve the zero set after positive shift. -/
theorem shifted_optimized_zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (positiveShift (optimized p)) v ↔
      InternalZero (positiveShift (expressionAt86 p)) v := by
  rw [internalZero_positiveShift, internalZero_positiveShift]
  exact optimized_zero_iff_original p (fun i => v i + 1)

def expression : Expr (Fin 13) := optimized CurrentWindowCarry2011.ports

def naturalExpression : Expr (Fin 13) := positiveShift expression

/-- This is a pointwise, not merely existential, fixed-port equivalence. -/
theorem current_zero_iff (v : Fin 13 → V) :
    InternalZero naturalExpression v ↔ InternalZero naturalExpression86 v :=
  shifted_optimized_zero_iff CurrentWindowCarry2011.ports v

theorem current_no_zero_iff :
    (∀ v : Fin 13 → V, ¬InternalZero naturalExpression v) ↔
      (∀ v : Fin 13 → V, ¬InternalZero naturalExpression86 v) := by
  constructor <;> intro h v hv
  · exact h v ((current_zero_iff v).mpr hv)
  · exact h v ((current_zero_iff v).mp hv)

end DiophantineConsistency.AdaptiveDirectOrdinateSquareSums
