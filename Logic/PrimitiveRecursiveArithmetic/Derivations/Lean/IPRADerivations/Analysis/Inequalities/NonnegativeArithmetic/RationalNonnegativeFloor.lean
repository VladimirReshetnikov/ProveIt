import IPRADerivations.Analysis.Optimization.Convexity.Secants.RationalConvexSecants
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals
import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName

/-!
# Exact numerical floor cuts for original nonnegative rational codes

The original signed numerator is converted to its genuine natural value
under a proved nonnegative source. Original numerical quotient/remainder
then supplies monotone integer cuts, their source interval bound, and
the exact 1/M scalar error of the rational grid point. All denominators
remain independent and every index is an internal numerical term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalNonnegativeFloor

open_ipra
open RationalConvexSecants (nonnegative naturalNumerator nonnegative_representation)
open RationalSupMetric (denominatorOf)
open RationalArgmin (rationalLE denominator_positive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRationalMetric (comparison_to_cleared comparison_of_cleared)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def index (q M : PTm n) : PTm n := quo (M*naturalNumerator q) (denominatorOf q)
def quantized (q M : PTm n) : PTm n := fraction (index q M) M

ipra_subst index [naturalNumerator, RationalSupMetric.numeratorOf, quo]
ipra_subst quantized

theorem original_division (q M : PTm n) : Γ ⊢[PRAAx]
    (M*naturalNumerator q ≐ denominatorOf q*index q M+rem (M*naturalNumerator q) (denominatorOf q)) ⋏
      lt (rem (M*naturalNumerator q) (denominatorOf q)) (denominatorOf q) :=
  div_mod_at ((eq_add_of_le (denominator_positive q)).eqTrans (by ipra_ring))

theorem integer_lower (q M : PTm n) : Γ ⊢[PRAAx] le (denominatorOf q*index q M) (M*naturalNumerator q) :=
  le_congr (.eqRefl _) (original_division q M).andE₁.eqSymm (le_add_right _ _)

/-- The same original quotient program is monotone under rational
order, even when the two raw denominators are different. -/
theorem index_monotone (q r M : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q)
    (hr : Γ ⊢[PRAAx] nonnegative r) (h : Γ ⊢[PRAAx] rationalLE q r) : Γ ⊢[PRAAx] le (index q M) (index r M) := by
  let U := naturalNumerator q
  let V := naturalNumerator r
  let D := denominatorOf q
  let E := denominatorOf r
  have clear : Γ ⊢[PRAAx] le (E*U) (V*D) :=
    comparison_to_cleared _ _ _ _ _ _ (nonnegative_representation q hq) (nonnegative_representation r hr) h
  have decompQ : Γ ⊢[PRAAx] M*U ≐ D*index q M+rem (M*U) D := (original_division q M).andE₁
  have decompR : Γ ⊢[PRAAx] M*V ≐ E*index r M+rem (M*V) E := (original_division r M).andE₁
  refine .orE (lt_or_le (index r M) (index q M)) ?_ Prf.hyp0
  let Δ := lt (index r M) (index q M)::Γ
  have less : Δ ⊢[PRAAx] lt (index r M) (index q M) := Prf.hyp0
  have impossible : Δ ⊢[PRAAx] le (D*E) (D*rem (M*V) E) := by
    apply le_of_eq_add (d := M*monus (V*D) (E*U)+D*E*monus (index q M) (succ (index r M))+E*rem (M*U) D)
    ipra_lc 𝔞 M*natEq (Γ := Δ) (eq_add_of_le clear.wk)+𝔞 D*𝔞 E*natEq (eq_add_of_le less)+
      𝔞 E*natEq (Γ := Δ) decompQ.wk-𝔞 D*natEq (Γ := Δ) decompR.wk
  exact le_lt_absurd _ (RationalValueBounds.positive_cancel (denominator_positive (Γ := Δ) q) impossible)
    (original_division (Γ := Δ) r M).andE₂

theorem index_bound (q M K : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q)
    (h : Γ ⊢[PRAAx] rationalLE q (natCode K)) : Γ ⊢[PRAAx] le (index q M) (M*K) := by
  have clear : Γ ⊢[PRAAx] le (naturalNumerator q) (K*denominatorOf q) :=
    le_congr (one_mul _) (.eqRefl _) (comparison_to_cleared _ _ _ _ _ _
      (nonnegative_representation q hq) (natCode_represents K) h)
  have multiplied : Γ ⊢[PRAAx] le (M*naturalNumerator q) (denominatorOf q*(M*K)) :=
    le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right M clear)
  exact RationalValueBounds.positive_cancel (denominator_positive q) (le_trans (integer_lower q M) multiplied)

theorem quantized_below (q M : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    rationalLE (quantized q M) q :=
  comparison_of_cleared _ _ _ _ _ _ hM (denominator_positive q) (fraction_represents _ _ hM)
    (nonnegative_representation q hq) (le_congr (.eqRefl _) (mul_comm _ _) (integer_lower q M))

theorem quantized_upper_error (q M : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    upper q (quantized q M) one M := by
  let U := naturalNumerator q
  let D := denominatorOf q
  let R := rem (M*U) D
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ (denominator_positive q) hM
    (nonnegative_representation q hq) (fraction_represents _ _ hM)
  apply zle_of_toZ (M*monus D R)
  have eq := natEq (original_division (Γ := Γ) q M).andE₁
  have small := natEq (eq_add_of_le (le_of_lt (original_division (Γ := Γ) q M).andE₂))
  simp only [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
  dsimp only [U,D,R] at eq small ⊢
  ipra_simps
  linear_combination 𝔞 M*eq-𝔞 M*small

/-- An actual original rational grid point with absolute scalar error
at most 1/M; no source canonicality or common denominator is required. -/
theorem quantization_error (q M : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    radius q (quantized q M) one M :=
  RationalValueBounds.radius_of_upper _ _ _ _ (quantized_upper_error q M hq hM)
    (RationalValueBounds.upper_of_order _ _ _ _ (quantized_below q M hq hM))

def indexF : PR 2 := PTm.toPR (index (var 0) (var 1))
theorem program_at (q M : PTm n) : Γ ⊢[PRAAx] ap2 indexF q M ≐ index q M := by
  simpa [indexF,ap2] using toPR_eq (Γ := Γ) (index (var 0) (var 1) : PTm 2) ![q,M]

theorem actual_original_nonnegative_floor_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((nonnegative (var 0) ⋏ (nonnegative (var 1) ⋏ rationalLE (var 0) (var 1))) ⟶ le (index (var 0) (var 2)) (index (var 1) (var 2))) :=
  closeUniv 3 (.impI (index_monotone _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_original_nonnegative_floor_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((nonnegative (var 0) ⋏ rationalLE (var 0) (natCode (var 2))) ⟶ le (index (var 0) (var 1)) (var 1*var 2)) :=
  closeUniv 3 (.impI (index_bound _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_nonnegative_quantization_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((nonnegative (var 0) ⋏ le one (var 1)) ⟶ radius (var 0) (quantized (var 0) (var 1)) one (var 1)) :=
  closeUniv 2 (.impI (quantization_error _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_nonnegative_floor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 indexF (var 0) (var 1) ≐ index (var 0) (var 1)) := closeUniv 2 (program_at _ _)

end LeanProofs.IPRA.Analysis.RationalNonnegativeFloor
