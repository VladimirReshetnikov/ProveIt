import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.Continuity.GaussianGammaFiniteValueProperness

/-!
# Literal actual compact-grid split at a shared rational step

Widths C1,C2 use actual counts C1*K,C2*K,(C1+C2)*K. The original
normalized weights are proved equal and the original rational grid
values match before/after the split. The finite sum splits LITERALLY
into its old prefix/offB suffix. Differently encoded evaluator calls
are not identified here; the subsequent metric theorem uses their
proved zero-distance rate instead.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactRiemannSplit

open_ipra
open GaussianRationalHorner (ofGaussian qadd qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCompactRiemannName (grid value inside sampleBody sampleData quadrature fraction_congr value_grid)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalFiniteSum (sum sum_index_congr)
open ComplexLogarithmRemainder (scale oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem inside_left (a C1 C2 E t : PTm n) (h : Γ ⊢[PRAAx] inside a C1 E t) : Γ ⊢[PRAAx] inside a (C1+C2) E t :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
    (le_trans h.andE₂.andE₂.andE₂ (le_of_eq_add (d := C2*sndT t) (by ipra_ring)))))

theorem inside_right (a C1 C2 E t : PTm n) (h : Γ ⊢[PRAAx] inside (a+C1) C2 E t) : Γ ⊢[PRAAx] inside a (C1+C2) E t :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI
    (le_trans (le_of_eq_add (d := C1*sndT t) (by ipra_ring)) h.andE₂.andE₂.andE₁)
    (le_congr (.eqRefl _) (by ipra_ring) h.andE₂.andE₂.andE₂)))

theorem native_scale (C A : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
    (scale (C*A) oneCode) (scale C (scale A oneCode)) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals try ipra_simps
  all_goals ring

/-- Positive scaling cancels only after the original canonical fraction
constructors and their genuine native value equality are exposed. -/
theorem fraction_cancel (C A D : PTm n) (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    ofGaussian (scale (C*A) oneCode) (C*D) ≐ ofGaussian (scale A oneCode) D :=
  (GaussianGammaFiniteValueProperness.fraction_equal _ _ _ (positive_product _ _ hC hD) (native_scale C A)).eqTrans
    (GaussianGammaEncodingRescaling.fraction_rescale (scale A oneCode) D C hD hC)

def sharedValue (i K a E : PTm n) : PTm n := ofGaussian (scale (a*K+i) oneCode) (E*K)
ipra_subst sharedValue

theorem grid_shared_value (i K a C E : PTm n) (hC : Γ ⊢[PRAAx] le one C)
    (hE : Γ ⊢[PRAAx] le one E) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    value (grid i (C*K) a C E) ≐ sharedValue i K a E :=
  (value_grid i (C*K) a C E).eqTrans
    ((fraction_congr _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] a*(C*K)+C*i ≐ C*(a*K+i))
      (by ipra_ring : Γ ⊢[PRAAx] E*(C*K) ≐ C*(E*K))).eqTrans
      (fraction_cancel C (a*K+i) (E*K) hC (positive_product _ _ hE hK)))

theorem weight_shared (C E K : PTm n) (hC : Γ ⊢[PRAAx] le one C)
    (hE : Γ ⊢[PRAAx] le one E) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    weight C E (C*K) ≐ weight one E K :=
  (fraction_congr _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] C ≐ C*one)
    (by ipra_ring : Γ ⊢[PRAAx] E*(C*K) ≐ C*(E*K))).eqTrans
    (fraction_cancel C one (E*K) hC (positive_product _ _ hE hK))

theorem sum_width_positive (C1 C2 : PTm n) (hC1 : Γ ⊢[PRAAx] le one C1) : Γ ⊢[PRAAx] le one (C1+C2) :=
  le_trans hC1 (le_add_right _ _)

theorem prefix_grid_value (i K a C1 C2 E : PTm n) (hC1 : Γ ⊢[PRAAx] le one C1)
    (hE : Γ ⊢[PRAAx] le one E) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    value (grid i ((C1+C2)*K) a (C1+C2) E) ≐ value (grid i (C1*K) a C1 E) :=
  (grid_shared_value i K a (C1+C2) E (sum_width_positive C1 C2 hC1) hE hK).eqTrans
    (grid_shared_value i K a C1 E hC1 hE hK).eqSymm

theorem suffix_grid_value (i K a C1 C2 E : PTm n) (hC1 : Γ ⊢[PRAAx] le one C1) (hC2 : Γ ⊢[PRAAx] le one C2)
    (hE : Γ ⊢[PRAAx] le one E) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    value (grid (C1*K+i) ((C1+C2)*K) a (C1+C2) E) ≐ value (grid i (C2*K) (a+C1) C2 E) :=
  (grid_shared_value (C1*K+i) K a (C1+C2) E (sum_width_positive C1 C2 hC1) hE hK).eqTrans
    ((fraction_congr _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] a*K+(C1*K+i) ≐ (a+C1)*K+i) (.eqRefl _)).eqTrans
      (grid_shared_value i K (a+C1) C2 E hC2 hE hK).eqSymm)

def fullData (s K a C1 C2 E x : PTm n) : PTm n := sampleData s ((C1+C2)*K) a (C1+C2) E x
def prefixPart (F : PR 3) (s K a C1 C2 E x : PTm n) : PTm n := qmul (weight one E K)
  (sum (sampleBody F) (C1*K) (fullData s K a C1 C2 E x))
def suffixPart (F : PR 3) (s K a C1 C2 E x : PTm n) : PTm n := qmul (weight one E K)
  (sum (offB (sampleBody F)) (C2*K) (pairT (C1*K) (fullData s K a C1 C2 E x)))
ipra_subst fullData
ipra_subst prefixPart
ipra_subst suffixPart

/-- A literal identity of the SAME actual full-grid sum, keeping its
original data in both generated prefix and offset suffix. -/
theorem literal_split (F : PR 3) (s K a C1 C2 E x : PTm n) (hC1 : Γ ⊢[PRAAx] le one C1)
    (hE : Γ ⊢[PRAAx] le one E) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    quadrature F s ((C1+C2)*K) a (C1+C2) E x ≐ qadd (prefixPart F s K a C1 C2 E x) (suffixPart F s K a C1 C2 E x) := by
  have old := (sum_index_congr (sampleBody F) (by ipra_ring : Γ ⊢[PRAAx] (C1+C2)*K ≐ C1*K+C2*K)
    (.eqRefl (fullData s K a C1 C2 E x))).eqTrans
      (GaussianRationalMatrixFiniteSums.sum_split (sampleBody F) (C1*K) (C2*K) (fullData s K a C1 C2 E x))
  exact (qmul_congr (weight_shared (C1+C2) E K (sum_width_positive C1 C2 hC1) hE hK) old).eqTrans
    (GaussianRationalCoefficientScaling.qmul_add _ _ _)


def input (C1 C2 E K : PTm n) : Fm PTm n := le one C1 ⋏ (le one C2 ⋏ (le one E ⋏ le one K))
def output (F : PR 3) (s K a C1 C2 E x : PTm n) : PTm n := pairT (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
  (pairT (prefixPart F s K a C1 C2 E x) (pairT (suffixPart F s K a C1 C2 E x) (weight one E K)))
def outputF (F : PR 3) : PR 7 := PTm.toPR (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (F : PR 3) (s K a C1 C2 E x : PTm n) : PTm n := PTm.app (outputF F) ![s,K,a,C1,C2,E,x]
ipra_subst output
theorem program_at (F : PR 3) (s K a C1 C2 E x : PTm n) : Γ ⊢[PRAAx]
    run F s K a C1 C2 E x ≐ output F s K a C1 C2 E x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![s,K,a,C1,C2,E,x]
theorem returned_full (F : PR 3) (s K a C1 C2 E x : PTm n) : Γ ⊢[PRAAx]
    fstT (run F s K a C1 C2 E x) ≐ quadrature F s ((C1+C2)*K) a (C1+C2) E x :=
  (program_at F s K a C1 C2 E x).fstE
theorem returned_tail (F : PR 3) (s K a C1 C2 E x : PTm n) : Γ ⊢[PRAAx]
    sndT (run F s K a C1 C2 E x) ≐ pairT (prefixPart F s K a C1 C2 E x) (pairT (suffixPart F s K a C1 C2 E x) (weight one E K)) :=
  (program_at F s K a C1 C2 E x).sndE
theorem returned_prefix (F : PR 3) (s K a C1 C2 E x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F s K a C1 C2 E x)) ≐ prefixPart F s K a C1 C2 E x :=
  (returned_tail F s K a C1 C2 E x).fstE
theorem returned_suffix_weight (F : PR 3) (s K a C1 C2 E x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F s K a C1 C2 E x)) ≐ pairT (suffixPart F s K a C1 C2 E x) (weight one E K) :=
  (returned_tail F s K a C1 C2 E x).sndE
theorem returned_suffix (F : PR 3) (s K a C1 C2 E x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F s K a C1 C2 E x))) ≐ suffixPart F s K a C1 C2 E x :=
  (returned_suffix_weight F s K a C1 C2 E x).fstE
theorem returned_weight (F : PR 3) (s K a C1 C2 E x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run F s K a C1 C2 E x))) ≐ weight one E K :=
  (returned_suffix_weight F s K a C1 C2 E x).sndE

theorem actual_common_step_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶ weight (var 0) (var 1) (var 0*var 2) ≐ weight one (var 1) (var 2)) :=
  closeUniv 3 (.impI (weight_shared _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_common_step_prefix_grid_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 3) (var 4) (var 5) (var 1) ⟶ value (grid (var 0) ((var 3+var 4)*var 1) (var 2) (var 3+var 4) (var 5)) ≐
      value (grid (var 0) (var 3*var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (prefix_grid_value _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_common_step_suffix_grid_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 3) (var 4) (var 5) (var 1) ⟶ value (grid (var 3*var 1+var 0) ((var 3+var 4)*var 1) (var 2) (var 3+var 4) (var 5)) ≐
      value (grid (var 0) (var 4*var 1) (var 2+var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (suffix_grid_value _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_literal_common_step_quadrature_split_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 3) (var 4) (var 5) (var 1) ⟶ quadrature F (var 0) ((var 3+var 4)*var 1) (var 2) (var 3+var 4) (var 5) (var 6) ≐
      qadd (prefixPart F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (suffixPart F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (literal_split F _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_literal_grid_split_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at F _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCompactRiemannSplit
