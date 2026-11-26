import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannSplit

/-!
# Actual shared-step compact quadrature additivity

A true original local sampled-modulus theorem at distance zero compares
the differently encoded full and piece grid points. The SAME original
sum split and positive common weight give the quantitative finite law.
No equality of evaluator observations or quadrature output is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactRiemannAdditivity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid value inside sampleBody sampleData sample_body_at quadrature sampledModulus)
open GaussianCompactRiemannSplit (fullData prefixPart suffixPart weight_shared sum_width_positive)
open GaussianRationalRiemannRefinement (weight termsDistance sum_distance)
open GaussianRationalFiniteSum (sum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (F : PR 3) (a C1 C2 E K L x : PTm n) : Fm PTm n := le one a ⋏ (le one E ⋏ (le one K ⋏
  (le one C1 ⋏ (le one C2 ⋏ sampledModulus F a (C1+C2) E L x))))
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (a C1 C2 E K L x : PTm n) :
    (input F a C1 C2 E K L x).subst σ = input F (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2)
      (Syn.subst σ E) (Syn.subst σ K) (Syn.subst σ L) (Syn.subst σ x) := by simp [input]

theorem inside_left (a C1 C2 E t : PTm n) (h : Γ ⊢[PRAAx] inside a C1 E t) : Γ ⊢[PRAAx] inside a (C1+C2) E t :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
    (le_trans h.andE₂.andE₂.andE₂ (le_of_eq_add (d := C2*sndT t) (by ipra_ring)))))

theorem inside_right (a C1 C2 E t : PTm n) (h : Γ ⊢[PRAAx] inside (a+C1) C2 E t) : Γ ⊢[PRAAx] inside a (C1+C2) E t :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI
    (le_trans (le_of_eq_add (d := C1*sndT t) (by ipra_ring)) h.andE₂.andE₂.andE₁)
    (le_congr (.eqRefl _) (by ipra_ring) h.andE₂.andE₂.andE₂)))

/-- The genuine zero-distance rate retains two actual observation errors. -/
theorem equal_value_samples (F : PR 3) (s a C E L x t u : PTm n)
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (he : Γ ⊢[PRAAx] value t ≐ value u) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F s t x) (ap3 F s u x) two (unit s) := by
  have metric := distance_congr he.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero (value u) one (le_refl one))
  have raw := GaussianCompactRiemannName.sampled_modulus_at F a C E L x s s t u zero one h (le_refl one) ht hu metric
  exact distance_radius_mono _ _ _ _ two (unit s)
    (GaussianNamedInverseRate.denominator_positive one s s (le_refl one)) (unit_positive s)
    (le_of_eq_add (d := zero) (by unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator; ipra_ring)) raw

theorem prefix_term_distance (F : PR 3) (i s a C1 C2 E K L x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x)
    (hi : Γ ⊢[PRAAx] lt i (C1*K)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody F) i (fullData s K a C1 C2 E x))
      (inst2 (sampleBody F) i (sampleData s (C1*K) a C1 E x)) two (unit s) := by
  have ha := h.andE₁
  have e := h.andE₂.andE₁
  have k := h.andE₂.andE₂.andE₁
  have c1 := h.andE₂.andE₂.andE₂.andE₁
  have c2 := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have m := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have bound : Γ ⊢[PRAAx] le i ((C1+C2)*K) := le_trans (le_of_lt hi) (mul_le_mul_right K (le_add_right C1 C2))
  have full := GaussianCompactRiemannName.grid_inside i ((C1+C2)*K) a (C1+C2) E ha e
    (positive_product _ _ (sum_width_positive C1 C2 c1) k) bound
  have part := inside_left a C1 C2 E _ (GaussianCompactRiemannName.grid_inside i (C1*K) a C1 E ha e
    (positive_product _ _ c1 k) (le_of_lt hi))
  have old := equal_value_samples F s a (C1+C2) E L x _ _ m full part (GaussianCompactRiemannSplit.prefix_grid_value i K a C1 C2 E c1 e k)
  exact distance_congr (sample_body_at F i s ((C1+C2)*K) a (C1+C2) E x).eqSymm
    (sample_body_at F i s (C1*K) a C1 E x).eqSymm (.eqRefl _) (.eqRefl _) old

theorem suffix_term_distance (F : PR 3) (i s a C1 C2 E K L x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x)
    (hi : Γ ⊢[PRAAx] lt i (C2*K)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (offB (sampleBody F)) i (pairT (C1*K) (fullData s K a C1 C2 E x)))
      (inst2 (sampleBody F) i (sampleData s (C2*K) (a+C1) C2 E x)) two (unit s) := by
  have ha := h.andE₁
  have e := h.andE₂.andE₁
  have k := h.andE₂.andE₂.andE₁
  have c1 := h.andE₂.andE₂.andE₂.andE₁
  have c2 := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have m := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have bound : Γ ⊢[PRAAx] le (C1*K+i) ((C1+C2)*K) :=
    le_congr (add_comm _ _) (by ipra_ring) (add_le_add_right (C1*K) (le_of_lt hi))
  have full := GaussianCompactRiemannName.grid_inside (C1*K+i) ((C1+C2)*K) a (C1+C2) E ha e
    (positive_product _ _ (sum_width_positive C1 C2 c1) k) bound
  have part := inside_right a C1 C2 E _ (GaussianCompactRiemannName.grid_inside i (C2*K) (a+C1) C2 E
    (le_trans ha (le_add_right _ _)) e (positive_product _ _ c2 k) (le_of_lt hi))
  have old := equal_value_samples F s a (C1+C2) E L x _ _ m full part (GaussianCompactRiemannSplit.suffix_grid_value i K a C1 C2 E c1 c2 e k)
  have off := (GaussianRationalFiniteProduct.offset_at (Γ := Γ) (sampleBody F) (C1*K) i (fullData s K a C1 C2 E x)).eqTrans
    (sample_body_at F (C1*K+i) s ((C1+C2)*K) a (C1+C2) E x)
  exact distance_congr off.eqSymm (sample_body_at F i s (C2*K) (a+C1) C2 E x).eqSymm (.eqRefl _) (.eqRefl _) old

/-- The common weight 1/(EK) genuinely cancels the numerical K in the
old sum's bound, using positive denominator comparison. -/
theorem weighted_sum_distance (f g : PTm 2) (C E K x y A D : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hK : Γ ⊢[PRAAx] le one K) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] termsDistance f g (C*K) x y A D) : Γ ⊢[PRAAx]
    distanceBounded (qmul (weight one E K) (sum f (C*K) x)) (qmul (weight one E K) (sum g (C*K) y)) (C*A) (E*D) := by
  have ek := positive_product _ _ hE hK
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ ek hD
    (GaussianRationalRiemannRefinement.weight_bound one E K hE hK) (sum_distance f g (C*K) x y A D hD h)
  have old := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight one E K) _ _).eqSymm (one_mul _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ (C*A) (E*D) (positive_product _ _ ek hD) (positive_product _ _ hE hD)
    (le_of_eq_add (d := zero) (by ipra_ring)) old

theorem prefix_distance (F : PR 3) (s a C1 C2 E K L x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x) : Γ ⊢[PRAAx]
    distanceBounded (prefixPart F s K a C1 C2 E x) (quadrature F s (C1*K) a C1 E x) (C1*two) (E*unit s) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift L) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] termsDistance (sampleBody F) (sampleBody F) (C1*K) (fullData s K a C1 C2 E x)
      (sampleData s (C1*K) a C1 E x) two (unit s) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianCompactRiemannSplit.subst_fullData,GaussianCompactRiemannName.subst_sampleData,PTm.subst_mul,
      GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using prefix_term_distance F (var 0)
        (Syn.shift s) (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift L) (Syn.shift x) hs.wk Prf.hyp0
  have raw := weighted_sum_distance _ _ C1 E K _ _ two (unit s) h.andE₂.andE₁ h.andE₂.andE₂.andE₁ (unit_positive s) terms
  exact distance_congr (.eqRefl _) (qmul_congr (weight_shared C1 E K h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) raw

theorem suffix_distance (F : PR 3) (s a C1 C2 E K L x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x) : Γ ⊢[PRAAx]
    distanceBounded (suffixPart F s K a C1 C2 E x) (quadrature F s (C2*K) (a+C1) C2 E x) (C2*two) (E*unit s) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift L) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] termsDistance (offB (sampleBody F)) (sampleBody F) (C2*K) (pairT (C1*K) (fullData s K a C1 C2 E x))
      (sampleData s (C2*K) (a+C1) C2 E x) two (unit s) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianCompactRiemannSplit.subst_fullData,GaussianCompactRiemannName.subst_sampleData,subst_pairT,PTm.subst_mul,PTm.subst_add,
      GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using suffix_term_distance F (var 0)
        (Syn.shift s) (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift L) (Syn.shift x) hs.wk Prf.hyp0
  have raw := weighted_sum_distance _ _ C2 E K _ _ two (unit s) h.andE₂.andE₁ h.andE₂.andE₂.andE₁ (unit_positive s) terms
  exact distance_congr (.eqRefl _) (qmul_congr (weight_shared C2 E K h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) raw

/-- Quantitative shared-step additivity of the actual stored compact
quadratures, with only genuine original local sampled modulus as input. -/
theorem shared_step_additivity (F : PR 3) (s a C1 C2 E K L x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
      (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x)) (two*(C1+C2)) (E*unit s) := by
  have both := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ (positive_product _ _ h.andE₂.andE₁ (unit_positive s))
    (prefix_distance F s a C1 C2 E K L x h) (suffix_distance F s a C1 C2 E K L x h)
  exact distance_congr (GaussianCompactRiemannSplit.literal_split F s K a C1 C2 E x h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁).eqSymm
    (.eqRefl _) (by ipra_ring) (.eqRefl _) both


def output (F : PR 3) (s a C1 C2 E K x : PTm n) : PTm n := pairT (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
  (pairT (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x)) (pairT (two*(C1+C2)) (E*unit s)))
def outputF (F : PR 3) : PR 7 := PTm.toPR (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (F : PR 3) (s a C1 C2 E K x : PTm n) : PTm n := PTm.app (outputF F) ![s,a,C1,C2,E,K,x]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (s a C1 C2 E K x : PTm n) :
    Syn.subst σ (output F s a C1 C2 E K x) = output F (Syn.subst σ s) (Syn.subst σ a) (Syn.subst σ C1)
      (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ K) (Syn.subst σ x) := by simp [output]
theorem program_at (F : PR 3) (s a C1 C2 E K x : PTm n) : Γ ⊢[PRAAx] run F s a C1 C2 E K x ≐ output F s a C1 C2 E K x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![s,a,C1,C2,E,K,x]
theorem returned_full (F : PR 3) (s a C1 C2 E K x : PTm n) : Γ ⊢[PRAAx]
    fstT (run F s a C1 C2 E K x) ≐ quadrature F s ((C1+C2)*K) a (C1+C2) E x :=
  (congrFst (program_at F s a C1 C2 E K x)).eqTrans (fst_pair _ _)
theorem returned_tail (F : PR 3) (s a C1 C2 E K x : PTm n) : Γ ⊢[PRAAx]
    sndT (run F s a C1 C2 E K x) ≐ pairT (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x))
      (pairT (two*(C1+C2)) (E*unit s)) := (congrSnd (program_at F s a C1 C2 E K x)).eqTrans (snd_pair _ _)
theorem returned_pieces (F : PR 3) (s a C1 C2 E K x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F s a C1 C2 E K x)) ≐ qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x) :=
  (congrFst (returned_tail F s a C1 C2 E K x)).eqTrans (fst_pair _ _)
theorem returned_budget (F : PR 3) (s a C1 C2 E K x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F s a C1 C2 E K x)) ≐ pairT (two*(C1+C2)) (E*unit s) :=
  (congrSnd (returned_tail F s a C1 C2 E K x)).eqTrans (snd_pair _ _)
theorem returned_numerator (F : PR 3) (s a C1 C2 E K x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F s a C1 C2 E K x))) ≐ two*(C1+C2) := (congrFst (returned_budget F s a C1 C2 E K x)).eqTrans (fst_pair _ _)
theorem returned_denominator (F : PR 3) (s a C1 C2 E K x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run F s a C1 C2 E K x))) ≐ E*unit s := (congrSnd (returned_budget F s a C1 C2 E K x)).eqTrans (snd_pair _ _)
theorem returned_distance (F : PR 3) (s a C1 C2 E K L x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run F s a C1 C2 E K x)) (fstT (sndT (run F s a C1 C2 E K x)))
      (fstT (sndT (sndT (run F s a C1 C2 E K x)))) (sndT (sndT (sndT (run F s a C1 C2 E K x)))) :=
  distance_congr (returned_full F s a C1 C2 E K x).eqSymm (returned_pieces F s a C1 C2 E K x).eqSymm
    (returned_numerator F s a C1 C2 E K x).eqSymm (returned_denominator F s a C1 C2 E K x).eqSymm
    (shared_step_additivity F s a C1 C2 E K L x h)

theorem actual_common_weight_sum_distance_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 1) ⋏ (le one (var 2) ⋏ (le one (var 6) ⋏ termsDistance f g (var 0*var 2) (var 3) (var 4) (var 5) (var 6)))) ⟶
      distanceBounded (qmul (weight one (var 1) (var 2)) (sum f (var 0*var 2) (var 3)))
        (qmul (weight one (var 1) (var 2)) (sum g (var 0*var 2) (var 4))) (var 0*var 5) (var 1*var 6)) :=
  closeUniv 7 (.impI (weighted_sum_distance f g _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_shared_step_compact_additivity_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (quadrature F (var 0) ((var 2+var 3)*var 5) (var 1) (var 2+var 3) (var 4) (var 7))
        (qadd (quadrature F (var 0) (var 2*var 5) (var 1) (var 2) (var 4) (var 7))
          (quadrature F (var 0) (var 3*var 5) (var 1+var 2) (var 3) (var 4) (var 7))) (two*(var 2+var 3)) (var 4*unit (var 0))) :=
  closeUniv 8 (.impI (shared_step_additivity F _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_finite_compact_additivity_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at F _ _ _ _ _ _ _)
theorem actual_returned_finite_compact_additivity_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (fstT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)))
        (fstT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))))
        (fstT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)))))
        (sndT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)))))) :=
  closeUniv 8 (.impI (returned_distance F _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactRiemannAdditivity
