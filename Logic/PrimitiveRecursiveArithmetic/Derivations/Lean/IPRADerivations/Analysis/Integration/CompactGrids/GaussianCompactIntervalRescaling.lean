import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity

/-!
# Actual compact names respect positive interval denominator rescaling

The original tuple (a,C,E) and its actual positive natural multiple
represent the same interval. Their original grid time codes remain
distinct. Canonical fraction cancellation proves time-value equality;
the original zero-distance sampled modulus, retaining its observation
errors, controls the actual evaluator calls and original finite sums.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactIntervalRescaling

open_ipra
open GaussianCompactRiemannName (inside sampledModulus localBody grid value sampleData sampleBody sample quadrature mesh precision
  sampled_modulus_rate shift_sampled_modulus)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight)
open GaussianRationalFiniteSum (sum)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (F : PR 3) (k a C E L T x : PTm n) : Fm PTm n :=
  le one k ⋏ GaussianCompactRiemannName.input F a C E L T x
ipra_subst input

theorem inside_unscale (k a C E t : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (h : Γ ⊢[PRAAx] inside (k*a) (k*C) (k*E) t) : Γ ⊢[PRAAx] inside a C E t := by
  have lower : Γ ⊢[PRAAx] le (k*(a*sndT t)) (k*(E*fstT t)) :=
    le_congr (by ipra_ring) (by ipra_ring) h.andE₂.andE₂.andE₁
  have upper : Γ ⊢[PRAAx] le (k*(E*fstT t)) (k*((a+C)*sndT t)) :=
    le_congr (by ipra_ring) (by ipra_ring) h.andE₂.andE₂.andE₂
  exact .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI (RationalValueBounds.positive_cancel hk lower) (RationalValueBounds.positive_cancel hk upper)))

theorem rescaled_modulus (F : PR 3) (k a C E L x : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx] sampledModulus F (k*a) (k*C) (k*E) L x := by
  have hs := shift_sampled_modulus <| shift_sampled_modulus <|
    shift_sampled_modulus <| shift_sampled_modulus h
  have ks := Order.shift_one_le <| Order.shift_one_le <| Order.shift_one_le <| Order.shift_one_le hk
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,PTm.subst_mul,Syn.shift] using sampled_modulus_rate F _ _ _ _ _
    (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk
    (inside_unscale _ _ _ _ _ ks.wk.wk.wk.wk Prf.hyp0.wk.wk) (inside_unscale _ _ _ _ _ ks.wk.wk.wk.wk Prf.hyp1) Prf.hyp0

theorem scaled_input (F : PR 3) (k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input F (k*a) (k*C) (k*E) L T x := by
  have width : Γ ⊢[PRAAx] le (k*C) ((k*E)*T) :=
    le_congr (.eqRefl _) (by ipra_ring) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl k) h.andE₂.andE₂.andE₂.andE₁)
  exact .andI (positive_product _ _ h.andE₁ h.andE₂.andE₁)
    (.andI (positive_product _ _ h.andE₁ h.andE₂.andE₂.andE₁) (.andI width
      (rescaled_modulus F k a C E L x h.andE₁ h.andE₂.andE₂.andE₂.andE₂)))

/-- Only represented time values coincide; original time codes and
original evaluator calls are retained as separate actual program terms. -/
theorem grid_value (i N k a C E : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    value (grid i N (k*a) (k*C) (k*E)) ≐ value (grid i N a C E) :=
  (GaussianCompactRiemannName.value_grid i N (k*a) (k*C) (k*E)).eqTrans
    ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)).eqTrans
      ((GaussianCompactRiemannSplit.fraction_cancel k (a*N+C*i) (E*N) hk (positive_product _ _ hE hN)).eqTrans
        (GaussianCompactRiemannName.value_grid i N a C E).eqSymm))

theorem weight_value (N k C E : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] weight (k*C) (k*E) N ≐ weight C E N :=
  (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl (k*C)) (by ipra_ring : Γ ⊢[PRAAx] (k*E)*N ≐ k*(E*N))).eqTrans
    (GaussianCompactRiemannSplit.fraction_cancel k C (E*N) hk (positive_product _ _ hE hN))

theorem term_distance (F : PR 3) (i s N k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody F) i (sampleData s N a C E x))
      (inst2 (sampleBody F) i (sampleData s N (k*a) (k*C) (k*E) x)) two (unit s) := by
  have first := GaussianCompactRiemannName.grid_inside i N a C E h.andE₂.andE₁ h.andE₂.andE₂.andE₁ hN (le_of_lt hi)
  have second := inside_unscale k a C E _ h.andE₁ (GaussianCompactRiemannName.grid_inside i N (k*a) (k*C) (k*E)
    (positive_product _ _ h.andE₁ h.andE₂.andE₁) (positive_product _ _ h.andE₁ h.andE₂.andE₂.andE₁) hN (le_of_lt hi))
  have actual := GaussianCompactRiemannAdditivity.equal_value_samples F s a C E L x _ _ h.andE₂.andE₂.andE₂.andE₂ first second
    (grid_value i N k a C E h.andE₁ h.andE₂.andE₂.andE₁ hN).eqSymm
  exact distance_congr (GaussianCompactRiemannName.sample_body_at F i s N a C E x).eqSymm
    (GaussianCompactRiemannName.sample_body_at F i s N (k*a) (k*C) (k*E) x).eqSymm (.eqRefl _) (.eqRefl _) actual

/-- Actual finite weighted sums have a quantitative observation error;
no false sample equality is inferred from time-value equality. -/
theorem quadrature_distance (F : PR 3) (s N k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s N a C E x) (quadrature F s N (k*a) (k*C) (k*E) x) (C*two) (E*unit s) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F (Syn.shift k) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have terms : Γ ⊢[PRAAx] termsDistance (sampleBody F) (sampleBody F) N (sampleData s N a C E x)
      (sampleData s N (k*a) (k*C) (k*E) x) two (unit s) := by
    refine .allI (.impI ?_)
    simpa only [GaussianCompactRiemannName.subst_sampleData,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using term_distance F (var 0) (Syn.shift s) (Syn.shift N)
      (Syn.shift k) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) hs.wk ns.wk Prf.hyp0
  have den := positive_product (Γ := Γ) _ _ h.andE₂.andE₂.andE₁ hN
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ den (unit_positive s)
    (GaussianRationalRiemannRefinement.weight_bound C E N h.andE₂.andE₂.andE₁ hN)
    (sum_distance _ _ N _ _ two (unit s) (unit_positive s) terms)
  have weighted := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm (.eqRefl _) (.eqRefl _) raw
  have clear := distance_radius_mono _ _ _ _ (C*two) (E*unit s)
    (positive_product _ _ den (unit_positive s)) (positive_product _ _ h.andE₂.andE₂.andE₁ (unit_positive s))
    (le_of_eq_add (d := zero) (by ipra_ring)) weighted
  exact distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (weight_value N k C E h.andE₁ h.andE₂.andE₂.andE₁ hN).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) clear

/-- SAME old mesh and original evaluator; only the represented interval
encoding was positively rescaled. -/
theorem sample_distance (F : PR 3) (p k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample F p (k*a) (k*C) (k*E) L T x) two (unit (p+num 6)) := by
  have raw := quadrature_distance F (precision p T) (mesh p L T) k a C E L T x h (GaussianCompactRiemannName.mesh_positive p L T)
  apply distance_radius_mono _ _ _ _ two (unit (p+num 6))
    (positive_product _ _ h.andE₂.andE₂.andE₁ (unit_positive _)) (unit_positive _) _ raw
  have width := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (two*unit (p+num 6))) h.andE₂.andE₂.andE₂.andE₁
  have precision := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (two*E)) (GaussianCompactRiemannName.precision_lower (Γ := Γ) p T)
  have first : Γ ⊢[PRAAx] le ((C*two)*unit (p+num 6)) (two*E*(unit (p+num 6)*T)) :=
    le_congr (by ipra_ring) (by ipra_ring) width
  exact le_trans first (le_congr (.eqRefl _) (by ipra_ring) precision)

theorem diagonal_distance (F : PR 3) (p k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample F p (k*a) (k*C) (k*E) L T x) two (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) (GaussianFactorBudget.power_monotone_length two p (p+num 6)
      (le_succ_self one) (le_add_right _ _))) (sample_distance F p k a C E L T x h)

theorem name_rescaling (F : PR 3) (k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F)
      (GaussianCompactRiemannName.data a C E L T x) (GaussianCompactRiemannName.data (k*a) (k*C) (k*E) L T x) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ two
    (GaussianCompactRiemannName.name_regular F a C E L T x h.andE₂)
    (GaussianCompactRiemannName.name_regular F (k*a) (k*C) (k*E) L T x (scaled_input F k a C E L T x h))
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F (Syn.shift k) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) :=
    by simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  refine .allI ?_
  have raw := diagonal_distance F (var 0) (Syn.shift k) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) hs
  have converted := distance_congr (GaussianCompactRiemannName.name_at F (var 0) (Syn.shift a) (Syn.shift C)
      (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x)).eqSymm
    (GaussianCompactRiemannName.name_at F (var 0) (Syn.shift k*Syn.shift a) (Syn.shift k*Syn.shift C)
      (Syn.shift k*Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) raw
  simpa only [GaussianCompactRiemannName.subst_data,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using converted

theorem observations (F : PR 3) (p q k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample F q (k*a) (k*C) (k*E) L T x) (unit p+unit q) (unit p*unit q) :=
  distance_congr (GaussianCompactRiemannName.name_at F p a C E L T x) (GaussianCompactRiemannName.name_at F q (k*a) (k*C) (k*E) L T x)
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (name_rescaling F k a C E L T x h))

def output (F : PR 3) (p q k a C E L T x : PTm n) : PTm n := pairT (sample F p a C E L T x)
  (pairT (sample F q (k*a) (k*C) (k*E) L T x) (pairT (unit p+unit q) (unit p*unit q)))
def outputF (F : PR 3) : PR 9 := PTm.toPR (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
def run (F : PR 3) (p q k a C E L T x : PTm n) : PTm n := PTm.app (outputF F) ![p,q,k,a,C,E,L,T,x]
ipra_subst output
theorem program_at (F : PR 3) (p q k a C E L T x : PTm n) : Γ ⊢[PRAAx]
    run F p q k a C E L T x ≐ output F p q k a C E L T x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9) ![p,q,k,a,C,E,L,T,x]
theorem returned_left (F : PR 3) (p q k a C E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (run F p q k a C E L T x) ≐ sample F p a C E L T x :=
  (program_at F p q k a C E L T x).fstE
theorem returned_tail (F : PR 3) (p q k a C E L T x : PTm n) : Γ ⊢[PRAAx]
    sndT (run F p q k a C E L T x) ≐ pairT (sample F q (k*a) (k*C) (k*E) L T x) (pairT (unit p+unit q) (unit p*unit q)) :=
  (program_at F p q k a C E L T x).sndE
theorem returned_right (F : PR 3) (p q k a C E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F p q k a C E L T x)) ≐ sample F q (k*a) (k*C) (k*E) L T x :=
  (returned_tail F p q k a C E L T x).fstE
theorem returned_budget (F : PR 3) (p q k a C E L T x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F p q k a C E L T x)) ≐ pairT (unit p+unit q) (unit p*unit q) :=
  (returned_tail F p q k a C E L T x).sndE
theorem returned_numerator (F : PR 3) (p q k a C E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F p q k a C E L T x))) ≐ unit p+unit q :=
  (returned_budget F p q k a C E L T x).fstE
theorem returned_denominator (F : PR 3) (p q k a C E L T x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run F p q k a C E L T x))) ≐ unit p*unit q :=
  (returned_budget F p q k a C E L T x).sndE
theorem returned_distance (F : PR 3) (p q k a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F k a C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run F p q k a C E L T x)) (fstT (sndT (run F p q k a C E L T x)))
      (fstT (sndT (sndT (run F p q k a C E L T x)))) (sndT (sndT (sndT (run F p q k a C E L T x)))) :=
  distance_congr (returned_left F p q k a C E L T x).eqSymm (returned_right F p q k a C E L T x).eqSymm
    (returned_numerator F p q k a C E L T x).eqSymm (returned_denominator F p q k a C E L T x).eqSymm
    (observations F p q k a C E L T x h)

theorem actual_inside_interval_unscale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 0) ⋏ inside (var 0*var 1) (var 0*var 2) (var 0*var 3) (var 4)) ⟶ inside (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (inside_unscale _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_scaled_original_compact_input_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianCompactRiemannName.input F (var 0*var 1) (var 0*var 2) (var 0*var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (scaled_input F _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_rescaled_original_quadratures_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 1)) ⟶
      distanceBounded (quadrature F (var 0) (var 1) (var 3) (var 4) (var 5) (var 8))
        (quadrature F (var 0) (var 1) (var 2*var 3) (var 2*var 4) (var 2*var 5) (var 8)) (var 4*two) (var 5*unit (var 0))) :=
  closeUniv 9 (.impI (quadrature_distance F _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_rescaled_compact_names_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F)
        (GaussianCompactRiemannName.data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (GaussianCompactRiemannName.data (var 0*var 1) (var 0*var 2) (var 0*var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (name_rescaling F _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_rescaled_independent_observations_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (sample F (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (sample F (var 1) (var 2*var 3) (var 2*var 4) (var 2*var 5) (var 6) (var 7) (var 8))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (observations F _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_interval_rescaling_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ≐
      output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) :=
  closeUniv 9 (program_at F _ _ _ _ _ _ _ _ _)
theorem actual_returned_interval_rescaling_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (fstT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (fstT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))))
        (fstT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))))
        (sndT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))))) :=
  closeUniv 9 (.impI (returned_distance F _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactIntervalRescaling
