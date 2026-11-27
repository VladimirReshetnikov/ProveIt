import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactRiemannAdditivity
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# Actual compact names are additive across an original rational split

The SAME old compact names are compared with genuine shared-step
refinements. Original sampled-modulus inputs derive both subinterval
inputs, finite shared-step additivity, and a vanishing diagonal error.
The actual normalized addF program is retained; no name induction or
integral/additivity output law is supplied as an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactNamedAdditivity

open_ipra
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_den)
open GaussianCompactRiemannName (sampledModulus localBody inside evaluatorName nameData sample quadrature mesh precision
  sampled_modulus_rate shift_sampled_modulus)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent point_at_later)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- Pure elimination of the original four numerical rate parameters. -/
theorem local_rate (F : PR 3) (a C E L x t u A D : PTm n) (h : Γ ⊢[PRAAx] sampledModulus F a C E L x)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate (evaluatorName F) (evaluatorName F) (nameData t x) (nameData u x) (L*A) D :=
  sampled_modulus_rate F a C E L x t u A D h hD ht hu hd

theorem left_modulus (F : PR 3) (a C1 C2 E L x : PTm n) (h : Γ ⊢[PRAAx] sampledModulus F a (C1+C2) E L x) : Γ ⊢[PRAAx]
    sampledModulus F a C1 E L x := by
  have hs := shift_sampled_modulus <| shift_sampled_modulus <|
    shift_sampled_modulus <| shift_sampled_modulus h
  simp only [Syn.shift, PTm.subst_add] at hs
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody, PTm.subst_add, Syn.shift] using sampled_modulus_rate F _ _ _ _ _ (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk (GaussianCompactRiemannAdditivity.inside_left _ _ _ _ _ Prf.hyp0.wk.wk)
    (GaussianCompactRiemannAdditivity.inside_left _ _ _ _ _ Prf.hyp1) Prf.hyp0

theorem right_modulus (F : PR 3) (a C1 C2 E L x : PTm n) (h : Γ ⊢[PRAAx] sampledModulus F a (C1+C2) E L x) : Γ ⊢[PRAAx]
    sampledModulus F (a+C1) C2 E L x := by
  have hs := shift_sampled_modulus <| shift_sampled_modulus <|
    shift_sampled_modulus <| shift_sampled_modulus h
  simp only [Syn.shift, PTm.subst_add] at hs
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody, PTm.subst_add, Syn.shift] using sampled_modulus_rate F _ _ _ _ _ (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk (GaussianCompactRiemannAdditivity.inside_right _ _ _ _ _ Prf.hyp0.wk.wk)
    (GaussianCompactRiemannAdditivity.inside_right _ _ _ _ _ Prf.hyp1) Prf.hyp0

def input (F : PR 3) (a C1 C2 E L T x : PTm n) : Fm PTm n := le one a ⋏ (le one E ⋏ (le one C1 ⋏ (le one C2 ⋏
  (le (C1+C2) (E*T) ⋏ sampledModulus F a (C1+C2) E L x))))
ipra_subst input

theorem full_input (F : PR 3) (a C1 C2 E L T x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input F a (C1+C2) E L T x :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂))
theorem left_input (F : PR 3) (a C1 C2 E L T x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input F a C1 E L T x :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI (le_trans (le_add_right C1 C2) h.andE₂.andE₂.andE₂.andE₂.andE₁)
    (left_modulus F a C1 C2 E L x h.andE₂.andE₂.andE₂.andE₂.andE₂)))
theorem right_input (F : PR 3) (a C1 C2 E L T x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input F (a+C1) C2 E L T x :=
  .andI (le_trans h.andE₁ (le_add_right _ _)) (.andI h.andE₂.andE₁ (.andI (le_trans (le_add_left C2 C1) h.andE₂.andE₂.andE₂.andE₂.andE₁)
    (right_modulus F a C1 C2 E L x h.andE₂.andE₂.andE₂.andE₂.andE₂)))

def refined (F : PR 3) (p a C E L T x : PTm n) : PTm n := quadrature F (precision p T) (C*mesh p L T) a C E x
ipra_subst refined

/-- Same actual name, genuinely refined by its numerical width. -/
theorem refinement_distance (F : PR 3) (p a C E L T x : PTm n) (hC : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] GaussianCompactRiemannName.input F a C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (refined F p a C E L T x) (sample F p a C E L T x) (num 3) (unit (p+num 6)) := by
  let N := mesh p L T
  let U := unit (precision p T)
  let K := unit (p+num 6)
  have n := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have raw := GaussianCompactRiemannName.quadrature_refinement F (precision p T) (precision p T) N C a C E L x h.andE₁ h.andE₂.andE₁ n hC h.andE₂.andE₂.andE₂
  have budget := GaussianCompactRiemannName.quadrature_budget C E L N U U K T h.andE₂.andE₂.andE₁
    (GaussianCompactRiemannName.mesh_cost p L T) (GaussianCompactRiemannName.precision_lower p T) (GaussianCompactRiemannName.precision_lower p T)
  have den := positive_product _ _ h.andE₂.andE₁ (positive_product _ _ (positive_product _ _ h.andE₂.andE₁ n)
    (positive_product _ _ (unit_positive (precision p T)) (unit_positive (precision p T))))
  apply distance_radius_mono _ _ _ _ (num 3) K
    (le_congr (.eqRefl _) (by unfold GaussianNamedInverseRate.rateDenominator; ipra_ring) den) (unit_positive _) _ raw
  exact budget

/-- A bound on the shared-step refinement pays three observation units at an earlier clock. -/
theorem observation_bound_of_refined (F : PR 3) (r s a C E L T x A D : PTm n)
    (hrs : Γ ⊢[PRAAx] le r s) (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D)
    (hin : Γ ⊢[PRAAx] GaussianCompactRiemannName.input F a C E L T x)
    (hbound : Γ ⊢[PRAAx] bounded (refined F s a C E L T x) A D) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianCompactRiemannName.nameF F) r (GaussianCompactRiemannName.data a C E L T x))
      (A*unit r+num 3*D) (D*unit r) := by
  let G := GaussianCompactRiemannName.nameF F
  let d := GaussianCompactRiemannName.data a C E L T x
  let w := refined F s a C E L T x
  have hr := unit_positive (Γ := Γ) r
  have hs := unit_positive (Γ := Γ) (s+num 6)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 G r d) (ap2 G s d) two (unit r) :=
    distance_symmetric _ _ _ _ hr (point_at_later G d r s
      (GaussianCompactRiemannName.name_regular F a C E L T x hin) hrs)
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) F s a C E L T x
  have room := le_trans (mul_le_mul_left (num 3) (GaussianExponentialReference.unit_monotone hrs))
    (GaussianCompactRiemannName.dyadic_six_lower s)
  have refineGap : Γ ⊢[PRAAx] distanceBounded (ap2 G s d) w one (unit r) :=
    distance_radius_mono _ _ _ _ _ _ hs hr (le_congr (.eqRefl _) (one_mul _).eqSymm room)
      (distance_symmetric _ _ _ _ hs
        (distance_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl _) (refinement_distance F s a C E L T x hC hin)))
  have distance : Γ ⊢[PRAAx] distanceBounded (ap2 G r d) w (num 3) (unit r) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hr near refineGap)
  exact bound_congr (.eqRefl _) (by ipra_ring) (mul_comm _ _)
    (GaussianReconstructionRoots.norm_from_distance (ap2 G r d) w (num 3) (unit r) A D hr hD distance hbound)

theorem finite_at_name_grid (F : PR 3) (p a C1 C2 E L T x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    distanceBounded (refined F p a (C1+C2) E L T x)
      (qadd (refined F p a C1 E L T x) (refined F p (a+C1) C2 E L T x)) two (unit (p+num 6)) := by
  have k := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have old := GaussianCompactRiemannAdditivity.shared_step_additivity F (precision p T) a C1 C2 E (mesh p L T) L x
    (.andI h.andE₁ (.andI h.andE₂.andE₁ (.andI k (.andI h.andE₂.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂)))))
  apply distance_radius_mono _ _ _ _ two (unit (p+num 6)) (positive_product _ _ h.andE₂.andE₁ (unit_positive _)) (unit_positive _) _ old
  ipra_le (2*𝔞(unit (p+num 6)))*sl h.andE₂.andE₂.andE₂.andE₂.andE₁+
    (2*𝔞(E))*sl (GaussianCompactRiemannName.precision_lower (Γ := Γ) p T)

theorem sample_additivity (F : PR 3) (p a C1 C2 E L T x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a (C1+C2) E L T x)
      (qadd (sample F p a C1 E L T x) (sample F p (a+C1) C2 E L T x)) (num 11) (unit (p+num 6)) := by
  have full := distance_symmetric _ _ _ _ (unit_positive _) (refinement_distance F p a (C1+C2) E L T x
    (GaussianCompactRiemannSplit.sum_width_positive C1 C2 h.andE₂.andE₂.andE₁) (full_input F a C1 C2 E L T x h))
  have left := refinement_distance F p a C1 E L T x h.andE₂.andE₂.andE₁ (left_input F a C1 C2 E L T x h)
  have right := refinement_distance F p (a+C1) C2 E L T x h.andE₂.andE₂.andE₂.andE₁ (right_input F a C1 C2 E L T x h)
  have pieces := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ (unit_positive _) left right
  have total := distance_triangle_same _ _ _ _ _ _ (unit_positive _) (distance_triangle_same _ _ _ _ _ _ (unit_positive _) full
    (finite_at_name_grid F p a C1 C2 E L T x h)) pieces
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) total

/-- The actual normalized addition observation, retaining both original
compact interval programs and their unchanged parameters. -/
def addedSample (F : PR 3) (p a C1 C2 E L T x : PTm n) : PTm n :=
  ap2 (GaussianNameArithmetic.addF (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F)) p
    (GaussianNameArithmetic.addData (GaussianCompactRiemannName.data a C1 E L T x)
      (GaussianCompactRiemannName.data (a+C1) C2 E L T x))
ipra_subst addedSample

theorem normalized_sample_additivity (F : PR 3) (p a C1 C2 E L T x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a (C1+C2) E L T x) (addedSample F p a C1 C2 E L T x) (num 14) (unit p) := by
  have old := sample_additivity F p a C1 C2 E L T x h
  have mono := GaussianFactorBudget.power_monotone_length (Γ := Γ) two p (p+num 6) (le_succ_self one) (le_add_right _ _)
  have widened := distance_radius_mono_den (unit_positive _) mono old
  have correction := GaussianNameRingLaws.add_sample_error (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F)
    (GaussianCompactRiemannName.data a C1 E L T x) (GaussianCompactRiemannName.data (a+C1) C2 E L T x) p
    (GaussianCompactRiemannName.name_regular F a C1 E L T x (left_input F a C1 C2 E L T x h))
    (GaussianCompactRiemannName.name_regular F (a+C1) C2 E L T x (right_input F a C1 C2 E L T x h))
  have adjusted := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qadd_congr
    (GaussianCompactRiemannName.name_at F p a C1 E L T x) (GaussianCompactRiemannName.name_at F p (a+C1) C2 E L T x))
      (.eqRefl _) (.eqRefl _) correction
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive _) widened (distance_symmetric _ _ _ _ (unit_positive _) adjusted))

/-- Exact cross-equivalence of the SAME original compact name with the
actual normalized sum of the SAME two subinterval names. -/
theorem name_additivity (F : PR 3) (a C1 C2 E L T x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.nameF F)
      (GaussianNameArithmetic.addF (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F))
      (GaussianCompactRiemannName.data a (C1+C2) E L T x)
      (GaussianNameArithmetic.addData (GaussianCompactRiemannName.data a C1 E L T x)
        (GaussianCompactRiemannName.data (a+C1) C2 E L T x)) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 14)
    (GaussianCompactRiemannName.name_regular F a (C1+C2) E L T x (full_input F a C1 C2 E L T x h))
    (GaussianNameArithmetic.add_fast _ _ _ _
      (GaussianCompactRiemannName.name_regular F a C1 E L T x (left_input F a C1 C2 E L T x h))
      (GaussianCompactRiemannName.name_regular F (a+C1) C2 E L T x (right_input F a C1 C2 E L T x h)))
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  refine .allI ?_
  have raw := normalized_sample_additivity F (var 0) (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) hs
  have converted := distance_congr (GaussianCompactRiemannName.name_at F (var 0) (Syn.shift a) (Syn.shift C1+Syn.shift C2)
    (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
  simpa only [GaussianCompactRiemannName.subst_data,GaussianNameArithmetic.subst_addData,PTm.subst_add,
    addedSample,PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using converted

/-- Split a compact name while retaining the same offset in both subintervals. -/
theorem name_additivity_with_offset (F : PR 3) (b a C1 C2 E L T x : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hE : Γ ⊢[PRAAx] le one E)
    (h1 : Γ ⊢[PRAAx] le one C1) (h2 : Γ ⊢[PRAAx] le one C2)
    (horizon : Γ ⊢[PRAAx] le (a+(C1+C2)) (E*T))
    (modulus : Γ ⊢[PRAAx] sampledModulus F (b+a) (C1+C2) E L x) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.nameF F)
      (GaussianNameArithmetic.addF (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F))
      (GaussianCompactRiemannName.data (b+a) (C1+C2) E L T x)
      (GaussianNameArithmetic.addData (GaussianCompactRiemannName.data (b+a) C1 E L T x)
        (GaussianCompactRiemannName.data (b+(a+C1)) C2 E L T x)) := by
  have h : Γ ⊢[PRAAx] input F (b+a) C1 C2 E L T x :=
    .andI (le_trans hb (le_add_right b a)) (.andI hE (.andI h1 (.andI h2
      (.andI (le_trans (le_add_left (C1+C2) a) horizon) modulus))))
  have right := GaussianCompactRiemannName.data_congr (Γ := Γ) (add_assoc b a C1)
    (.eqRefl C2) (.eqRefl E) (.eqRefl L) (.eqRefl T) (.eqRefl x)
  exact GaussianNameEquivalence.cross_data_congr _ _ _ _ _ _ (.eqRefl _)
    (GaussianNameArithmetic.add_data_congr (.eqRefl _) right)
    (name_additivity F (b+a) C1 C2 E L T x h)

theorem observations (F : PR 3) (p q a C1 C2 E L T x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a (C1+C2) E L T x) (addedSample F q a C1 C2 E L T x)
      (unit p+unit q) (unit p*unit q) :=
  distance_congr (GaussianCompactRiemannName.name_at F p a (C1+C2) E L T x) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ p q (name_additivity F a C1 C2 E L T x h))

def output (F : PR 3) (p q a C1 C2 E L T x : PTm n) : PTm n :=
  pairT (sample F p a (C1+C2) E L T x) (pairT (addedSample F q a C1 C2 E L T x) (pairT (unit p+unit q) (unit p*unit q)))
def outputF (F : PR 3) : PR 9 := PTm.toPR (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
def run (F : PR 3) (p q a C1 C2 E L T x : PTm n) : PTm n := PTm.app (outputF F) ![p,q,a,C1,C2,E,L,T,x]
ipra_subst output
theorem program_at (F : PR 3) (p q a C1 C2 E L T x : PTm n) : Γ ⊢[PRAAx]
    run F p q a C1 C2 E L T x ≐ output F p q a C1 C2 E L T x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9) ![p,q,a,C1,C2,E,L,T,x]
theorem returned_full (F : PR 3) (p q a C1 C2 E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (run F p q a C1 C2 E L T x) ≐ sample F p a (C1+C2) E L T x :=
  (program_at F p q a C1 C2 E L T x).fstE
theorem returned_tail (F : PR 3) (p q a C1 C2 E L T x : PTm n) : Γ ⊢[PRAAx]
    sndT (run F p q a C1 C2 E L T x) ≐ pairT (addedSample F q a C1 C2 E L T x) (pairT (unit p+unit q) (unit p*unit q)) :=
  (program_at F p q a C1 C2 E L T x).sndE
theorem returned_sum (F : PR 3) (p q a C1 C2 E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F p q a C1 C2 E L T x)) ≐ addedSample F q a C1 C2 E L T x :=
  (returned_tail F p q a C1 C2 E L T x).fstE
theorem returned_budget (F : PR 3) (p q a C1 C2 E L T x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F p q a C1 C2 E L T x)) ≐ pairT (unit p+unit q) (unit p*unit q) :=
  (returned_tail F p q a C1 C2 E L T x).sndE
theorem returned_numerator (F : PR 3) (p q a C1 C2 E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F p q a C1 C2 E L T x))) ≐ unit p+unit q :=
  (returned_budget F p q a C1 C2 E L T x).fstE
theorem returned_denominator (F : PR 3) (p q a C1 C2 E L T x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run F p q a C1 C2 E L T x))) ≐ unit p*unit q :=
  (returned_budget F p q a C1 C2 E L T x).sndE
theorem returned_distance (F : PR 3) (p q a C1 C2 E L T x : PTm n) (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run F p q a C1 C2 E L T x)) (fstT (sndT (run F p q a C1 C2 E L T x)))
      (fstT (sndT (sndT (run F p q a C1 C2 E L T x)))) (sndT (sndT (sndT (run F p q a C1 C2 E L T x)))) :=
  distance_congr (returned_full F p q a C1 C2 E L T x).eqSymm (returned_sum F p q a C1 C2 E L T x).eqSymm
    (returned_numerator F p q a C1 C2 E L T x).eqSymm (returned_denominator F p q a C1 C2 E L T x).eqSymm
    (observations F p q a C1 C2 E L T x h)

theorem actual_compact_samples_additive_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (sample F (var 0) (var 1) (var 2+var 3) (var 4) (var 5) (var 6) (var 7))
        (qadd (sample F (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7))
          (sample F (var 0) (var 1+var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) (num 11) (unit (var 0+num 6))) :=
  closeUniv 8 (.impI (sample_additivity F _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_normalized_compact_additivity_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (sample F (var 0) (var 1) (var 2+var 3) (var 4) (var 5) (var 6) (var 7))
        (addedSample F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (num 14) (unit (var 0))) :=
  closeUniv 8 (.impI (normalized_sample_additivity F _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_compact_names_additive_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent (GaussianCompactRiemannName.nameF F)
        (GaussianNameArithmetic.addF (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F))
        (GaussianCompactRiemannName.data (var 0) (var 1+var 2) (var 3) (var 4) (var 5) (var 6))
        (GaussianNameArithmetic.addData (GaussianCompactRiemannName.data (var 0) (var 1) (var 3) (var 4) (var 5) (var 6))
          (GaussianCompactRiemannName.data (var 0+var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))) :=
  closeUniv 7 (.impI (name_additivity F _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_compact_additivity_independent_observations_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (sample F (var 0) (var 2) (var 3+var 4) (var 5) (var 6) (var 7) (var 8))
        (addedSample F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (observations F _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_compact_additivity_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ≐
      output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) :=
  closeUniv 9 (program_at F _ _ _ _ _ _ _ _ _)
theorem actual_returned_compact_additivity_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (fstT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (fstT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))))
        (fstT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))))
        (sndT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))))) :=
  closeUniv 9 (.impI (returned_distance F _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactNamedAdditivity
