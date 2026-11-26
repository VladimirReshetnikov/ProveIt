import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# Actual compact quadrature names are independent of legitimate budgets

The unchanged original compact sampler is compared at two independent
valid numerical Lipschitz/width budgets. Its two actual meshes are
compared through their literal common product mesh and one computed
observation precision. The proof uses genuine original finite refinement
and finite gap removal, with no induction on name predicates or supplied
mesh/output equality.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactMeshIndependence

open_ipra
open GaussianCompactRiemannName (sample quadrature mesh precision)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (F : PR 3) (a C E L T M S x : PTm n) : Fm PTm n :=
  GaussianCompactRiemannName.input F a C E L T x ⋏ GaussianCompactRiemannName.input F a C E M S x
def commonPrecision (p T S : PTm n) : PTm n := precision p T+precision p S
def commonSample (F : PR 3) (p a C E L T M S x : PTm n) : PTm n :=
  quadrature F (commonPrecision p T S) (mesh p L T*mesh p M S) a C E x

ipra_subst input
ipra_subst commonPrecision
ipra_subst commonSample

/-- Any actual refinement factor and sufficiently late original sample
precision satisfy the SAME old compact name's numerical budget. -/
theorem arbitrary_refinement (F : PR 3) (p q R a C E L T x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianCompactRiemannName.input F a C E L T x)
    (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] le (precision p T) q) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F q (R*mesh p L T) a C E x) (sample F p a C E L T x) (num 3) (unit (p+num 6)) := by
  let N := mesh p L T
  let U := unit q
  let V := unit (precision p T)
  let K := unit (p+num 6)
  have n := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have later := GaussianFactorBudget.power_monotone_length (Γ := Γ) two (precision p T) q (le_succ_self one) hq
  have firstBudget := le_trans (GaussianCompactRiemannName.precision_lower (Γ := Γ) p T) later
  have raw := GaussianCompactRiemannName.quadrature_refinement F q (precision p T) N R a C E L x
    h.andE₁ h.andE₂.andE₁ n hR h.andE₂.andE₂.andE₂
  have budget := GaussianCompactRiemannName.quadrature_budget C E L N U V K T h.andE₂.andE₂.andE₁
    (GaussianCompactRiemannName.mesh_cost p L T) firstBudget (GaussianCompactRiemannName.precision_lower p T)
  have den := positive_product _ _ h.andE₂.andE₁ (positive_product _ _ (positive_product _ _ h.andE₂.andE₁ n)
    (positive_product _ _ (unit_positive q) (unit_positive (precision p T))))
  apply distance_radius_mono _ _ _ _ (num 3) K
    (le_congr (.eqRefl _) (by unfold GaussianNamedInverseRate.rateDenominator; ipra_ring) den) (unit_positive _) _ raw
  exact budget

theorem common_left (F : PR 3) (p a C E L T M S x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T M S x) : Γ ⊢[PRAAx]
    distanceBounded (commonSample F p a C E L T M S x) (sample F p a C E L T x) (num 3) (unit (p+num 6)) :=
  distance_congr (GaussianCompactRiemannName.quadrature_index_congr F (commonPrecision p T S)
    (mesh p M S*mesh p L T) (mesh p L T*mesh p M S) a C E x (by ipra_ring)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (arbitrary_refinement F p (commonPrecision p T S) (mesh p M S) a C E L T x h.andE₁
      (GaussianCompactRiemannName.mesh_positive p M S) (le_add_right _ _))

theorem common_right (F : PR 3) (p a C E L T M S x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T M S x) : Γ ⊢[PRAAx]
    distanceBounded (commonSample F p a C E L T M S x) (sample F p a C E M S x) (num 3) (unit (p+num 6)) :=
  arbitrary_refinement F p (commonPrecision p T S) (mesh p L T) a C E M S x h.andE₂
    (GaussianCompactRiemannName.mesh_positive p L T) (le_add_left _ _)

/-- Two original samplers at independent legitimate budgets are compared
through one real product grid, rather than identifying raw samples. -/
theorem sample_distance (F : PR 3) (p a C E L T M S x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T M S x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample F p a C E M S x) (num 6) (unit (p+num 6)) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive _)
      (distance_symmetric _ _ _ _ (unit_positive _) (common_left F p a C E L T M S x h))
      (common_right F p a C E L T M S x h))

theorem diagonal_distance (F : PR 3) (p a C E L T M S x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T M S x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample F p a C E M S x) (num 6) (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (num 6)) (GaussianFactorBudget.power_monotone_length two p (p+num 6)
      (le_succ_self one) (le_add_right _ _))) (sample_distance F p a C E L T M S x h)

/-- Exact budget independence of the actual unchanged original compact
names. Both legitimate original inputs are explicit and sufficient. -/
theorem name_independence (F : PR 3) (a C E L T M S x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T M S x) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F)
      (GaussianCompactRiemannName.data a C E L T x) (GaussianCompactRiemannName.data a C E M S x) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (GaussianCompactRiemannName.name_regular F a C E L T x h.andE₁)
    (GaussianCompactRiemannName.name_regular F a C E M S x h.andE₂)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift M) (Syn.shift S) (Syn.shift x) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  refine .allI ?_
  have raw := diagonal_distance F (var 0) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift M) (Syn.shift S) (Syn.shift x) hs
  have converted := distance_congr (GaussianCompactRiemannName.name_at F (var 0) (Syn.shift a) (Syn.shift C)
      (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x)).eqSymm
    (GaussianCompactRiemannName.name_at F (var 0) (Syn.shift a) (Syn.shift C)
      (Syn.shift E) (Syn.shift M) (Syn.shift S) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) raw
  simpa only [GaussianCompactRiemannName.subst_data,PTm.subst_num,Syn.shift] using converted

theorem observations (F : PR 3) (p q a C E L T M S x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T M S x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample F q a C E M S x) (unit p+unit q) (unit p*unit q) :=
  distance_congr (GaussianCompactRiemannName.name_at F p a C E L T x) (GaussianCompactRiemannName.name_at F q a C E M S x)
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (name_independence F a C E L T M S x h))

def output (F : PR 3) (p q a C E L T M S x : PTm n) : PTm n :=
  pairT (sample F p a C E L T x) (pairT (sample F q a C E M S x) (pairT (unit p+unit q) (unit p*unit q)))
def outputF (F : PR 3) : PR 10 := PTm.toPR (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
def run (F : PR 3) (p q a C E L T M S x : PTm n) : PTm n := PTm.app (outputF F) ![p,q,a,C,E,L,T,M,S,x]
ipra_subst output
theorem program_at (F : PR 3) (p q a C E L T M S x : PTm n) : Γ ⊢[PRAAx]
    run F p q a C E L T M S x ≐ output F p q a C E L T M S x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) : PTm 10) ![p,q,a,C,E,L,T,M,S,x]
theorem returned_left (F : PR 3) (p q a C E L T M S x : PTm n) : Γ ⊢[PRAAx]
    fstT (run F p q a C E L T M S x) ≐ sample F p a C E L T x :=
  (program_at F p q a C E L T M S x).fstE
theorem returned_tail (F : PR 3) (p q a C E L T M S x : PTm n) : Γ ⊢[PRAAx]
    sndT (run F p q a C E L T M S x) ≐ pairT (sample F q a C E M S x) (pairT (unit p+unit q) (unit p*unit q)) :=
  (program_at F p q a C E L T M S x).sndE
theorem returned_right (F : PR 3) (p q a C E L T M S x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F p q a C E L T M S x)) ≐ sample F q a C E M S x :=
  (returned_tail F p q a C E L T M S x).fstE
theorem returned_budget (F : PR 3) (p q a C E L T M S x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F p q a C E L T M S x)) ≐ pairT (unit p+unit q) (unit p*unit q) :=
  (returned_tail F p q a C E L T M S x).sndE
theorem returned_numerator (F : PR 3) (p q a C E L T M S x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F p q a C E L T M S x))) ≐ unit p+unit q :=
  (returned_budget F p q a C E L T M S x).fstE
theorem returned_denominator (F : PR 3) (p q a C E L T M S x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run F p q a C E L T M S x))) ≐ unit p*unit q :=
  (returned_budget F p q a C E L T M S x).sndE
theorem returned_distance (F : PR 3) (p q a C E L T M S x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T M S x) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run F p q a C E L T M S x)) (fstT (sndT (run F p q a C E L T M S x)))
      (fstT (sndT (sndT (run F p q a C E L T M S x)))) (sndT (sndT (sndT (run F p q a C E L T M S x)))) :=
  distance_congr (returned_left F p q a C E L T M S x).eqSymm (returned_right F p q a C E L T M S x).eqSymm
    (returned_numerator F p q a C E L T M S x).eqSymm (returned_denominator F p q a C E L T M S x).eqSymm
    (observations F p q a C E L T M S x h)

theorem actual_arbitrary_compact_refinement_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((GaussianCompactRiemannName.input F (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
      (le one (var 2) ⋏ le (precision (var 0) (var 7)) (var 1))) ⟶
      distanceBounded (quadrature F (var 1) (var 2*mesh (var 0) (var 6) (var 7)) (var 3) (var 4) (var 5) (var 8))
        (sample F (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (num 3) (unit (var 0+num 6))) :=
  closeUniv 9 (.impI (arbitrary_refinement F _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_legitimate_mesh_samples_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (sample F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 8))
        (sample F (var 0) (var 1) (var 2) (var 3) (var 6) (var 7) (var 8)) (num 6) (unit (var 0+num 6))) :=
  closeUniv 9 (.impI (sample_distance F _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_legitimate_mesh_names_independent_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F)
        (GaussianCompactRiemannName.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 7))
        (GaussianCompactRiemannName.data (var 0) (var 1) (var 2) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (name_independence F _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_independent_mesh_observations_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (sample F (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 9))
        (sample F (var 1) (var 2) (var 3) (var 4) (var 7) (var 8) (var 9)) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (observations F _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_mesh_independence_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ≐
      output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)) :=
  closeUniv 10 (program_at F _ _ _ _ _ _ _ _ _ _)
theorem actual_returned_mesh_independence_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (fstT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))
        (fstT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))))
        (fstT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))))
        (sndT (sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))))) :=
  closeUniv 10 (.impI (returned_distance F _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactMeshIndependence
