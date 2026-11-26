import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUpperTailNameBudget
import IPRADerivations.Analysis.Gamma.GaussianGammaCompactCutoffSplit
import IPRADerivations.Core.CongruenceTactic

/-!
# Exact original named Euler upper-tail bound

The actual upperData from the original cutoff split is unchanged.
Its real compact mesh and evaluator precision feed the true finite
upper-tail kernel at auxiliary reference precision s. A computed K
controls every finite error. Original pointCN and one rational finite
gap remove that auxiliary error, retaining exactly the requested
observation error. Equal cutoffs use literal zero-width observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedUpperTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCompactCutoffSplit (source upperData upper_regular)
open GaussianGammaIntegralCutoffs (etaDen top height)
open GaussianGammaCompactCutoffGeometry (upperWidth)
open GaussianEulerCompactAdditivity (nameF)
open GaussianEulerCompactModulus (lipschitz)
open GaussianCompactRiemannName (mesh precision quadrature)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianEulerUpperTailNameBudget (errorCost finiteNumerator finiteDenominator)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (p z R B k j A : PTm n) : PTm n := ap2 nameF p (upperData z R B k j A)
def cost (k j A R : PTm n) : PTm n := errorCost R (upperWidth k j A R)
def cofinalNumerator (s k j A R : PTm n) : PTm n := two*majorant R*unit s+cost k j A R*unit (height k A R)
def cofinalDenominator (s k A R : PTm n) : PTm n := unit (height k A R)*unit s
def numerator (p k A R : PTm n) : PTm n := two*majorant R*unit p+unit (height k A R)
def denominator (p k A R : PTm n) : PTm n := unit (height k A R)*unit p
@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (p z R B k j A : PTm n) :
    Syn.subst σ (point p z R B k j A) = point (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ k) (Syn.subst σ j) (Syn.subst σ A) := by simp [point]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (k j A R : PTm n) :
    Syn.subst σ (cost k j A R) = cost (Syn.subst σ k) (Syn.subst σ j) (Syn.subst σ A) (Syn.subst σ R) := by simp [cost]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p k A R : PTm n) :
    Syn.subst σ (numerator p k A R) = numerator (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [numerator,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p k A R : PTm n) :
    Syn.subst σ (denominator p k A R) = denominator (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [denominator,height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem quadrature_start_congr (F : PR 3) (p N a a' C E x : PTm n) (ha : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx]
    quadrature F p N a C E x ≐ quadrature F p N a' C E x :=
  GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
    (GaussianRationalFiniteSum.sum_index_congr (GaussianCompactRiemannName.sampleBody F) (.eqRefl N)
      (congrPairT (.eqRefl p) (congrPairT (.eqRefl N) (congrPairT ha (.eqRefl _)))))

theorem point_at (s z R B k j A : PTm n) : Γ ⊢[PRAAx]
    point s z R B k j A ≐ quadrature evaluatorF (precision s (top j A R))
      (mesh s (lipschitz R (etaDen j A R) (top j A R)) (top j A R))
      (top k A R*etaDen j A R) (upperWidth k j A R) (etaDen j A R) (fixedData z B) :=
  (GaussianCompactRiemannName.name_at evaluatorF s (etaDen j A R*top k A R) (upperWidth k j A R)
    (etaDen j A R) (lipschitz R (etaDen j A R) (top j A R)) (top j A R) (fixedData z B)).eqTrans
      (quadrature_start_congr _ _ _ _ _ _ _ _ (mul_comm _ _))

theorem cofinal_denominator_positive (s k A R : PTm n) : Γ ⊢[PRAAx] le one (cofinalDenominator s k A R) :=
  positive_product _ _ (unit_positive _) (unit_positive s)
theorem denominator_positive (p k A R : PTm n) : Γ ⊢[PRAAx] le one (denominator p k A R) :=
  positive_product _ _ (unit_positive _) (unit_positive p)

/-- Every finite error in the actual original compact observation is
bounded by the internally computed K/2^s. -/
theorem cofinal_bound_strict (s z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) (hkj : Γ ⊢[PRAAx] lt k j) : Γ ⊢[PRAAx]
    bounded (point s z R B k j A) (cofinalNumerator s k j A R) (cofinalDenominator s k A R) := by
  let E := etaDen j A R
  let T := top j A R
  let L := lipschitz R E T
  let C := upperWidth k j A R
  let P := precision s T
  let N := mesh s L T
  have ep := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) j A R
  have np := GaussianCompactRiemannName.mesh_positive (Γ := Γ) s L T
  have cp := GaussianGammaCompactCutoffGeometry.upper_positive k j A R hkj
  have step := GaussianEulerUpperTailNameBudget.original_mesh_step s k j A R h.andE₂.andE₂
  have raw := GaussianEulerCompactUpperTail.original_upper_cutoff_bound P s N k A C E z R B np cp ep step h.andE₁
  have widened := bounded_radius_mono _ _ _ (cofinalNumerator s k j A R) (cofinalDenominator s k A R)
    (GaussianEulerUpperTailNameBudget.denominator_positive P s N (height k A R) E ep np) (cofinal_denominator_positive s k A R)
    (GaussianEulerUpperTailNameBudget.finite_budget P s N (height k A R) C E R ep
      (GaussianEulerUpperTailNameBudget.mesh_unit_lower s L T) (GaussianEulerUpperTailNameBudget.precision_unit_lower s T)) raw
  exact bound_congr (point_at s z R B k j A).eqSymm (.eqRefl _) (.eqRefl _) widened

theorem point_zero_of_width_zero (s z R B k j A : PTm n) (hc : Γ ⊢[PRAAx] upperWidth k j A R ≐ zero) : Γ ⊢[PRAAx]
    point s z R B k j A ≐ qzero := by
  let E := etaDen j A R
  let T := top j A R
  have eqData : Γ ⊢[PRAAx] upperData z R B k j A ≐ GaussianEulerCompactAdditivity.data z R B (E*top k A R) zero E T :=
    GaussianGammaCompactCutoffSplit.euler_data_congr _ _ _ _ _ _ _ _ _ _ _ (.eqRefl _) hc (.eqRefl _) (.eqRefl _)
  exact (congrAp2 nameF (.eqRefl s) eqData).eqTrans
    (GaussianCompactZeroWidth.observation_zero evaluatorF s (E*top k A R) E (lipschitz R E T) T (fixedData z B)
      (GaussianGammaIntegralCutoffs.eta_den_positive j A R))

theorem zero_bound (A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] bounded (qzero : PTm n) A D := by
  have zeroNorm : Γ ⊢[PRAAx] bounded (qzero : PTm n) zero one :=
    (GaussianReconstructionRoots.distance_zero_iff qzero zero one (le_refl one)).iffMp
      (GaussianRationalPowerDifference.distance_refl_zero qzero one (le_refl one))
  exact bounded_radius_mono _ _ _ _ _ (le_refl one) hD (le_of_eq_add (d := A) (by ipra_ring)) zeroNorm

theorem cofinal_bound_zero (s z R B k j A : PTm n) (hc : Γ ⊢[PRAAx] upperWidth k j A R ≐ zero) : Γ ⊢[PRAAx]
    bounded (point s z R B k j A) (cofinalNumerator s k j A R) (cofinalDenominator s k A R) :=
  bound_congr (point_zero_of_width_zero s z R B k j A hc).eqSymm (.eqRefl _) (.eqRefl _)
    (zero_bound _ _ (cofinal_denominator_positive s k A R))

theorem cofinal_bound (s z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) : Γ ⊢[PRAAx]
    bounded (point s z R B k j A) (cofinalNumerator s k j A R) (cofinalDenominator s k A R) := by
  refine .orE (lt_or_eq_of_le h.andE₂.andE₂) (cofinal_bound_strict s z R B k j A h.wk Prf.hyp0) ?_
  have widthEq : (k ≐ j) :: Γ ⊢[PRAAx] upperWidth k j A R ≐ upperWidth k k A R := by
    ipra_congr (upperWidth (var 0) (var 1) (var 2) (var 3) : PTm 4) with
      [.eqRefl k, Prf.hyp0.eqSymm, .eqRefl A, .eqRefl R]
  exact cofinal_bound_zero s z R B k j A (widthEq.eqTrans (GaussianGammaCompactCutoffGeometry.same_upper k A R))

theorem point_canonical (p z R B k j A : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (point p z R B k j A) :=
  GaussianCompactRiemannName.name_canonical evaluatorF p _ _ _ _ _ _

/-- True original pointCN keeps requested eps_p. Only the auxiliary
(K+1)eps_s will be removed at an actual rational gap query. -/
theorem observation_slack (p s z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (point p z R B k j A) (numerator p k A R) (denominator p k A R) (cost k j A R+one) s := by
  have u := unit_positive (Γ := Γ) p
  have v := unit_positive (Γ := Γ) s
  have dv := cofinal_denominator_positive (Γ := Γ) s k A R
  have dm := positive_product (Γ := Γ) _ _ u v
  have close := GaussianNameEquivalence.point_at nameF (upperData z R B k j A) p s (upper_regular z R B k j A h)
  have sum := GaussianRationalReciprocal.bounded_sum (point s z R B k j A) (qsub (point p z R B k j A) (point s z R B k j A))
    (cofinalNumerator s k j A R) (cofinalDenominator s k A R) (unit p+unit s) (unit p*unit s) dv dm (cofinal_bound s z R B k j A h) close
  have exactPoint := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (point s z R B k j A) (point p z R B k j A)
    (point_canonical p z R B k j A)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ dv dm)
    (positive_product _ _ (denominator_positive p k A R) v) _ (bound_congr exactPoint (.eqRefl _) (.eqRefl _) sum)
  exact le_of_eq_add (d := zero) (by unfold cofinalNumerator cofinalDenominator numerator denominator unit; ipra_ring)

/-- Exact original named upper tail: 2*(2^R R!)*2^-height(k)
plus the one requested ordinary observation error. -/
theorem original_named_upper_tail (p z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) : Γ ⊢[PRAAx]
    bounded (point p z R B k j A) (two*majorant R*unit p+unit (height k A R)) (unit (height k A R)*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost k j A R+one) (denominator_positive p k A R)
    (observation_slack p (GaussianRationalSlackRemoval.precision (point p z R B k j A) (numerator p k A R)
      (denominator p k A R) (cost k j A R+one)) z R B k j A h)

def output (p z R B k j A : PTm n) : PTm n := pairT (point p z R B k j A)
  (pairT (numerator p k A R) (pairT (denominator p k A R) (cost k j A R)))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (p z R B k j A : PTm n) : PTm n := PTm.app outputF ![p,z,R,B,k,j,A]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p z R B k j A : PTm n) :
    Syn.subst σ (output p z R B k j A) = output (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ k) (Syn.subst σ j) (Syn.subst σ A) := by simp [output]
theorem program_at (p z R B k j A : PTm n) : Γ ⊢[PRAAx] run p z R B k j A ≐ output p z R B k j A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,z,R,B,k,j,A]
theorem returned_point (p z R B k j A : PTm n) : Γ ⊢[PRAAx] fstT (run p z R B k j A) ≐ point p z R B k j A :=
  (congrFst (program_at p z R B k j A)).eqTrans (fst_pair _ _)
theorem returned_tail (p z R B k j A : PTm n) : Γ ⊢[PRAAx] sndT (run p z R B k j A) ≐
    pairT (numerator p k A R) (pairT (denominator p k A R) (cost k j A R)) :=
  (congrSnd (program_at p z R B k j A)).eqTrans (snd_pair _ _)
theorem returned_numerator (p z R B k j A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p z R B k j A)) ≐ numerator p k A R :=
  (congrFst (returned_tail p z R B k j A)).eqTrans (fst_pair _ _)
theorem returned_last (p z R B k j A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p z R B k j A)) ≐ pairT (denominator p k A R) (cost k j A R) :=
  (congrSnd (returned_tail p z R B k j A)).eqTrans (snd_pair _ _)
theorem returned_denominator (p z R B k j A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p z R B k j A))) ≐ denominator p k A R :=
  (congrFst (returned_last p z R B k j A)).eqTrans (fst_pair _ _)
theorem returned_cost (p z R B k j A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p z R B k j A))) ≐ cost k j A R :=
  (congrSnd (returned_last p z R B k j A)).eqTrans (snd_pair _ _)
theorem returned_bound (p z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) : Γ ⊢[PRAAx]
    bounded (fstT (run p z R B k j A)) (fstT (sndT (run p z R B k j A))) (fstT (sndT (sndT (run p z R B k j A)))) :=
  bound_congr (returned_point p z R B k j A).eqSymm (returned_numerator p z R B k j A).eqSymm
    (returned_denominator p z R B k j A).eqSymm (original_named_upper_tail p z R B k j A h)

theorem original_equal_cutoff_upper_observation_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 4) (var 5) ≐ qzero) :=
  closeUniv 6 (point_zero_of_width_zero _ _ _ _ _ _ _ (GaussianGammaCompactCutoffGeometry.same_upper _ _ _))
theorem actual_upper_tail_compact_observation_cofinal_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (cofinalNumerator (var 0) (var 4) (var 5) (var 6) (var 2)) (cofinalDenominator (var 0) (var 4) (var 6) (var 2))) :=
  closeUniv 7 (.impI (cofinal_bound _ _ _ _ _ _ _ Prf.hyp0))
theorem original_named_upper_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (numerator (var 0) (var 4) (var 6) (var 2)) (denominator (var 0) (var 4) (var 6) (var 2))) :=
  closeUniv 7 (.impI (original_named_upper_tail _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_named_upper_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem actual_returned_named_upper_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) :=
  closeUniv 7 (.impI (returned_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedUpperTail
