import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaExponentStep
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmExponentialIdentity

/-!
# Adjacent-cutoff independence of the actual original C7 construction

The actual exponent step is exponentiated using the checked radius
transport and addition operation. Original local C4 gives the actual next
Euler factor. Exact head succession and the checked name ring laws then
give equality of the original C7 names at N and N+1, without division.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaAdjacentCutoff

open_ipra
open GaussianRationalHorner (qmul ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNameEquivalence (diagonalEquivalent crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular exponentF exponentialF)
open GaussianGammaCutoffName (exponentData exponentRadius exponentialData head nameF data)
open GaussianGammaCanonicalTailName (source)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Cross equivalences are passed through the actual multiplication
program, retaining each side's independently computed normalization. -/
theorem multiply_cross (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hfp : Γ ⊢[PRAAx] pointCN f' x')
    (hg : Γ ⊢[PRAAx] pointCN g y) (hgp : Γ ⊢[PRAAx] pointCN g' y')
    (he : Γ ⊢[PRAAx] crossEquivalent f f' x x') (he' : Γ ⊢[PRAAx] crossEquivalent g g' y y') :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) (multiplyF f' g')
      (multiplyData f g x y) (multiplyData f' g' x' y') :=
  GaussianNameArithmetic.multiply_equivalent _ _ _ _ _ _ _ _ hf hfp hg hgp
    (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ he')

theorem linear_constant_diagonal (w : PTm n) : Γ ⊢[PRAAx]
    diagonalEquivalent GaussianFiniteLogarithmCompositionName.constantF constantF w
      (GaussianFiniteLogarithmCompositionTail.linearValue w) := by
  refine .allI ?_
  have a := GaussianFiniteLogarithmCompositionName.constant_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift w)
  have b := constant_at (Γ := Γ.map Fm.shift) (var 0) (GaussianFiniteLogarithmCompositionTail.linearValue (Syn.shift w))
  have e := distance_radius_mono (Γ := Γ.map Fm.shift) _ _ zero (unit (var 0)) two (unit (var 0))
    (unit_positive (var 0)) (unit_positive (var 0))
    (le_of_eq_add (d := two*unit (var 0)) (by ipra_ring))
    (GaussianRationalPowerDifference.distance_refl_zero
      (GaussianFiniteLogarithmCompositionTail.linearValue (Syn.shift w)) (unit (var 0)) (unit_positive (var 0)))
  simpa only [diagonalEquivalent,Syn.shift,GaussianFiniteLogarithmCompositionTail.subst_linearValue,
    GaussianFiniteLogarithmCompositionName.constant] using
    distance_congr a.eqSymm b.eqSymm (.eqRefl _) (.eqRefl _) e

theorem linear_constant_cross (w : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent GaussianFiniteLogarithmCompositionName.constantF constantF w
      (GaussianFiniteLogarithmCompositionTail.linearValue w) :=
  GaussianNameEquivalence.diagonal_to_cross _ _ _ _ (GaussianFiniteLogarithmCompositionName.constant_regular w)
    (constant_regular _) (linear_constant_diagonal w)

def localData (z R B N : PTm n) : PTm n := GaussianLocalLogarithmName.data z (R*B) (B*succ N)
def commonRadius (z R B N : PTm n) : PTm n := exponentRadius z R B (succ N)+one
def factorProductF : PR 2 := multiplyF exponentialF constantF
def factorProductData (z R B N : PTm n) : PTm n := multiplyData exponentialF constantF
  (exponentialData z R B (succ N)) (GaussianGammaEulerHead.factor N z B)
ipra_subst localData
ipra_subst commonRadius
ipra_subst factorProductData

theorem local_exponential_factor (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF GaussianLocalLogarithmName.pointF) constantF
      (GaussianRadiusExponentialName.data one (localData z R B N)) (GaussianGammaEulerHead.factor N z B) := by
  have hs := GaussianGammaExponentStep.local_source z R B N h
  have old := GaussianLocalLogarithmName.original_exponential_input z (R*B) (B*succ N) hs
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _
    (GaussianExponentialRadiusIndependence.original_unit_cross _ _ old))
    (cross_trans _ _ _ _ _ _ (GaussianLocalLogarithmExponentialIdentity.source_cross z (R*B) (B*succ N) hs)
      (linear_constant_cross (ofGaussian z (B*succ N))))

/-- The actual bounded-name exponential at cutoff N equals the actual
product of the successor exponential and the original Euler factor. -/
theorem exponential_step_factor (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent exponentialF factorProductF (exponentialData z R B N) (factorProductData z R B N) := by
  let W := commonRadius z R B N
  let X := exponentData z R B (succ N)
  let Y := localData z R B N
  let G := GaussianLocalLogarithmName.pointF
  have hs := GaussianGammaCanonicalTailMetric.source_successor z R B N h
  have nextInput := GaussianGammaCutoffName.exponential_input z R B (succ N) hs
  have localInput := GaussianExponentialRadiusIndependence.radius_one_input G Y
    (GaussianLocalLogarithmName.original_exponential_input z (R*B) (B*succ N)
      (GaussianGammaExponentStep.local_source z R B N h))
  have nextWide := GaussianExponentialRadiusIndependence.input_widen exponentF (exponentRadius z R B (succ N)) W X nextInput
    (le_add_right _ _)
  have localWide := GaussianExponentialRadiusIndependence.input_widen G one W Y localInput
    (le_of_eq_add (d := exponentRadius z R B (succ N)) (by unfold W commonRadius; ipra_ring))
  have wPositive : Γ ⊢[PRAAx] le one W :=
    le_of_eq_add (d := exponentRadius z R B (succ N)) (by unfold W commonRadius; ipra_ring)
  have compared := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF GaussianGammaExponentStep.stepF
    (exponentRadius z R B N) (W+W) (exponentData z R B N) (GaussianGammaExponentStep.stepData z R B N)
    (GaussianGammaCutoffName.exponential_input z R B N h)
    (GaussianExponentialReference.add_input exponentF G W X Y nextWide localWide)
    (GaussianGammaExponentStep.exponent_step_equivalent z R B N h)
  have addition := GaussianExponentialAddition.exponential_add_cross exponentF G W X Y wPositive nextWide localWide
  have oldE := GaussianExponentialRadiusIndependence.same_input_cross exponentF W (exponentRadius z R B (succ N)) X nextWide nextInput
  have oldL := cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.same_input_cross G W one Y localWide localInput)
    (local_exponential_factor z R B N h)
  have products := multiply_cross (GaussianRadiusExponentialName.nameF exponentF) exponentialF
    (GaussianRadiusExponentialName.nameF G) constantF _ _ _ _
    (GaussianRadiusExponentialName.name_regular exponentF W X nextWide)
    (GaussianGammaCutoffName.exponential_regular z R B (succ N) hs)
    (GaussianRadiusExponentialName.name_regular G W Y localWide) (constant_regular _) oldE oldL
  exact cross_trans _ _ _ _ _ _ compared (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ addition) products)

theorem head_successor (z B N : PTm n) : Γ ⊢[PRAAx] head z B (succ N) ≐
    qmul (head z B N) (GaussianGammaEulerHead.factor N z B) :=
  (GaussianGammaEulerHead.program_at z B (succ N)).eqTrans
    ((GaussianGammaEulerHead.head_succ z B N).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (GaussianGammaEulerHead.program_at z B N).eqSymm (.eqRefl _)))

theorem head_product_at (p z B N : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyF constantF constantF) p
      (multiplyData constantF constantF (head z B N) (GaussianGammaEulerHead.factor N z B)) ≐ head z B (succ N) :=
  (GaussianNameArithmetic.multiply_at constantF constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr
      (constant_at _ _) (constant_at _ _))).eqTrans
        ((GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
          (head_successor z B N).eqSymm))

theorem head_product_cross (z B N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF constantF constantF) constantF
      (multiplyData constantF constantF (head z B N) (GaussianGammaEulerHead.factor N z B)) (head z B (succ N)) := by
  refine GaussianNameEquivalence.diagonal_to_cross _ _ _ _
    (multiply_fast _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _) (.allI ?_)
  have a := head_product_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift z) (Syn.shift B) (Syn.shift N)
  have b := constant_at (Γ := Γ.map Fm.shift) (var 0) (head (Syn.shift z) (Syn.shift B) (succ (Syn.shift N)))
  have e := distance_radius_mono (Γ := Γ.map Fm.shift) _ _ zero (unit (var 0)) two (unit (var 0))
    (unit_positive (var 0)) (unit_positive (var 0))
    (le_of_eq_add (d := two*unit (var 0)) (by ipra_ring))
    (GaussianRationalPowerDifference.distance_refl_zero
      (head (Syn.shift z) (Syn.shift B) (succ (Syn.shift N))) (unit (var 0)) (unit_positive (var 0)))
  simpa only [diagonalEquivalent,Syn.shift,GaussianNameArithmetic.subst_multiplyData,
    GaussianGammaCutoffName.subst_head,GaussianGammaEulerHead.subst_factor,ConciseIPRA.PTm.subst_succ] using
    distance_congr a.eqSymm b.eqSymm (.eqRefl _) (.eqRefl _) e

/-- Adjacent-cutoff C7 identity for the actual original programs, valid
also when the literal polynomial head vanishes. -/
theorem adjacent_cutoff_equivalent (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B N) (data z R B (succ N)) := by
  let H := head z B N
  let F := GaussianGammaEulerHead.factor N z B
  let X := exponentialData z R B (succ N)
  have hs := GaussianGammaCanonicalTailMetric.source_successor z R B N h
  have cnNext := GaussianGammaCutoffName.exponential_regular z R B (succ N) hs
  have cnFactor := multiply_fast exponentialF constantF X F cnNext (constant_regular F)
  have cnSwap := multiply_fast constantF exponentialF F X (constant_regular F) cnNext
  have cnHead := multiply_fast (Γ := Γ) constantF constantF H F (constant_regular H) (constant_regular F)
  have first := multiply_cross constantF constantF exponentialF factorProductF H H _ _
    (constant_regular H) (constant_regular H) (GaussianGammaCutoffName.exponential_regular z R B N h)
    cnFactor (cross_refl constantF H (constant_regular H)) (exponential_step_factor z R B N h)
  have swap := GaussianNameRingLaws.multiply_commutative exponentialF constantF X F cnNext (constant_regular F)
  have second := multiply_cross constantF constantF factorProductF (multiplyF constantF exponentialF) H H _ _
    (constant_regular H) (constant_regular H) cnFactor cnSwap
    (cross_refl constantF H (constant_regular H)) swap
  have associate := GaussianNameRingLaws.multiply_associative constantF constantF exponentialF H F X
    (constant_regular H) (constant_regular F) cnNext
  have final := multiply_cross (multiplyF constantF constantF) constantF exponentialF exponentialF _ _ X X
    cnHead (constant_regular (head z B (succ N))) cnNext cnNext
    (head_product_cross z B N) (cross_refl exponentialF X cnNext)
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ second (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ associate) final))

/-! The actual supplier returns the original C7 data at the two cutoffs. -/
def output (z R B N : PTm n) : PTm n := pairT (data z R B N) (data z R B (succ N))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z R B N : PTm n) : PTm n := PTm.app outputF ![z,R,B,N]
ipra_subst output
ipra_subst run
theorem program_at (z R B N : PTm n) : Γ ⊢[PRAAx] run z R B N ≐ output z R B N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,R,B,N]
theorem returned_first (z R B N : PTm n) : Γ ⊢[PRAAx] fstT (run z R B N) ≐ data z R B N :=
  (program_at _ _ _ _).fstE
theorem returned_successor (z R B N : PTm n) : Γ ⊢[PRAAx] sndT (run z R B N) ≐ data z R B (succ N) :=
  (program_at _ _ _ _).sndE
theorem returned_equivalence (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (fstT (run z R B N)) (sndT (run z R B N)) := by
  have eq := Prf.eqSubst (Γ := Γ) (crossEquivalent nameF nameF (var 0) (var 1) : Fm PTm 2)
    ![data z R B N,data z R B (succ N)] ![fstT (run z R B N),sndT (run z R B N)]
    (fun i => by fin_cases i; exact (returned_first z R B N).eqSymm; exact (returned_successor z R B N).eqSymm)
    (by simpa using adjacent_cutoff_equivalent z R B N h)
  simpa using eq

theorem original_local_exponential_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (GaussianRadiusExponentialName.nameF GaussianLocalLogarithmName.pointF) constantF
        (GaussianRadiusExponentialName.data one (localData (var 0) (var 1) (var 2) (var 3)))
        (GaussianGammaEulerHead.factor (var 3) (var 0) (var 2))) :=
  closeUniv 4 (.impI (local_exponential_factor _ _ _ _ Prf.hyp0))
theorem original_C7_exponential_factor_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent exponentialF factorProductF
      (exponentialData (var 0) (var 1) (var 2) (var 3)) (factorProductData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exponential_step_factor _ _ _ _ Prf.hyp0))
theorem actual_original_head_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (head (var 0) (var 1) (succ (var 2)) ≐ qmul (head (var 0) (var 1) (var 2))
      (GaussianGammaEulerHead.factor (var 2) (var 0) (var 1))) := closeUniv 3 (head_successor _ _ _)
theorem original_C7_adjacent_cutoff_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF nameF
      (data (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (succ (var 3)))) :=
  closeUniv 4 (.impI (adjacent_cutoff_equivalent _ _ _ _ Prf.hyp0))
theorem actual_adjacent_cutoff_supplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_adjacent_cutoff_returned_data_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ data (var 0) (var 1) (var 2) (var 3)) ⋏
      (sndT (run (var 0) (var 1) (var 2) (var 3)) ≐ data (var 0) (var 1) (var 2) (succ (var 3)))) :=
  closeUniv 4 (.andI (returned_first _ _ _ _) (returned_successor _ _ _ _))
theorem original_returned_adjacent_cutoff_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF nameF
      (fstT (run (var 0) (var 1) (var 2) (var 3))) (sndT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (returned_equivalence _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaAdjacentCutoff
