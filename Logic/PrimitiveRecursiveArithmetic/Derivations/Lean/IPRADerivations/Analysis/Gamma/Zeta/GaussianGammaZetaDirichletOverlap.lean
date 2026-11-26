import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaDirichletCofinal
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# The original Dirichlet value is independent of the chart bounds

The finite prefixes use the same inverse-power names at each index
when the native parameter is fixed. A common late cutoff and the two
original truncation rates identify the cofinal names on their overlap.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletOverlap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerPositiveScalingConstant (inverseF inverseData inverse_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaDirichletCofinal (nameF cutoff observations regular)
open GaussianGammaZetaDirichletFiniteRate (prefixData)
open GaussianGammaZetaMellinDampedImproper (dirichletF dirichletBody parameters dirichlet_at)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamilyCongruence (family_sum_cross)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "cd" => GaussianGammaZetaDirichletCofinal.data

private theorem same_rows (N z R S B A J : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] equalRows inverseF inverseF dirichletBody dirichletBody N
      (parameters (shifted z B) (R+one) B A) (parameters (shifted z B) (S+one) B J) := by
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  let w := shifted (sh z) (sh B)
  let j : PTm (n+1) := succ (var 0)
  let d := inverseData w (sh B) j one
  have hd : Δ ⊢[PRAAx] le one (sh B) := by
    simpa [Fm.shift,Syn.shift,sh,Δ,one] using hb.shift.wk
  have same := cross_refl inverseF d (inverse_regular w (sh B) j one (.andI hd (.andI (zero_lt_succ _) (le_refl one))))
  have e := cross_data_congr inverseF inverseF d
    (inst2 dirichletBody (var 0) (parameters w (sh R+one) (sh B) (sh A))) d
    (inst2 dirichletBody (var 0) (parameters w (sh S+one) (sh B) (sh J)))
    (dirichlet_at (var 0) w (sh R+one) (sh B) (sh A)).eqSymm
    (dirichlet_at (var 0) w (sh S+one) (sh B) (sh J)).eqSymm same
  simpa only [Syn.shift,sh,w,Δ,GaussianGammaZetaMellinDampedImproper.subst_parameters,
    GaussianGammaEulerHeadShift.subst_shifted,PTm.subst_add,PTm.subst_succ,PTm.subst_zero,one] using e

theorem finite_overlap (N z R S B A J : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent dirichletF dirichletF (prefixData N z R B A) (prefixData N z S B J) :=
  family_sum_cross inverseF inverseF dirichletBody dirichletBody N _ _ (same_rows N z R S B A J hb)

theorem original_observations (p z R S B A J : PTm n)
    (ha : Γ ⊢[PRAAx] source z R B A) (hj : Γ ⊢[PRAAx] source z S B J) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (cd z R B A)) (ap2 nameF p (cd z S B J)) (num 6) (unit p) := by
  let K := cutoff A p
  let L := cutoff J p
  let N := K+L
  let x := prefixData N z R B A
  let y := prefixData N z S B J
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have d := positive_product _ _ hu hu
  have left := GaussianGammaZetaDirichletCofinal.late_observations p p N z R B A ha (le_add_right K L)
  have right := GaussianGammaZetaDirichletCofinal.late_observations p p N z S B J hj (le_add_left L K)
  have mid := cross_at dirichletF dirichletF x y p p (finite_overlap N z R S B A J ha.andE₁.andE₂.andE₁.andE₁)
  have all := distance_triangle_same _ _ _ _ _ _ d left
    (distance_triangle_same _ _ _ _ _ _ d mid (distance_symmetric _ _ _ _ d right))
  exact distance_radius_mono _ _ _ _ (num 6) u d hu (le_of_eq_add (d := zero) (by dsimp only [u]; ipra_ring)) all

theorem original_overlap (z R S B A J : PTm n)
    (ha : Γ ⊢[PRAAx] source z R B A) (hj : Γ ⊢[PRAAx] source z S B J) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (cd z R B A) (cd z S B J) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (regular z R B A ha) (regular z S B J hj) (.allI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ] using ha.shift
  have js : Δ ⊢[PRAAx] source (sh z) (sh S) (sh B) (sh J) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hj.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianGammaZetaDirichletCofinal.data,
    GaussianGammaZetaMellinDampedImproper.subst_parameters,PTm.subst_num,Syn.shift,sh,Δ] using
    original_observations (var 0) (sh z) (sh R) (sh S) (sh B) (sh A) (sh J) hs js

theorem actual_original_Dirichlet_chart_overlap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 3) (var 4) ⟶ source (var 0) (var 2) (var 3) (var 5) ⟶
        crossEquivalent nameF nameF (cd (var 0) (var 1) (var 3) (var 4)) (cd (var 0) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (original_overlap _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletOverlap
