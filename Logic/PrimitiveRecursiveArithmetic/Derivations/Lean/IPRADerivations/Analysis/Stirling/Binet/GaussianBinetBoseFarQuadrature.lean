import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBoseFarBound
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBoseCompact
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceStripCutoff
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetSecondDecayEnvelope
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.SpecialFunctions.GaussianNamedDampingPowerReciprocalTail

/-!
# Uniform upper-tail bound for the original second Binet left sums

For any positive lower endpoint, use the left grid whose step is
1/(E*N). Its inverse-square majorant telescopes, giving a bound
independent of the right endpoint and of the sampling precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFarQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (fixedData subst_fixedData)
open GaussianBinetBoseCompact (evaluatorF evaluator_at tag_lower gain)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open LeanProofs.IPRA.PTm (num)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (grid grid_inside inside quadrature sampleBody sampleData sample_body_at)
open GaussianNamedDampingPowerReciprocalTail (row body gridData affine_grid_term original_scalar_left_embedded_bound)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalSumMajorant (majorized majorized_congr termsMajorized)
open GaussianRightHalfPlaneLogarithm (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] private theorem subst_gridData {m : ℕ} (σ : Fin n → PTm m) (K A E N : PTm n) :
    Syn.subst σ (gridData K A E N) = gridData (Syn.subst σ K) (Syn.subst σ A) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [gridData]

private theorem cell_majorant (i p N X Y D sign A C E K : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hi : Γ ⊢[PRAAx] lt i (C*N)) : Γ ⊢[PRAAx]
    majorized (inst2 (sampleBody evaluatorF) i (sampleData p (C*N) (E+A) C E (fixedData X Y D sign)))
      (inst2 body i (gridData K A E N)) := by
  let M := C*N
  let t := grid i M (E+A) C E
  let u := grid i M A C E
  let a := tagNumerator t
  let b := sndT t
  have hM := positive_product C N hC hN
  have ht : Γ ⊢[PRAAx] inside (E+A) C E t :=
    grid_inside i M (E+A) C E (le_trans hE (le_add_right _ _)) hE hM (le_of_lt hi)
  have ha := (tag_lower A C E t hA hE ht).andE₁
  have hb := ht.andE₂.andE₁
  have obs := GaussianBinetBoseFarBound.rational_time_bound p X Y D sign a b K hz ha hb hK
  have maj := GaussianBinetSecondDecayEnvelope.fraction_majorized _ _ _ (positive_product _ _ ha ha) obs
  have read := (sample_body_at (Γ := Γ) evaluatorF i p M (E+A) C E (fixedData X Y D sign)).eqTrans
    (evaluator_at p t X Y D sign)
  have exactTag := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) i M A C E
  have en : Γ ⊢[PRAAx] fstT u ≐ a := (fst_pair _ _).eqTrans exactTag.andE₁.eqSymm
  have ed : Γ ⊢[PRAAx] sndT u ≐ b := (snd_pair _ _).eqTrans exactTag.andE₂.eqSymm
  have scalar :
      Γ ⊢[PRAAx] inst2 body i (gridData K A E N) ≐
        GaussianEuclideanDistanceName.fraction (K*b*b) (a*a) :=
    (affine_grid_term i K A C E N hA hC hN).eqTrans
      (RationalNonnegativePowers.fraction_congr (congrMul (congrMul (.eqRefl K) ed) ed) (congrMul en en))
  exact majorized_congr read.eqSymm scalar.eqSymm maj

theorem upper_tail_bound (p N X Y D sign A C E K : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p (C*N) (E+A) C E (fixedData X Y D sign)) (two*K*E) A := by
  let M := C*N
  let f := sampleBody evaluatorF
  let x := sampleData p M (E+A) C E (fixedData X Y D sign)
  let y := gridData K A E N
  have rows : Γ ⊢[PRAAx] termsMajorized f body M x y := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s C*s N) :: Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have as' : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hA.shift.wk
    have cs : Δ ⊢[PRAAx] le one (s C) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hC.shift.wk
    have es : Δ ⊢[PRAAx] le one (s E) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hE.shift.wk
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    simpa only [f,x,y,M,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      subst_fixedData,subst_gridData,PTm.subst_add,PTm.subst_mul] using
      cell_majorant (var 0) (s p) (s N) (s X) (s Y) (s D) (s sign) (s A) (s C) (s E) (s K)
        zs as' cs es ns ks Prf.hyp0
  exact GaussianRationalSumMajorant.majorant_bound _ _ _ _ hA
    (GaussianCompactScalarMajorant.weighted_majorant f body M x y C E (positive_product C N hC hN) hE rows)
    (original_scalar_left_embedded_bound K A C E N hA hC hE hN)

theorem name_bound (p X Y D sign T A C E K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBinetBoseCompact.source X D sign T A C E)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded
      (ap2 GaussianBinetBoseCompact.nameF p (GaussianBinetBoseCompact.data X Y D sign T A C E))
      (num 3*A+(two*K*E)*unit (p+num 6)) (unit (p+num 6)*A) := by
  let x := fixedData X Y D sign
  let L := gain D E T
  let M := GaussianCompactRiemannName.mesh p L T
  let q := GaussianCompactRiemannName.precision p T
  let W := unit (p+num 6)
  let u := GaussianCompactRiemannName.sample evaluatorF p (E+A) C E L T x
  let v := quadrature evaluatorF q (C*M) (E+A) C E x
  have hA := h.andE₂.andE₁
  have hE := h.andE₂.andE₂.andE₁
  have bound := upper_tail_bound q M X Y D sign A C E K h.andE₁ hA hC hE
    (GaussianCompactRiemannName.mesh_positive p L T) hK
  have dist := GaussianCompactNamedAdditivity.refinement_distance evaluatorF p (E+A) C E L T x hC
    (GaussianBinetBoseCompact.compact_input X Y D sign T A C E h)
  have norm := GaussianReconstructionRoots.norm_from_distance u v (num 3) W (two*K*E) A
    (unit_positive _) hA (distance_symmetric v u (num 3) W (unit_positive _) dist) bound
  exact GaussianRationalReciprocal.bound_congr
    (GaussianCompactRiemannName.name_at evaluatorF p (E+A) C E L T x).eqSymm (.eqRefl _) (.eqRefl _) norm

theorem actual_second_Binet_upper_tail_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 2) (var 4) (var 5) ⋏ (le one (var 6) ⋏ le one (var 7))) ⋏
      (le one (var 8) ⋏ (le one (var 1) ⋏ le (var 4) (var 9*var 2))) ⟶
      bounded (quadrature evaluatorF (var 0) (var 7*var 1) (var 8+var 6) (var 7) (var 8)
        (fixedData (var 2) (var 3) (var 4) (var 5))) (two*var 9*var 8) (var 6)) :=
  closeUniv 10 (.impI (upper_tail_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁
    Prf.hyp0.andE₁.andE₂.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseFarQuadrature
