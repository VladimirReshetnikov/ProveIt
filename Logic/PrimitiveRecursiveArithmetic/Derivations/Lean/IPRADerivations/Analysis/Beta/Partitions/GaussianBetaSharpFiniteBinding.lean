import IPRADerivations.Analysis.Beta.EulerProducts.GaussianBetaFiniteEulerAtCutoff
import IPRADerivations.Analysis.Beta.Tails.GaussianBetaZeroExtendedGrid
import IPRADerivations.Analysis.Beta.Tails.GaussianBetaZeroExtensionAligned
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedSplit
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpPartition
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaRefinedFixedCompactComparison
import IPRADerivations.Analysis.Euler.GaussianEulerImproperName
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffGeometry

/-!
# Binding the shared grid to the original finite and improper Euler names

The extended beta quadrature loses only the aligned-time sampling error
when its zero exterior is removed. The Euler quadrature uses a mesh
refining the literal improper sampler at the same cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpFiniteBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaFiniteEulerComparison (supportWidth support_width_endpoint)
open GaussianBetaSharpPartition (exteriorWidth)
open GaussianBetaKernelGridComparison (sampleDataBeta)
open GaussianGammaCompactQuadratureBoundary (width width_bound exact_right_endpoint)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive top)
open GaussianGammaEulerCompactQuadrature (conservativeCells)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature)
open GaussianCompactAlignedSplit (quadrature_congr quadrature_empty quadrature_canonical)
open GaussianRationalHorner (positive_product qadd qzero)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fullBeta (p k A R K z B N : PTm n) : PTm n :=
  GaussianBetaZeroExtendedGrid.sample p (width k A R*K) one (width k A R) (etaDen k A R) z B N
def fullEuler (p k A R K z B : PTm n) : PTm n :=
  quadrature GaussianEulerIntegrandName.evaluatorF p (width k A R*K) one (width k A R)
    (etaDen k A R) (GaussianEulerIntegrandName.fixedData z B)
def multiplier (H k A R : PTm n) : PTm n := H*conservativeCells (k+num 4) k A R

theorem multiplier_positive (H k A R : PTm n) (hH : Γ ⊢[PRAAx] le one H) :
    Γ ⊢[PRAAx] le one (multiplier H k A R) :=
  GaussianBetaRefinedFixedCompactComparison.refined_mesh_positive (k+num 4) H k A R hH

theorem support_and_exterior_width (k A R N : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hTop : Γ ⊢[PRAAx] le N (top k A R)) :
    Γ ⊢[PRAAx] supportWidth (etaDen k A R) N+exteriorWidth k A R N ≐ width k A R := by
  let E := etaDen k A R
  let U := supportWidth E N
  let X := exteriorWidth k A R N
  have hs := support_width_endpoint E N (eta_den_positive k A R) hN
  have hx : Γ ⊢[PRAAx] E*N+X ≐ E*top k A R := by
    exact (eq_add_of_le (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E hTop))).eqSymm
  apply add_left_cancel (a := one)
  exact (show Γ ⊢[PRAAx] one+(U+X) ≐ (one+U)+X by ipra_ring).eqTrans
    ((congrAdd hs (.eqRefl X)).eqTrans (hx.eqTrans (exact_right_endpoint k A R).eqSymm))

private theorem exterior_at_shared_count (p a C E K z B N : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hK : Γ ⊢[PRAAx] le one K) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le (E*N) a) :
    Γ ⊢[PRAAx] GaussianBetaZeroExtendedGrid.sample p (C*K) a C E z B N ≐ qzero := by
  let F := GaussianBetaZeroExtension.evaluatorF
  let x := sampleDataBeta z B N
  apply Prf.orE (zero_or_succ C)
  · have hc : (C ≐ zero) :: Γ ⊢[PRAAx] C*K ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl K)).eqTrans (zero_mul K)
    exact (quadrature_congr F (.eqRefl p) hc (.eqRefl a) (.eqRefl C) (.eqRefl E) (.eqRefl x)).eqTrans
      (quadrature_empty F p a C E x)
  · have hp : (C ≐ succ (pred C)) :: Γ ⊢[PRAAx] le one C :=
      le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact GaussianBetaZeroExtendedGrid.exterior_grid_zero p (C*K) a C E z B N
      hE.wk (positive_product _ _ hp hK.wk) hN.wk ha.wk

/-- The full extended grid and the original finite-support grid differ by
the aligned-time error alone. -/
theorem finite_support_comparison (p k A R K z B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hN : Γ ⊢[PRAAx] le one N) (hTop : Γ ⊢[PRAAx] le N (top k A R))
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded (fullBeta p k A R K z B N)
      (GaussianBetaFiniteEulerAtCutoff.observation p k z R B A N (supportWidth (etaDen k A R) N*K))
      (two*width k A R) (etaDen k A R*unit p) := by
  let F := GaussianBetaZeroExtension.evaluatorF
  let E := etaDen k A R
  let U := supportWidth E N
  let X := exteriorWidth k A R N
  let W := width k A R
  let x := sampleDataBeta z B N
  have hE := eta_den_positive (Γ := Γ) k A R
  have hs := support_width_endpoint E N hE hN
  have hw := support_and_exterior_width k A R N hN hTop
  have aligned := GaussianBetaZeroExtensionAligned.original_aligned_samples z R B E N (U+X)
    (.andI h.andE₁ (.andI hE h.andE₂)) hN
  have split := GaussianCompactAlignedSplit.shared_step_additivity F p one U X E K x
    (.andI (le_refl one) (.andI hE (.andI hK aligned)))
  have headEq := quadrature_congr F (.eqRefl p) (congrMul hw (.eqRefl K))
    (.eqRefl one) hw (.eqRefl E) (.eqRefl x)
  have tailEq := exterior_at_shared_count p (one+U) X E K z B N hE hK hN
    (le_congr (.eqRefl _) hs.eqSymm (le_refl _))
  have remove := (qadd_congr (.eqRefl (quadrature F p (U*K) one U E x)) tailEq).eqTrans
    (GaussianRationalLinearProduct.qadd_zero_right _ (quadrature_canonical F p (U*K) one U E x))
  have supported := GaussianBetaZeroExtendedGrid.same_supported_grid p (U*K) one U E z B N
    (le_congr hs.eqSymm (.eqRefl _) (le_refl _))
  exact distance_congr headEq (remove.eqTrans supported) (congrMul (.eqRefl two) hw) (.eqRefl _) split

/-- The shared extended-grid observation approximates the original finite
Euler name at an independent query. -/
theorem original_finite_euler (t p q k z R B A N K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaFiniteEulerComparison.source z R B A N)
    (hTop : Γ ⊢[PRAAx] le N (top k A R)) (hK : Γ ⊢[PRAAx] le one K)
    (hk : Γ ⊢[PRAAx] le (GaussianBetaFiniteEulerAtCutoff.minimumCutoff t A) k)
    (hM : Γ ⊢[PRAAx] le (GaussianBetaFiniteEulerAtCutoff.minimumCells t k z R B A N)
      (supportWidth (etaDen k A R) N*K))
    (hp : Γ ⊢[PRAAx] le (GaussianBetaFiniteEulerAtCutoff.minimumPrecision t k z R B A N
      (supportWidth (etaDen k A R) N*K)) p)
    (hTime : Γ ⊢[PRAAx] le (two*top k A R*unit t) (unit p)) : Γ ⊢[PRAAx]
      distanceBounded (fullBeta p k A R K z B N) (ap2 eulerF q (eulerData z R B A N))
        (unit t+two*unit q) (unit t*unit q) := by
  let E := etaDen k A R
  let W := width k A R
  let T := top k A R
  let U := unit t
  let V := unit q
  have hu := unit_positive (Γ := Γ) t
  have hv := unit_positive (Γ := Γ) q
  have hd := positive_product _ _ hu hv
  have src : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B :=
    h.andE₁.andE₂.andE₁
  have split := finite_support_comparison p k A R K z B N src
    (GaussianBetaFiniteEulerComparison.degree_positive z R B A N h) hTop hK
  have compare : Γ ⊢[PRAAx] le (two*W*U) (one*(E*unit p)) := by
    have wr := mul_le_mul_right U (mul_le_mul_right two (width_bound (Γ := Γ) k A R))
    exact le_trans (le_congr (by ipra_ring) (show Γ ⊢[PRAAx] (E*T)*two*U ≐ (two*T*U)*E by ipra_ring) wr)
      (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right E hTime))
  have first := distance_radius_mono _ _ _ _ _ _
    (positive_product E _ (eta_den_positive k A R) (unit_positive p)) hu compare split
  have second := GaussianBetaFiniteEulerAtCutoff.original_at_cutoff t p q k z R B A N
    (supportWidth E N*K) h hk hM hp
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hd) hd
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hu hd first second)

/-- The common multiplier refines the compact grid used by the actual
improper sampler. An independent output query costs its own observation error. -/
theorem original_improper_euler (t p v k z R B A H : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerImproperName.source z R B A)
    (hH : Γ ⊢[PRAAx] le one H) (ht : Γ ⊢[PRAAx] le t k)
    (hp : Γ ⊢[PRAAx] le (GaussianBetaRefinedFixedCompactComparison.referencePrecision (k+num 4) k A R) p) :
    Γ ⊢[PRAAx] distanceBounded (fullEuler p k A R (multiplier H k A R) z B)
      (ap2 GaussianEulerImproperName.nameF v (GaussianEulerImproperName.data z R B A))
      (unit t+num 4*unit v) (unit t*unit v) := by
  let W := width k A R
  let q := k+num 4
  let M := conservativeCells q k A R
  let x := GaussianEulerIntegrandName.fixedData z B
  let U := unit t
  let V := unit v
  have hu := unit_positive (Γ := Γ) t
  have hv := unit_positive (Γ := Γ) v
  have hd := positive_product _ _ hu hv
  have later := GaussianExponentialReference.unit_monotone (Γ := Γ) ht
  have muchLater : Γ ⊢[PRAAx] le U (unit (q+num 6)) :=
    GaussianExponentialReference.unit_monotone (le_trans ht (le_trans (le_add_right _ _) (le_add_right _ _)))
  have hWH := positive_product W H (GaussianGammaCompactCutoffGeometry.width_positive k A R) hH
  have refined := GaussianBetaRefinedFixedCompactComparison.original_euler_refinement p q (W*H) z R B k A h.andE₁ hWH hp
  have meshEq : Γ ⊢[PRAAx] W*(H*M) ≐ (W*H)*M := by ipra_ring
  have leftEq := quadrature_congr GaussianEulerIntegrandName.evaluatorF
    (.eqRefl p) meshEq (.eqRefl one) (.eqRefl W) (.eqRefl (etaDen k A R)) (.eqRefl x)
  have first := distance_radius_mono _ _ _ _ _ _ (unit_positive (q+num 6)) hu
    (mul_le_mul_right (num 3) muchLater |> le_congr (mul_comm _ _) (mul_comm _ _))
    (distance_congr leftEq.eqSymm (GaussianEulerImproperName.original_observation k z R B A).eqSymm
      (.eqRefl _) (.eqRefl _) refined)
  have bridge : Γ ⊢[PRAAx] le ((unit k+V)*(U*V)) ((U+V)*(unit k*V)) := by
    have term := mul_le_mul_right (V*V) later
    have add := add_le_add_right (unit k*U*V) term
    exact le_congr (by ipra_ring) (by ipra_ring) add
  have second := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive k) hv) hd bridge
    (GaussianEulerImproperName.observations k v z R B A h)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hd) hd
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hu hd first second)

theorem actual_extended_grid_original_finite_Euler_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((GaussianBetaFiniteEulerComparison.source (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
        le (var 8) (top (var 3) (var 7) (var 5)) ⋏ le one (var 9) ⋏
        le (GaussianBetaFiniteEulerAtCutoff.minimumCutoff (var 0) (var 7)) (var 3) ⋏
        le (GaussianBetaFiniteEulerAtCutoff.minimumCells (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
          (supportWidth (etaDen (var 3) (var 7) (var 5)) (var 8)*var 9) ⋏
        le (GaussianBetaFiniteEulerAtCutoff.minimumPrecision (var 0) (var 3) (var 4) (var 5) (var 6)
          (var 7) (var 8) (supportWidth (etaDen (var 3) (var 7) (var 5)) (var 8)*var 9)) (var 1) ⋏
        le (two*top (var 3) (var 7) (var 5)*unit (var 0)) (unit (var 1))) ⟶
        distanceBounded (fullBeta (var 1) (var 3) (var 7) (var 5) (var 9) (var 4) (var 6) (var 8))
          (ap2 eulerF (var 2) (eulerData (var 4) (var 5) (var 6) (var 7) (var 8)))
          (unit (var 0)+two*unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 10 (.impI (original_finite_euler _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

theorem actual_shared_grid_original_improper_Euler_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((GaussianEulerImproperName.source (var 4) (var 5) (var 6) (var 7) ⋏
        le one (var 8) ⋏ le (var 0) (var 3) ⋏
        le (GaussianBetaRefinedFixedCompactComparison.referencePrecision (var 3+num 4) (var 3) (var 7) (var 5)) (var 1)) ⟶
        distanceBounded (fullEuler (var 1) (var 3) (var 7) (var 5)
          (multiplier (var 8) (var 3) (var 7) (var 5)) (var 4) (var 6))
          (ap2 GaussianEulerImproperName.nameF (var 2) (GaussianEulerImproperName.data (var 4) (var 5) (var 6) (var 7)))
          (unit (var 0)+num 4*unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 9 (.impI (original_improper_euler _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpFiniteBinding
