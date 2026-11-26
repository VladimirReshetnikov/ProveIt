import IPRADerivations.Analysis.Euler.ExponentialSubstitution.GaussianEulerExponentialLogCompact
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerLaterCutoffObservation
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingCutoffGeometry

/-!
# The original Gamma name and the cofinal exponential image sampler

The sampler evaluates the actual exponential kernel and logarithmic
widths on the images of the original Euler cutoff grids. The compact
comparison and the original omitted-tail budget pay the two independent
observation allowances for the improper value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialImproper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source)
open GaussianGammaIntegralCutoffs (etaDen height top tailCoefficient)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev data (z R B A : PTm n) : PTm n := GaussianEulerImproperName.data z R B A
def compactData (k z R B A : PTm n) : PTm n :=
  GaussianEulerExponentialLogCompact.data z R B one (width k A R) (etaDen k A R) (top k A R)
def sample (p z R B A : PTm n) : PTm n :=
  ap2 GaussianEulerExponentialLogCompact.nameF (succ (succ p)) (compactData (succ p) z R B A)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B A : PTm n) :
    Syn.subst σ (sample p z R B A) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [sample,compactData,width,etaDen,top,height,tailCoefficient]

private def fields (p x : PTm n) : Fin 5 → PTm n :=
  ![p,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))]
private def body : PTm 5 := sample (var 0) (var 1) (var 2) (var 3) (var 4)
private def reader (p x : PTm n) : PTm n := Syn.subst (fields p x) body
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))

private theorem decoded_values (p z R B A : PTm n) (i : Fin 5) :
    Γ ⊢[PRAAx] fields p (data z R B A) i ≐ (![p,z,R,B,A] : Fin 5 → PTm n) i := by
  fin_cases i
  · exact .eqRefl _
  · exact GaussianEulerVaryingCutoffName.data_z z R B A
  · exact GaussianEulerVaryingCutoffName.data_R z R B A
  · exact GaussianEulerVaryingCutoffName.data_B z R B A
  · exact GaussianEulerVaryingCutoffName.data_A z R B A

theorem name_at (p z R B A : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B A) ≐ sample p z R B A := by
  let x := data z R B A
  have read : Syn.subst (![p,x] : Fin 2 → PTm n) (reader (var 0) (var 1)) = reader p x := by
    unfold reader
    rw [Syn.subst_subst]
    congr 1
    funext i
    fin_cases i <;> simp [fields]
  have first : Γ ⊢[PRAAx] ap2 nameF p x ≐ reader p x := by
    simpa only [nameF,ap2,read] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,x]
  have decode : Syn.subst (![p,z,R,B,A] : Fin 5 → PTm n) body = sample p z R B A := by
    simp only [body,subst_sample,Syn.subst_var]
    rfl
  exact first.eqTrans (by simpa only [reader,decode] using Prf.eqCongr body (decoded_values p z R B A))

theorem original_Euler_observations (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B A)) (ap2 GaussianEulerImproperName.nameF q (data z R B A))
      (unit p+unit q) (unit p*unit q) := by
  let k := succ p
  let P := unit p
  let Q := unit q
  let U := unit k
  let V := unit (succ k)
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hU := unit_positive (Γ := Γ) k
  have hD := positive_product _ _ hU hQ
  have original := GaussianEulerIntegralGammaIdentification.improper_source z R B A h
  have hs := GaussianEulerPositiveScalingCutoffGeometry.cutoff_interval k A z R B original.andE₁
  have obs := GaussianEulerExponentialLogCompact.original_observations (succ k) (succ k) z R B one
    (width k A R) (etaDen k A R) (top k A R) hs
  have grow : Γ ⊢[PRAAx] V ≐ U*two := pw_succ two k
  have changed := distance_congr (.eqRefl _) (.eqRefl _) (congrAdd grow grow) (congrMul grow grow) obs
  have first := distance_radius_mono _ _ _ _ Q (U*Q)
    (positive_product _ _ (positive_product _ _ hU (le_succ_self one)) (positive_product _ _ hU (le_succ_self one))) hD
    (le_of_eq_add (d := zero) (by ipra_ring)) changed
  have tail := distance_congr (.eqRefl _) (.eqRefl _) (add_comm Q U) (mul_comm Q U)
    (distance_symmetric _ _ _ _ (positive_product _ _ hQ hU)
      (GaussianEulerLaterCutoffObservation.successor_precision_observations q k z R B A k original (le_refl k)))
  have both := distance_triangle_same _ _ _ _ _ _ hD first tail
  have twice : Γ ⊢[PRAAx] U ≐ P*two := pw_succ two p
  have bound := distance_congr (.eqRefl _) (.eqRefl _) (congrAdd (.eqRefl Q) (congrAdd twice (.eqRefl Q)))
    (congrMul twice (.eqRefl Q)) both
  exact distance_congr (name_at p z R B A).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hP (le_succ_self one)) hQ)
      (positive_product _ _ hP hQ) (le_of_eq_add (d := zero) (by ipra_ring)) bound)

theorem original_Euler_cross (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianEulerImproperName.nameF (data z R B A) (data z R B A) := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) :=
    by simpa only [Fm.shift,GaussianEulerIntegralGammaIdentification.subst_source,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEulerImproperName.subst_data,Syn.shift,sh] using
    original_Euler_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh A) hh

theorem name_regular (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx] pointCN nameF (data z R B A) :=
  cross_trans _ _ _ _ _ _ (original_Euler_cross z R B A h)
    (cross_symm _ _ _ _ (original_Euler_cross z R B A h))

theorem original_Gamma_cross (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaReciprocalInverse.gammaF (data z R B A) (GaussianGammaReciprocalInverse.gammaData z R B A) :=
  cross_trans _ _ _ _ _ _ (original_Euler_cross z R B A h)
    (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A h)

theorem actual_exponential_image_improper_is_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF GaussianGammaReciprocalInverse.gammaF
      (data (var 0) (var 1) (var 2) (var 3)) (GaussianGammaReciprocalInverse.gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_Gamma_cross _ _ _ _ Prf.hyp0))

theorem actual_exponential_image_improper_Gamma_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5)))
        (ap2 GaussianGammaReciprocalInverse.gammaF (var 1) (GaussianGammaReciprocalInverse.gammaData (var 2) (var 3) (var 4) (var 5)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (cross_at _ _ _ _ _ _ (original_Gamma_cross _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialImproper
