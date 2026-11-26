import IPRADerivations.Analysis.Exponential.GaussianRadiusExponentialLipschitzRate
import IPRADerivations.Analysis.Exponential.GaussianNamedRadiusExponentialFreeze
import IPRADerivations.Analysis.Exponential.GaussianSignedNameExponentialOrder

/-!
# Preserve an exponential rate with a supplied constant comparison

A constant rational bound and an upper bound on the leading error
give one common radius for every original input observation. The
exponential rate remains valid at the two original evaluation radii.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedExponentialRateFromConstant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameBounds (U)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "input" => GaussianRadiusExponentialName.input
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def cap (M K : PTm n) : PTm n := M+K+two

@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (M K : PTm n) :
    Syn.subst σ (cap M K) = cap (Syn.subst σ M) (Syn.subst σ K) := by simp [cap,two]

theorem sample_bound (f : PR 2) (p x v M A D K : PTm n) (hv : Γ ⊢[PRAAx] bounded v M one)
    (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le A (K*D))
    (hr : Γ ⊢[PRAAx] independentRate f C x v A D) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) (cap M K) one := by
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have hdu := positive_product D u hd hu
  have h := diagonal_rate f C x v A D p hd hr
  have e : Γ ⊢[PRAAx] le ((A*u+two*D)*one) ((K+two)*(D*u)) := by
    ipra_le 𝔞(u)*sl hk+2*𝔞(D)*sl hu
  have dist := distance_radius_mono _ _ _ _ _ _ hdu (le_refl one) e h
  have v' := bound_congr (constant_at p v).eqSymm (.eqRefl M) (.eqRefl one) hv
  exact bound_congr (.eqRefl _) (by unfold cap; ipra_ring) (one_mul one)
    (norm_from_distance (ap2 f p x) (ap2 C p v) (K+two) one M one (le_refl one) (le_refl one) dist v')

theorem common_input (f : PR 2) (x v M A D K : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hv : Γ ⊢[PRAAx] bounded v M one) (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le A (K*D))
    (hr : Γ ⊢[PRAAx] independentRate f C x v A D) : Γ ⊢[PRAAx] input f (cap M K) x := by
  refine .andI hf (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have vs : Δ ⊢[PRAAx] bounded (sh v) (sh M) one := by simpa [Fm.shift,Syn.shift,sh,Δ] using hv.shift
  have ds : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hd.shift
  have ks : Δ ⊢[PRAAx] le (sh A) (sh K*sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hk.shift
  have rs : Δ ⊢[PRAAx] independentRate f C (sh x) (sh v) (sh A) (sh D) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hr.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,sh,Δ,subst_cap] using
    sample_bound f (var 0) (sh x) (sh v) (sh M) (sh A) (sh D) (sh K) vs ds ks rs

theorem rate (f : PR 2) (x v M A D K : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hv : Γ ⊢[PRAAx] bounded v M one) (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le A (K*D))
    (hr : Γ ⊢[PRAAx] independentRate f C x v A D) :
    Γ ⊢[PRAAx] independentRate (E f) (E C) (exponentialInputData f x) (ed M v) (factor (cap M K)*A) D := by
  let R := cap M K
  have fi := common_input f x v M A D K hf hv hd hk hr
  have v0 := GaussianSignedNameExponentialOrder.constant_input v M hv
  have hM : Γ ⊢[PRAAx] le M R := le_trans (le_add_right M K) (le_add_right (M+K) two)
  have vi := GaussianExponentialRadiusIndependence.input_widen C M R v v0 hM
  have dataRate := GaussianRadiusExponentialLipschitzRate.independent_rate f C R x v A D
    (.andI hd (.andI fi (.andI vi hr)))
  have f0 := exponential_input f x hf
  have left := GaussianExponentialRadiusIndependence.same_input_cross f (U f x) R x f0 fi
  have right := GaussianExponentialRadiusIndependence.same_input_cross C M R v v0 vi
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hd dataRate left right

theorem actual_named_exponential_rate_from_constant_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let x := var 0
     let v := var 1
     let M := var 2
     let A := var 3
     let D := var 4
     let K := var 5
     pointCN f x ⟶ bounded v M one ⟶ le one D ⟶ le A (K*D) ⟶ independentRate f C x v A D ⟶
       independentRate (E f) (E C) (exponentialInputData f x) (ed M v) (factor (cap M K)*A) D) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (rate f _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianNamedExponentialRateFromConstant
