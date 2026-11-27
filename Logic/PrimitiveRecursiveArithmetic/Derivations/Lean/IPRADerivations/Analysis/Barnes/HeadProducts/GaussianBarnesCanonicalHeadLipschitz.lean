import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHead
import IPRADerivations.Analysis.Barnes.HeadProducts.Factors.GaussianBarnesCanonicalFactorLipschitz
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# Common-disk Lipschitz comparison of the original finite Barnes heads

Every row with index at most the final cutoff fits the same factor
radius and Lipschitz budget. The original row product estimate uses
those uniform bounds while retaining the two original normalization
clocks. A diagonal bound then gives the exact independent-observation
allowances for the resulting actual finite names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadLipschitz

open_ipra
open GaussianBarnesCanonicalHead (source body parameters factor_at nameF data regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator subst_diagonalNumerator subst_diagonalDenominator)
open GaussianNamedFiniteProduct (amplification rowBoundsAt rowDistance sample_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)
local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "Rrows" => GaussianNamedFiniteProductFamily.rowF F body
local notation "factorCap" => GaussianBarnesCanonicalFactor.cap
local notation "factorGain" => GaussianBarnesCanonicalFactorLipschitz.gain

def gain (R N r : PTm n) : PTm n := amplification (factorCap R (N+r)) r*factorGain R (N+r)
def observationCost (R N r : PTm n) : PTm n := two*amplification (factorCap R (N+r)) r

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R N r : PTm n) :
    Syn.subst σ (gain R N r) = gain (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ r) := by simp [gain]

@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (R N r : PTm n) :
    Syn.subst σ (observationCost R N r) = observationCost (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [observationCost,two]

private theorem index_bound (N i r : PTm n) (hi : Γ ⊢[PRAAx] lt i r) : Γ ⊢[PRAAx] le (succ (N+i)) (N+r) :=
  le_congr ((add_comm (succ i) N).eqTrans (add_succ N i)) (add_comm r N) (add_le_add_right N hi)

private theorem cap_mono (R i j : PTm n) (h : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] le (factorCap R i) (factorCap R j) := by
  have power := GaussianFactorBudget.power_monotone_length (R+one) i j (le_add_left one R) h
  unfold GaussianBarnesCanonicalFactor.cap
  ipra_le 𝔞(GaussianRadiusExponentialLipschitzRate.factor (GaussianBarnesCanonicalFactor.exponentRadius R))*sl power

private theorem factor_source (z R B k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source z R B k :=
  .andI h.andE₁ (.andI hk h.andE₂)

theorem row_bounds (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] rowBoundsAt Rrows p r (factorCap R (N+r)) (parameters z R B N) := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh r) :: Γ.map Fm.shift
  let k := succ (sh N+i)
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have hi : Δ ⊢[PRAAx] le k (sh N+sh r) := index_bound (sh N) i (sh r) Prf.hyp0
  have fact := GaussianBarnesCanonicalFactor.sample_bound (sh p) (sh z) (sh R) (sh B) k
    (factor_source _ _ _ _ hs (zero_lt_succ _))
  have bigger := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (mul_le_mul_right one (cap_mono (sh R) k (sh N+sh r) hi)) fact
  simpa only [rowBoundsAt,Syn.shift,sh,Δ,i,GaussianBarnesCanonicalHead.subst_parameters,
    GaussianBarnesCanonicalFactor.subst_cap,PTm.subst_add] using
    GaussianRationalReciprocal.bound_congr (factor_at (sh p) i (sh z) (sh R) (sh B) (sh N)).eqSymm
      (.eqRefl _) (.eqRefl _) bigger

theorem rows_distance (p s t z w R B D N r A K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (hK : Γ ⊢[PRAAx] le one K) (hp : Γ ⊢[PRAAx] le p s) (hq : Γ ⊢[PRAAx] le p t)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A K) :
    Γ ⊢[PRAAx] rowDistance Rrows Rrows s t r
      (diagonalNumerator (factorGain R (N+r)*A) K two p) (diagonalDenominator K p)
      (parameters z R B N) (parameters w R D N) := by
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh r) :: Γ.map Fm.shift
  let k := succ (sh N+i)
  let G := factorGain (sh R) (sh N+sh r)
  let U := unit (sh p)
  let X := unit (sh s)
  let Y := unit (sh t)
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift.wk
  have hw' : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift.wk
  have hK' : Δ ⊢[PRAAx] le one (sh K) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hK.shift.wk
  have hp' : Δ ⊢[PRAAx] le (sh p) (sh s) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hp.shift.wk
  have hq' : Δ ⊢[PRAAx] le (sh p) (sh t) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hq.shift.wk
  have dist : Δ ⊢[PRAAx] distanceBounded (ofGaussian (sh z) (sh B)) (ofGaussian (sh w) (sh D)) (sh A) (sh K) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have hi : Δ ⊢[PRAAx] le k (sh N+sh r) := index_bound (sh N) i (sh r) Prf.hyp0
  have indexGain := GaussianBarnesCanonicalFactorLipschitz.gain_mono (sh R) k (sh N+sh r) hi
  have growX : Δ ⊢[PRAAx] le U X := GaussianExponentialReference.unit_monotone hp'
  have growY : Δ ⊢[PRAAx] le U Y := GaussianExponentialReference.unit_monotone hq'
  have core := GaussianBarnesCanonicalFactorLipschitz.independent_rate (sh z) (sh w) (sh R) (sh B) (sh D) k (sh A) (sh K)
    (factor_source _ _ _ _ hz' (zero_lt_succ _)) (factor_source _ _ _ _ hw' (zero_lt_succ _)) hK' dist
  have obs := rate_at F F _ _ (factorGain (sh R) k*sh A) (sh K) (sh s) (sh t) core
  have widened : Δ ⊢[PRAAx] distanceBounded
      (ap2 F (sh s) (GaussianBarnesCanonicalFactor.data (sh z) (sh R) (sh B) k))
      (ap2 F (sh t) (GaussianBarnesCanonicalFactor.data (sh w) (sh R) (sh D) k))
      (diagonalNumerator (G*sh A) (sh K) two (sh p)) (diagonalDenominator (sh K) (sh p)) := by
    apply distance_radius_mono _ _ _ _ _ _ (denominator_positive (sh K) (sh s) (sh t) hK')
      (positive_product _ _ hK' (unit_positive (sh p))) _ obs
    change Δ ⊢[PRAAx] le
      (((factorGain (sh R) k*sh A)*X*Y+sh K*(X+Y))*(sh K*U))
      (((G*sh A)*U+two*sh K)*(sh K*X*Y))
    ipra_le 𝔞(sh A*X*Y*sh K*U)*sl indexGain+𝔞(sh K*sh K*Y)*sl growX+𝔞(sh K*sh K*X)*sl growY
  simpa only [rowDistance,Syn.shift,sh,Δ,i,G,GaussianBarnesCanonicalHead.subst_parameters,
    GaussianBarnesCanonicalFactorLipschitz.subst_gain,subst_diagonalNumerator,subst_diagonalDenominator,
    PTm.subst_add,PTm.subst_mul,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      distance_congr (factor_at (sh s) i (sh z) (sh R) (sh B) (sh N)).eqSymm
        (factor_at (sh t) i (sh w) (sh R) (sh D) (sh N)).eqSymm (.eqRefl _) (.eqRefl _) widened

theorem diagonal (p z w R B D N r A K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B N r)) (ap2 nameF p (data w R D N r))
      (diagonalNumerator (gain R N r*A) K (observationCost R N r) p) (diagonalDenominator K p) := by
  let left := parameters z R B N
  let right := parameters w R D N
  let C := factorCap R (N+r)
  let L := GaussianNamedFiniteProductFamily.radius F body r left
  let M := GaussianNamedFiniteProductFamily.radius F body r right
  let s := GaussianNamedFiniteProductName.clock r L one p
  let t := GaussianNamedFiniteProductName.clock r M one p
  have hp : Γ ⊢[PRAAx] le p s := GaussianNamedFiniteProductName.clock_later r L one p
  have hq : Γ ⊢[PRAAx] le p t := GaussianNamedFiniteProductName.clock_later r M one p
  have b₁ := row_bounds s z R B N r hz
  have b₂ := row_bounds t w R D N r hw
  have read := rows_distance p s t z w R B D N r A K hz hw hK hp hq h
  have raw := sample_distance Rrows Rrows s t r C _ (diagonalDenominator K p) left right
    (positive_product _ _ hK (unit_positive p)) b₁ b₂ read
  exact distance_congr (GaussianBarnesCanonicalHead.sample_at p z R B N r).eqSymm
    (GaussianBarnesCanonicalHead.sample_at p w R D N r).eqSymm
    (by dsimp only [gain,observationCost,diagonalNumerator,C]; ipra_ring) (.eqRefl _) raw

theorem independent_rate (z w R B D N r A K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A K) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B N r) (data w R D N r) (gain R N r*A) K := by
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF _ _ _ _ (observationCost R N r) hK
    (regular z R B N r hz) (regular w R D N r hw)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
  have ht : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift
  have hk : Δ ⊢[PRAAx] le one (sh K) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hK.shift
  have hd : Δ ⊢[PRAAx] distanceBounded (ofGaussian (sh z) (sh B)) (ofGaussian (sh w) (sh D)) (sh A) (sh K) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  simpa only [diagonalEnvelope,Syn.shift,sh,Δ,GaussianBarnesCanonicalHead.subst_data,subst_diagonalNumerator,
    subst_diagonalDenominator,subst_gain,subst_observationCost,PTm.subst_mul] using
    diagonal (var 0) (sh z) (sh w) (sh R) (sh B) (sh D) (sh N) (sh r) (sh A) (sh K) hs ht hk hd

theorem actual_Barnes_finite_head_common_disk_lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 0) (var 2) (var 3) ⟶ source (var 1) (var 2) (var 4) ⟶
        le one (var 8) ⟶ distanceBounded (ofGaussian (var 0) (var 3)) (ofGaussian (var 1) (var 4)) (var 7) (var 8) ⟶
        independentRate nameF nameF (data (var 0) (var 2) (var 3) (var 5) (var 6)) (data (var 1) (var 2) (var 4) (var 5) (var 6))
          (gain (var 2) (var 5) (var 6)*var 7) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (independent_rate _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadLipschitz
