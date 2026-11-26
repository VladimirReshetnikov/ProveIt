import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorGridObservations
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorEvenGridLimit
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence

/-!
# The quadratic rate of the actual cofinal Barnes even grid

One literal partial product serves every row of both cofinal grids.
The disk-uniform coefficient cutoff and the two observation thresholds
charge the remaining errors to the squared displacement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorEvenGridLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded bounded_neg bounded_mono normSq)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinalGrid tailCutoff amplification deadline row_bound)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid)
open GaussianBarnesCanonicalFiniteTaylorEvenGridLimit (quadraticClock)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor stepDivisor_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (query_budget)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble even_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_as_product naturalPoint)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "gd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "finiteObserved" => GaussianBarnesCanonicalFiniteTaylorEvenGridComparison.observed
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def observed (t z h R B e : PTm n) : PTm n :=
  observedDouble (cofinalGrid t z h R B e) (cofinalGrid t z (ComplexLogarithmRemainder.neg h) R B e) e (ofGaussian h B)

@[simp] theorem subst_observed {m : ℕ} (σ : Fin n → PTm m) (t z h R B e : PTm n) :
    Syn.subst σ (observed t z h R B e) =
      observed (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ e) :=
  by simp [observed]

def observationClock (B e : PTm n) : PTm n := deadline (quadraticClock B) B e

def cutoff (R B J e : PTm n) : PTm n :=
  tailCutoff (observationClock B e) R+
    GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff (quadraticClock B) (R+one) J e

def literalClock (z h R B M J e : PTm n) : PTm n :=
  observationClock B e+
    GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.observationClock (quadraticClock B) z h R B (cutoff R B J e) M e

def uniformGain (R M e : PTm n) : PTm n := GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.uniformGain R M e+num 8

theorem grid_comparison (p t s z h R B H r e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le (e*H) B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hr : Γ ⊢[PRAAx] le (tailCutoff (deadline p B e) R) r)
    (ht : Γ ⊢[PRAAx] le (deadline p B e) t) (hs : Γ ⊢[PRAAx] le (deadline p B e) s) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B e) (finiteObserved s z h R B r e) two (unit p) := by
  let k := deadline p B e
  let Q := unit k
  let T := unit t
  let S := unit s
  let U := unit p
  let C := amplification B e
  let A := rateNumerator one Q t s
  let N := rateDenominator Q t s
  have tq : Γ ⊢[PRAAx] le Q T := unit_monotone ht
  have sq : Γ ⊢[PRAAx] le Q S := unit_monotone hs
  have paid : Γ ⊢[PRAAx] le (num 3*C*U) Q := query_budget _ _
  have hB := hz.andE₁
  have hN : Γ ⊢[PRAAx] le one N := GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive k)
  have sep : Γ ⊢[PRAAx] lower (ofGaussian h B) one B :=
    GaussianNamedDifferenceQuotient.parameter_lower h B (.andI hB hn)
  have raw := even_error (cofinalGrid t z h R B e) (cofinalGrid t z (ComplexLogarithmRemainder.neg h) R B e)
    (literalGrid s z h R B r e) (literalGrid s z (ComplexLogarithmRemainder.neg h) R B r e)
    e (ofGaussian h B) one B A A N (le_refl one) hB sep hN
    (row_bound t s k z h R B H r e hz hh hsmall hr)
    (row_bound t s k z (ComplexLogarithmRemainder.neg h) R B H r e hz (bounded_neg hh) hsmall hr)
  have exactRaw : Γ ⊢[PRAAx] distanceBounded (observed t z h R B e) (finiteObserved s z h R B r e)
      (pw B e*(pw two e*(A+A))) N :=
    distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
      ((congrMul (GaussianPolynomialPerturbation.one_power e) (.eqRefl N)).eqTrans (one_mul N)) raw
  have cmp : Γ ⊢[PRAAx] le ((pw B e*(pw two e*(A+A)))*U) (two*N) := by
    change Γ ⊢[PRAAx] le
      ((pw B e*(pw two e*((one*T*S+Q*(T+S))+(one*T*S+Q*(T+S)))))*U) (two*(Q*T*S))
    ipra_le 2*𝔞(T)*𝔞(S)*sl paid+2*𝔞(C)*𝔞(U)*𝔞(T)*sl sq+2*𝔞(C)*𝔞(U)*𝔞(S)*sl tq using
      dsimp only [C,amplification]
      ipra_simps
      ring
  exact distance_radius_mono _ _ _ _ _ _ hN (unit_positive p) cmp exactRaw

private theorem coefficient_comparison (k u z R B r J e : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B)
    (he : Γ ⊢[PRAAx] le e (previous J))
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff k (R+one) J e) r)
    (hu : Γ ⊢[PRAAx] le k u) :
    Γ ⊢[PRAAx] distanceBounded (natScale two (ap2 F k (fd z (R+one) B r J e)))
      (natScale two (ap2 G u (gd z (R+one) B J e))) (num 6) (unit k) := by
  let f := ap2 F k (fd z (R+one) B r J e)
  let g := ap2 G u (gd z (R+one) B J e)
  let Q := unit k
  let V := unit u
  let A := rateNumerator one Q u k
  let N := rateDenominator Q u k
  have hv : Γ ⊢[PRAAx] le Q V := unit_monotone hu
  have hq := unit_positive (Γ := Γ) k
  have hN : Γ ⊢[PRAAx] le one N := GaussianNamedInverseRate.denominator_positive _ _ _ hq
  have near : Γ ⊢[PRAAx] distanceBounded g f A N :=
    rate_at G F (gd z (R+one) B J e) (fd z (R+one) B r J e) one Q u k
      (GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate k z (R+one) B r J e hz he hr)
  have cmp : Γ ⊢[PRAAx] le (A*Q) (num 3*N) := by
    change Γ ⊢[PRAAx] le ((one*V*Q+Q*(V+Q))*Q) (num 3*(Q*V*Q))
    ipra_le (𝔞(Q)*𝔞(Q))*sl hv
  have close := distance_symmetric _ _ _ _ hq (distance_radius_mono _ _ _ _ _ _ hN hq cmp near)
  have double := GaussianNamedDifferenceQuotient.scale_distance (naturalPoint two) f g two (num 3) Q hq
    (GaussianNamedNaturalScale.natural_point_bound two) close
  exact distance_congr (natScale_as_product two f).eqSymm (natScale_as_product two g).eqSymm
    (by ipra_ring) (.eqRefl _) double

private theorem charge_clock (B H Q C : PTm n) (hQ : Γ ⊢[PRAAx] le (B*B) Q)
    (hH : Γ ⊢[PRAAx] le one (H*H)) :
    Γ ⊢[PRAAx] le (C*(B*B)) ((C*(H*H))*Q) := by
  ipra_le 𝔞(C)*sl hQ+𝔞(C)*𝔞(Q)*sl hH

theorem uniform_rate (z h R B M J e t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock B e) t) (hu : Γ ⊢[PRAAx] le (quadraticClock B) u) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B e) (natScale two (ap2 G u (gd z (R+one) B J e)))
      (uniformGain R M e*(norm1 h*norm1 h)) (B*B) := by
  let k := quadraticClock B
  let H := norm1 h
  let r := cutoff R B J e
  let s := literalClock z h R B M J e
  let O := observationClock B e
  let A := tailCutoff O R
  let C := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff k (R+one) J e
  let T := GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.observationClock k z h R B r M e
  let K := GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.uniformGain R M e
  let Q := unit k
  let x := observed t z h R B e
  let y := finiteObserved s z h R B r e
  let f := natScale two (ap2 F k (fd z (R+one) B r J e))
  let g := natScale two (ap2 G u (gd z (R+one) B J e))
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hHH := positive_product H H hH hH
  have hB := hz.andE₁
  have hBB := positive_product B B hB hB
  have hQ := unit_positive (Γ := Γ) k
  have fit : Γ ⊢[PRAAx] (B*B)*unit zero ≐ B*B :=
    (congrMul (.eqRefl _) (pw_zero two)).eqTrans (by ipra_ring)
  have paid : Γ ⊢[PRAAx] le (B*B) Q := le_congr fit (.eqRefl _) (query_budget (B*B) zero)
  have admitted : Γ ⊢[PRAAx] le (e*H) B := by
    have e' : Γ ⊢[PRAAx] le e (e*stepDivisor R) :=
      le_congr (one_mul e) (mul_comm _ _) (mul_le_mul_right e (stepDivisor_positive R))
    exact le_trans (mul_le_mul_right H e') hsmall
  have disk : Γ ⊢[PRAAx] source z (R+one) B :=
    .andI hB (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))
  have near : Γ ⊢[PRAAx] distanceBounded x y two Q :=
    grid_comparison k t s z h R B H r e hz (normSq_le_norm1_square h) admitted hn (le_add_right A C) ht (le_add_right O T)
  have finite : Γ ⊢[PRAAx] distanceBounded y f (K*(H*H)) (B*B) :=
    GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.uniform_rate z h R B r M J e s k hz hn hsmall hdeg hJ
      (le_add_left T O) (le_refl k)
  have final : Γ ⊢[PRAAx] distanceBounded f g (num 6) Q :=
    coefficient_comparison k u z R B r J e disk hJ (le_add_left C A) hu
  have first : Γ ⊢[PRAAx] distanceBounded x y (two*(H*H)) (B*B) :=
    distance_radius_mono _ _ _ _ _ _ hQ hBB (charge_clock B H Q two paid hHH) near
  have last : Γ ⊢[PRAAx] distanceBounded f g (num 6*(H*H)) (B*B) :=
    distance_radius_mono _ _ _ _ _ _ hQ hBB (charge_clock B H Q (num 6) paid hHH) final
  have total : Γ ⊢[PRAAx] (two*(H*H)+K*(H*H)+(num 6)*(H*H)) ≐ ((K+num 8)*(H*H)) := by ipra_ring
  exact distance_congr (.eqRefl _) (.eqRefl _) total (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hBB (distance_triangle_same _ _ _ _ _ _ hBB first finite) last)

theorem actual_Barnes_cofinal_even_grid_uniform_quadratic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let M := var 4
     let J := var 5
     let e := var 6
     let t := var 7
     let u := var 8
     (source z R B ⋏ (le one (normSq h) ⋏ (previous M ≐ succ e ⋏ le e (previous J)))) ⟶
       (le ((e*stepDivisor R)*norm1 h) B ⋏ (le (observationClock B e) t ⋏ le (quadraticClock B) u)) ⟶
       distanceBounded (observed t z h R B e) (natScale two (ap2 G u (gd z (R+one) B J e)))
         (uniformGain R M e*(norm1 h*norm1 h)) (B*B)) :=
  closeUniv 9 (.impI (.impI (uniform_rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp0.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorEvenGridLimit
