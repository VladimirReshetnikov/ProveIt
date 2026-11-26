import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Exponential.GaussianExponentialReference
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent

/-!
# Independent rates for the original named sum

Adding rates A/B and C/E preserves their sum as the leading error.
Each original fast addition query pays for two input observations,
so the resulting rate keeps one dyadic error per output observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedAddRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianExponentialReference (add_sample)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (addF addData sum_distance)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

export GaussianNamedDifferenceRate (self_rate)
export GaussianNamedRateComposition (leadingNumerator leadingDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def input (F G H K : PR 2) (x y u v A B C E : PTm n) : Fm PTm n :=
  (le one B ⋏ le one E) ⋏ (independentRate F H x u A B ⋏ independentRate G K y v C E)

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F G H K : PR 2) (x y u v A B C E : PTm n) :
    (input F G H K x y u v A B C E).subst σ = input F G H K (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ E) := by
  simp [input]

theorem independent_at (F G H K : PR 2) (x y u v A B C E p q : PTm n)
    (h : Γ ⊢[PRAAx] input F G H K x y u v A B C E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (addF F G) p (addData x y)) (ap2 (addF H K) q (addData u v))
      (rateNumerator (leadingNumerator A B C E) (leadingDenominator B E) p q)
      (rateDenominator (leadingDenominator B E) p q) := by
  let r := exponent two p
  let s := exponent two q
  let V := leadingDenominator B E
  let D := rateDenominator V r s
  have hB := h.andE₁.andE₁
  have hE := h.andE₁.andE₂
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ hB hE
  have hD := denominator_positive V r s hV
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 F r x) (ap2 H s u) (rateNumerator A B r s*E) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive B r s hB) hD
      (le_of_eq_add (d := zero) (by dsimp only [D, V, rateDenominator, leadingDenominator]; ipra_ring))
      (rate_at F H x u A B r s h.andE₂.andE₁)
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 G r y) (ap2 K s v) (rateNumerator C E r s*B) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive E r s hE) hD
      (le_of_eq_add (d := zero) (by dsimp only [D, V, rateDenominator, leadingDenominator]; ipra_ring))
      (rate_at G K y v C E r s h.andE₂.andE₂)
  have both := sum_distance _ _ _ _ _ _ _ hD first second
  have original := distance_congr (add_sample F G x y p).eqSymm (add_sample H K u v q).eqSymm
    (.eqRefl _) (.eqRefl _) both
  apply distance_radius_mono _ _ _ _ _ _ hD (denominator_positive V p q hV) ?_ original
  dsimp only [D, V, rateNumerator, rateDenominator, leadingNumerator, leadingDenominator]
  ipra_le (𝔞 B*𝔞 E)^2*𝔞 (unit s)*𝔞 (unit q)*sl (query_budget two p) +
    (𝔞 B*𝔞 E)^2*𝔞 (unit r)*𝔞 (unit p)*sl (query_budget two q)

theorem rate_of_input (F G H K : PR 2) (x y u v A B C E : PTm n)
    (h : Γ ⊢[PRAAx] input F G H K x y u v A B C E) :
    Γ ⊢[PRAAx] independentRate (addF F G) (addF H K) (addData x y) (addData u v)
      (leadingNumerator A B C E) (leadingDenominator B E) := by
  let sh (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] input F G H K (sh x) (sh y) (sh u) (sh v) (sh A) (sh B) (sh C) (sh E) := by
    simpa only [Δ, Fm.shift, subst_input, Syn.shift, sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate, Syn.shift, GaussianNameArithmetic.subst_addData,
    GaussianNamedRateComposition.subst_leadingNumerator, GaussianNamedRateComposition.subst_leadingDenominator, sh] using
    independent_at F G H K (sh x) (sh y) (sh u) (sh v) (sh A) (sh B) (sh C) (sh E) (var 1) (var 0) hs

theorem independent_rate (F G H K : PR 2) (x y u v A B C E : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hFH : Γ ⊢[PRAAx] independentRate F H x u A B) (hGK : Γ ⊢[PRAAx] independentRate G K y v C E) :
    Γ ⊢[PRAAx] independentRate (addF F G) (addF H K) (addData x y) (addData u v)
      (leadingNumerator A B C E) (leadingDenominator B E) :=
  rate_of_input F G H K x y u v A B C E (.andI (.andI hB hE) (.andI hFH hGK))

theorem constant_rate (x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded x y A D) : Γ ⊢[PRAAx] independentRate constantF constantF x y A D := by
  let sh (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have ds : Δ ⊢[PRAAx] le one (sh D) := by
    simpa [Δ, Fm.shift, Syn.shift, sh] using hD.shift.shift
  have hs : Δ ⊢[PRAAx] distanceBounded (sh x) (sh y) (sh A) (sh D) := by
    simpa only [Δ, Fm.shift, GaussianRationalMetric.subst_distanceBounded, Syn.shift, sh] using h.shift.shift
  have obs : Δ ⊢[PRAAx] distanceBounded (ap2 constantF p (sh x)) (ap2 constantF q (sh y))
      (rateNumerator (sh A) (sh D) p q) (rateDenominator (sh D) p q) := by
    refine distance_congr (constant_at p (sh x)).eqSymm (constant_at q (sh y)).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ _ _ _ _ ds (denominator_positive (sh D) p q ds) ?_ hs)
    apply le_of_eq_add (d := sh D*sh D*(unit p+unit q))
    unfold rateNumerator rateDenominator
    ipra_ring
  refine .allI (.allI ?_)
  simpa only [independentRate, Syn.shift, sh, p, q] using obs

theorem actual_normalized_sum_independent_rate_closed (F G H K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (input F G H K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        independentRate (addF F G) (addF H K) (addData (var 0) (var 1)) (addData (var 2) (var 3))
          (leadingNumerator (var 4) (var 5) (var 6) (var 7)) (leadingDenominator (var 5) (var 7))) :=
  closeUniv 8 (.impI (rate_of_input F G H K _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_named_constant_independent_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 3) ⋏ distanceBounded (var 0) (var 1) (var 2) (var 3)) ⟶
        independentRate constantF constantF (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (constant_rate _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedAddRate
