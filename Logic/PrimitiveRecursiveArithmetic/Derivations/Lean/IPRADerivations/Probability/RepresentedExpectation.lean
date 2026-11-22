import IPRADerivations.Probability.ConditionalAveraging
import IPRADerivations.Foundations.FiniteObservations.MetricKernel

/-!
# The finite inequalities behind the represented expectation

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, Theorem "Represented
expectation" ("Apply the exact finite inequality `|I(x_k) − I(x_l)| ≤ d₁(x_k, x_l)`") and the remarks before it
on bounded Lipschitz test functions and effective tightness, for finite tables of natural terms with natural
row weights `W_j` (the expectation `I x = ∑_j W_j x_j`, cleared of the common denominator):

* `exp_contract`: `|I x − I y| ≤ I |x − y|`;
* `exp_name`: if `I |x_k − x_l| ≤ ε_k + ε_l` (a regular `L¹` name), then `|I x_k − I x_l| ≤ ε_k + ε_l`, so
  `I x_k` is a regular rational name; equivalent names (`I |x_k − y_k| ≤ ε_k`) give `|I x_k − I y_k| ≤ ε_k`;
* `lipschitz_pt`, `lipschitz_test` ("if `|h| ≤ M` and `h` has Lipschitz constant `L`, then
  `I(|h(f) − h(g)|) ≤ max(L, 2M) d₀(f, g)`. Indeed, for `|f − g| ≤ 1` use Lipschitz continuity; otherwise use
  the bound `2M`"), with `d₀` the capped distance `I min(1, |f − g|)` and any `K ≥ L`, `K ≥ 2M`;
* `tail_pt` (effective tightness, "`P(|x_s| > B + 1) ≤ d₀(x_s, x_r)`" pointwise): if `x_r ≤ B` and
  `x_s ≥ B + 2`, then `min(1, |x_s − x_r|) = 1`.
-/

namespace LeanProofs.IPRA.Probability.RepresentedExpectation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.ErrorBudget (nsum toG_nsum)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_mul ad_le_of)
open LeanProofs.IPRA.Probability.ConditionalAveraging (nsum_mono ad_nsum_le)
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n m : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The cleared expectation `I x = ∑_j W_j x_j`. -/
def I (W x : Fin m → PTm n) : PTm n := nsum fun j => W j * x j

/-- `|I x − I y| ≤ I |x − y|`. -/
theorem exp_contract (W x y : Fin m → PTm n) :
    Γ ⊢[PRAAx] le (ad (I W x) (I W y)) (I W fun j => ad (x j) (y j)) :=
  le_trans (ad_nsum_le _ _) (nsum_mono fun j => le_congr (.eqRefl _) (ad_mul _ _ _) (le_refl _))

/-- A regular `L¹` name gives a regular scalar name. -/
theorem exp_name (W : Fin m → PTm n) {x y : Fin m → PTm n} {e : PTm n}
    (h : Γ ⊢[PRAAx] le (I W fun j => ad (x j) (y j)) e) : Γ ⊢[PRAAx] le (ad (I W x) (I W y)) e :=
  le_trans (exp_contract W x y) h

theorem ad_le_add (a b : PTm n) : Γ ⊢[PRAAx] le (ad a b) (a + b) :=
  ad_le_of (by ipra_le 2 * 𝔟 b) (by ipra_le 2 * 𝔟 a)

/-- A bounded Lipschitz test function: `|h a − h b| ≤ K min(1, |a − b|)` for `K ≥ L`, `K ≥ 2M`. -/
theorem lipschitz_pt {ha hb a b L M K : PTm n} (hL : Γ ⊢[PRAAx] le (ad ha hb) (L * ad a b))
    (hMa : Γ ⊢[PRAAx] le ha M) (hMb : Γ ⊢[PRAAx] le hb M) (hK₁ : Γ ⊢[PRAAx] le L K)
    (hK₂ : Γ ⊢[PRAAx] le (two * M) K) :
    Γ ⊢[PRAAx] le (ad ha hb) (K * meet one (ad a b)) := by
  refine .orE (le_total one (ad a b)) ?_ ?_
  · have e : (le one (ad a b) :: Γ) ⊢[PRAAx] meet one (ad a b) ≐ one := meet_left Prf.hyp0
    have s := ad_le_add (Γ := le one (ad a b) :: Γ) ha hb
    have h1 := hMa.wk (ψ := le one (ad a b))
    have h2 := hMb.wk (ψ := le one (ad a b))
    have h3 := hK₂.wk (ψ := le one (ad a b))
    have g : (le one (ad a b) :: Γ) ⊢[PRAAx] le (ad ha hb) (K * one) := by
      ipra_le sl s + sl h1 + sl h2 + sl h3
    exact le_congr (.eqRefl _) (congrMul (.eqRefl _) e.eqSymm) g
  · have e : (le (ad a b) one :: Γ) ⊢[PRAAx] meet one (ad a b) ≐ ad a b := meet_right Prf.hyp0
    have h0 := hL.wk (ψ := le (ad a b) one)
    have h1 := hK₁.wk (ψ := le (ad a b) one)
    have g : (le (ad a b) one :: Γ) ⊢[PRAAx] le (ad ha hb) (K * ad a b) := by
      ipra_le sl h0 + (𝔟 (monus a b) + 𝔟 (monus b a)) * sl h1
    exact le_congr (.eqRefl _) (congrMul (.eqRefl _) e.eqSymm) g

/-- `I(|h(f) − h(g)|) ≤ K d₀(f, g)` with `d₀(f, g) = I min(1, |f − g|)`. -/
theorem lipschitz_test (W f g : Fin m → PTm n) (h : PTm n → PTm n) {L M K : PTm n}
    (hL : ∀ j, Γ ⊢[PRAAx] le (ad (h (f j)) (h (g j))) (L * ad (f j) (g j)))
    (hM : ∀ a, Γ ⊢[PRAAx] le (h a) M) (hK₁ : Γ ⊢[PRAAx] le L K) (hK₂ : Γ ⊢[PRAAx] le (two * M) K) :
    Γ ⊢[PRAAx] le (I W fun j => ad (h (f j)) (h (g j))) (K * I W fun j => meet one (ad (f j) (g j))) := by
  have p : ∀ j, Γ ⊢[PRAAx] le (W j * ad (h (f j)) (h (g j))) (W j * (K * meet one (ad (f j) (g j)))) :=
    fun j => by
      have q := lipschitz_pt (hL j) (hM (f j)) (hM (g j)) hK₁ hK₂
      ipra_le 𝔟 (W j) * sl q
  have s := nsum_mono p
  have e : Γ ⊢[PRAAx] (nsum fun j => W j * (K * meet one (ad (f j) (g j)))) ≐
      K * nsum fun j => W j * meet one (ad (f j) (g j)) := by
    apply deriveNat
    simp only [toG_nsum, Q.mk_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact le_congr (.eqRefl _) e s

/-- Effective tightness, pointwise: `x_r ≤ B` and `x_s ≥ B + 2` give `min(1, |x_s − x_r|) = 1`. -/
theorem tail_pt {xs xr B : PTm n} (hr : Γ ⊢[PRAAx] le xr B) (hs : Γ ⊢[PRAAx] le (succ (succ B)) xs) :
    Γ ⊢[PRAAx] meet one (ad xs xr) ≐ one := by
  refine meet_left ?_
  have hm : Γ ⊢[PRAAx] le (succ xr) xs := le_trans (by ipra_le sl hr + 1) hs
  have hle : Γ ⊢[PRAAx] le xr xs := le_trans (by ipra_le 1) hm
  have e := natEq (eq_add_of_le hle)
  show Γ ⊢[PRAAx] le one (monus xs xr + monus xr xs)
  ipra_le sl hm + 𝔟 (monus xr xs) with (-1) * e

end LeanProofs.IPRA.Probability.RepresentedExpectation
