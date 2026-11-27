import IPRADerivations.Topology.KuhnSimplices
import IPRADerivations.Core.Gcd

/-!
# Digit codes for packed lists

Framework (packet `topology/dimension_invariance_ipra`, `thm:alternative`; reusable wherever a
bounded search ranges over the points of a grid): a list of `k` entries below `P` is coded by the
number `Σ_q x_q P^q` and decoded by its base-`P` digits, so a least-witness search over the numbers
`< P^k` (`Core/Search`) is a search over the points of `{0, …, P − 1}^k`.

* `pwr k P = P^k`, `enc k P x = x_0 + P (x_1 + P (⋯))`, `dec k P c b` the list of the first `k`
  base-`P` digits of `c` over the base `b`, `quoK k P c = ⌊c / P^k⌋`;
* `dec_enc`: `dec k P (enc k P x + P^k w) b = canon k b x` when every entry `x_q < P`;
* `quoK_enc`: `⌊(enc k P x + P^k w) / P^k⌋ = w`;
* `enc_lt`: `enc k P x < P^k`; `pair_lt`: `enc u + K enc v < K K` for `enc u, enc v < K`;
* `dec_le`: the digits are `≤ P − 1`.
-/

namespace LeanProofs.IPRA.Foundations.DigitCodes

open_ipra exports
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Topology.KuhnSimplices

set_option autoImplicit false

variable {n : ℕ}

/-- `P^k` as a product. -/
def pwr : ℕ → PTm n → PTm n
  | 0, _ => one
  | k + 1, P => P * pwr k P

/-- `x_0 + P (x_1 + P (⋯ x_{k−1}))`. -/
def enc : ℕ → PTm n → PTm n → PTm n
  | 0, _, _ => zero
  | k + 1, P, x => fstT x + P * enc k P (sndT x)

/-- The first `k` base-`P` digits of `c`, packed over `b`. -/
def dec : ℕ → PTm n → PTm n → PTm n → PTm n
  | 0, _, _, b => b
  | k + 1, P, c, b => pairT (rem c P) (dec k P (quo c P) b)

/-- `⌊c / P^k⌋`. -/
def quoK : ℕ → PTm n → PTm n → PTm n
  | 0, _, c => c
  | k + 1, P, c => quoK k P (quo c P)

@[simp] theorem subst_pwr {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (k : ℕ) (P : PTm n), Syn.subst σ (pwr k P) = pwr k (Syn.subst σ P)
  | 0, _ => by simp [pwr]
  | k + 1, P => by simp [pwr, subst_pwr σ k]

@[simp] theorem subst_enc {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (k : ℕ) (P x : PTm n), Syn.subst σ (enc k P x) = enc k (Syn.subst σ P) (Syn.subst σ x)
  | 0, _, _ => by simp [enc]
  | k + 1, P, x => by simp [enc, subst_enc σ k]

@[simp] theorem subst_dec {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (k : ℕ) (P c b : PTm n), Syn.subst σ (dec k P c b) = dec k (Syn.subst σ P) (Syn.subst σ c) (Syn.subst σ b)
  | 0, _, _, _ => rfl
  | k + 1, P, c, b => by simp [dec, subst_dec σ k, subst_ap2]

@[simp] theorem subst_quoK {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (k : ℕ) (P c : PTm n), Syn.subst σ (quoK k P c) = quoK k (Syn.subst σ P) (Syn.subst σ c)
  | 0, _, _ => rfl
  | k + 1, P, c => by simp [quoK, subst_quoK σ k, subst_ap2]

variable {Γ : List (Fm PTm n)}

/-- One digit: `⌊(a + P y)/P⌋ = y` and `(a + P y) mod P = a` for `a < P`. -/
theorem digit {P cP a y : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ cP) (ha : Γ ⊢[PRAAx] lt a P) :
    Γ ⊢[PRAAx] (quo (a + P * y) P ≐ y) ⋏ (rem (a + P * y) P ≐ a) := by
  have hz : Γ ⊢[PRAAx] a + P * y ≐ succ cP * y + a :=
    (add_comm _ _).eqTrans (congrAdd (congrMul hP (.eqRefl _)) (.eqRefl _))
  have u := div_mod_unique hz (lt_congr (.eqRefl _) hP ha)
  exact .andI ((congrAp2 quoF (.eqRefl _) hP).eqTrans (Prf.andE₁ u))
    ((congrAp2 remF (.eqRefl _) hP).eqTrans (Prf.andE₂ u))

theorem enc_step (k : ℕ) (P x w : PTm n) :
    Γ ⊢[PRAAx] enc (k + 1) P x + pwr (k + 1) P * w ≐ fstT x + P * (enc k P (sndT x) + pwr k P * w) := by
  ipra_lc [enc, pwr]

theorem congrDec (k : ℕ) (P : PTm n) {c c' : PTm n} (b : PTm n) (h : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] dec k P c b ≐ dec k P c' b := by
  induction k generalizing c c' with
  | zero => exact .eqRefl _
  | succ k ih => exact congrPairT (congrAp2 remF h (.eqRefl _)) (ih (congrAp2 quoF h (.eqRefl _)))

theorem congrQuoK (k : ℕ) (P : PTm n) {c c' : PTm n} (h : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] quoK k P c ≐ quoK k P c' := by
  induction k generalizing c c' with
  | zero => exact h
  | succ k ih => exact ih (congrAp2 quoF h (.eqRefl _))

/-- Decoding inverts encoding. -/
theorem dec_enc {P cP : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ cP) :
    ∀ (k : ℕ) (x w b : PTm n), (∀ q, q < k → (Γ ⊢[PRAAx] lt (proj q x) P)) →
      (Γ ⊢[PRAAx] dec k P (enc k P x + pwr k P * w) b ≐ canon k b x)
  | 0, _, _, _, _ => .eqRefl _
  | k + 1, x, w, b, hx => by
    have d := digit (y := enc k P (sndT x) + pwr k P * w) hP (hx 0 (by omega))
    refine (congrDec (k + 1) P b (enc_step k P x w)).eqTrans ?_
    exact congrPairT (Prf.andE₂ d) ((congrDec k P b (Prf.andE₁ d)).eqTrans
      (dec_enc hP k (sndT x) w b (fun q hq => hx (q + 1) (by omega))))

/-- The high part of a code. -/
theorem quoK_enc {P cP : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ cP) :
    ∀ (k : ℕ) (x w : PTm n), (∀ q, q < k → (Γ ⊢[PRAAx] lt (proj q x) P)) →
      (Γ ⊢[PRAAx] quoK k P (enc k P x + pwr k P * w) ≐ w)
  | 0, x, w, _ => by
    show Γ ⊢[PRAAx] zero + one * w ≐ w
    ipra_ring
  | k + 1, x, w, hx => by
    have d := digit (y := enc k P (sndT x) + pwr k P * w) hP (hx 0 (by omega))
    refine (congrQuoK (k + 1) P (enc_step k P x w)).eqTrans ?_
    exact (congrQuoK k P (Prf.andE₁ d)).eqTrans
      (quoK_enc hP k (sndT x) w (fun q hq => hx (q + 1) (by omega)))

/-- A code is below `P^k`. -/
theorem enc_lt {P : PTm n} :
    ∀ (k : ℕ) (x : PTm n), (∀ q, q < k → (Γ ⊢[PRAAx] lt (proj q x) P)) →
      (Γ ⊢[PRAAx] lt (enc k P x) (pwr k P))
  | 0, _, _ => (succ_monus_succ _ _).eqTrans (zero_monus _)
  | k + 1, x, hx => by
    refine le_of_eq_add (d := monus P (succ (proj 0 x)) + P * monus (pwr k P) (succ (enc k P (sndT x)))) ?_
    ipra_lc [enc, pwr, proj] natEq (eq_add_of_le (hx 0 (by omega))) +
      𝔞 P * natEq (eq_add_of_le (enc_lt k (sndT x) (fun q hq => hx (q + 1) (by omega))))

/-- A pair of codes below `K` gives a code below `K K`. -/
theorem pair_lt {eu ev K : PTm n} (hu : Γ ⊢[PRAAx] lt eu K) (hv : Γ ⊢[PRAAx] lt ev K) :
    Γ ⊢[PRAAx] lt (eu + K * ev) (K * K) :=
  lt_congr ((congrAdd (mul_comm _ _) (.eqRefl _)).eqTrans (add_comm _ _))
    (.eqRefl _) (Order.mul_add_lt_mul hv hu)

/-- The digits are below `P`. -/
theorem dec_lt {P cP : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ cP) :
    ∀ (k : ℕ) (c b : PTm n) (q : ℕ), q < k → (Γ ⊢[PRAAx] lt (proj q (dec k P c b)) P)
  | k + 1, c, b, 0, _ => by
    have d := div_mod_at (Γ := Γ) (x := c) hP
    exact lt_congr (fst_pair _ _).eqSymm (.eqRefl _) (Prf.andE₂ d)
  | k + 1, c, b, q + 1, hq => (lt_congr (proj_pair_succ q _ _).eqSymm (.eqRefl _)
      (dec_lt hP k (quo c P) b q (by omega)))

/-- The tail of a decoded list is the base. -/
theorem tl_dec : ∀ (k : ℕ) (P c b : PTm n), Γ ⊢[PRAAx] tl k (dec k P c b) ≐ b
  | 0, _, _, _ => .eqRefl _
  | k + 1, P, c, b => (tl_pair_succ k _ _).eqTrans (tl_dec k P (quo c P) b)

end LeanProofs.IPRA.Foundations.DigitCodes
