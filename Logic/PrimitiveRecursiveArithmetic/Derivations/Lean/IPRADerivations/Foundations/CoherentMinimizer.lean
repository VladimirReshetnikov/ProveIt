import IPRADerivations.Foundations.ModulusNormalization

/-!
# Coherent extraction from approximate minima

Packet: `foundations/ipra_finite_observation`, `tex/analysis.tex`, Theorem `thm:coherent-minimizer`
("Coherent extraction from approximate minima").

In the setting of `thm:finite-net-infimum`, the rational points `a_i` are approximate minimizers,
`f(a_i) ≤ V + 2^{-i}` (the paper's `¾ 2^{-i}` is stronger), and a primitive recursive `u` is a quantitative
uniqueness modulus: two points within `2^{-u(k)}` of the optimum are within `2^{-k}` of each other
(`eq:quantitative-uniqueness`). With `v(k) = k + max_{j ≤ k} u(j)` (`ModulusNormalization.mhat`) and
`x_k = a_{v(k)}`, the paper's estimate is `d(x_k, x_l) ≤ 2^{-min(k, l)} ≤ 2^{-k} + 2^{-l}`.

Cleared form: the optimum gap of `a_i` is `G(i)/W` (with `f(a_i) − V = G(i)/W ≥ 0`) and the distance between
`a_i` and `a_j` is `D(i, j)/W′`. The hypotheses are rules at the context `Γ`, for arbitrary terms:

* `opt`: `2^i G(i) ≤ W`;
* `uniq`: `2^{u(k)} G(i) ≤ W` and `2^{u(k)} G(j) ≤ W` give `2^k D(i, j) ≤ W′`.

Derived:

* `gap_le`: `2^{u(k)} G(a_{v(l)}) ≤ W` for `k ≤ l`, since `u(k) ≤ v(k) ≤ v(l)` and `2^e` is monotone in `e`;
* `coherent_le`, `coherent_ge`: `2^{min(k,l)} D(x_k, x_l) ≤ W′`, each order separately;
* `mn_le_left`, `mn_le_right`, `pw_min`: `min(k, l)` and `2^k 2^l ≤ (2^k + 2^l) 2^{min(k,l)}`;
* `cauchy`: uniqueness at precision `min(k, l)` gives `2^k 2^l D(x_k, x_l) ≤ (2^k + 2^l) W′`, i.e. `d(x_k, x_l) ≤ 2^{-k} + 2^{-l}`: the `x_k` form a
  regular point name.

The canonical evaluation `f(X) = V` and the uniqueness of the point name are not derived here.
-/

namespace LeanProofs.IPRA.Foundations.CoherentMinimizer

open_ipra exports
open LeanProofs.IPRA.Foundations.ModulusNormalization (mhat index_le modulus_le mhat_mono)
open LeanProofs.IPRA.Probability.Ninther (mn mn_le mn_ge)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `2 = succ (pred 2)`. -/
theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) :=
  congrSucc (pred_succ one).eqSymm

section Extraction

variable (u : PTm 2) (x : PTm n) (G : PTm n → PTm n) (D : PTm n → PTm n → PTm n) (W W' : PTm n)

/-- The candidate gaps are at most `2^{-i}`. -/
abbrev Opt : Prop := ∀ i : PTm n, Γ ⊢[PRAAx] le (pw two i * G i) W

/-- `eq:quantitative-uniqueness`: within `2^{-u(k)}` of the optimum implies within `2^{-k}`. -/
abbrev Uniq : Prop := ∀ k i j : PTm n,
  (Γ ⊢[PRAAx] le (pw two (inst2 u k x) * G i) W) → (Γ ⊢[PRAAx] le (pw two (inst2 u k x) * G j) W) →
    (Γ ⊢[PRAAx] le (pw two k * D i j) W')

variable {u x G D W W'}

/-- For `k ≤ l`, the point `x_l = a_{v(l)}` is within `2^{-u(k)}` of the optimum. -/
theorem gap_le (opt : Opt (Γ := Γ) G W) {k l : PTm n} (h : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] le (pw two (inst2 u k x) * G (mhat u l x)) W := by
  have m₁ := modulus_le u (Γ := Γ) (x := x) (le_refl k)
  have m₂ := mhat_mono u (x := x) h
  have e : Γ ⊢[PRAAx] le (inst2 u k x) (mhat u l x) := by ipra_le sl m₁ + sl m₂
  have p := pw_le_exp two_pos e
  have o := opt (mhat u l x)
  ipra_le sl o + sl p * 𝔟 (G (mhat u l x))

/-- `2^k D(x_k, x_l) ≤ W′` for `k ≤ l`. -/
theorem coherent_le (opt : Opt (Γ := Γ) G W) (uniq : Uniq (Γ := Γ) u x G D W W') {k l : PTm n}
    (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx] le (pw two k * D (mhat u k x) (mhat u l x)) W' :=
  uniq k _ _ (gap_le opt (le_refl k)) (gap_le opt h)

/-- `2^l D(x_k, x_l) ≤ W′` for `l ≤ k`. -/
theorem coherent_ge (opt : Opt (Γ := Γ) G W) (uniq : Uniq (Γ := Γ) u x G D W W') {k l : PTm n}
    (h : Γ ⊢[PRAAx] le l k) : Γ ⊢[PRAAx] le (pw two l * D (mhat u k x) (mhat u l x)) W' :=
  uniq l _ _ (gap_le opt h) (gap_le opt (le_refl l))

/-- `min(k, l) ≤ k`. -/
theorem mn_le_left (k l : PTm n) : Γ ⊢[PRAAx] le (mn k l) k :=
  Common.monus_le_self k (monus k l)

/-- `min(k, l) ≤ l`. -/
theorem mn_le_right (k l : PTm n) : Γ ⊢[PRAAx] le (mn k l) l :=
  Order.monus_le_of_le_add
    (le_congr (.eqRefl _) (add_comm l (monus k l)) (Common.le_add_monus k l))

/-- `2^k 2^l ≤ (2^k + 2^l) 2^{min(k,l)}`. -/
theorem pw_min (k l : PTm n) :
    Γ ⊢[PRAAx] le (pw two k * pw two l) ((pw two k + pw two l) * pw two (mn k l)) := by
  refine .orE (le_total k l) ?_ ?_
  · have e := natEq (congrPw (.eqRefl (two : PTm n)) (mn_le (Γ := le k l :: Γ) Prf.hyp0))
    ipra_le 𝔟 (pw two k) * 𝔟 (pw two k) using
      linear_combination (𝔟 (pw two k) + 𝔟 (pw two l)) * e
  · have e := natEq (congrPw (.eqRefl (two : PTm n)) (mn_ge (Γ := le l k :: Γ) Prf.hyp0))
    ipra_le 𝔟 (pw two l) * 𝔟 (pw two l) using
      linear_combination (𝔟 (pw two k) + 𝔟 (pw two l)) * e

/-- `thm:coherent-minimizer`: `d(x_k, x_l) ≤ 2^{-min(k,l)} ≤ 2^{-k} + 2^{-l}`, cleared. -/
theorem cauchy (opt : Opt (Γ := Γ) G W) (uniq : Uniq (Γ := Γ) u x G D W W') (k l : PTm n) :
    Γ ⊢[PRAAx] le (pw two k * pw two l * D (mhat u k x) (mhat u l x)) ((pw two k + pw two l) * W') := by
  have c := uniq (mn k l) _ _ (gap_le opt (mn_le_left k l)) (gap_le opt (mn_le_right k l))
  have a := pw_min (Γ := Γ) k l
  ipra_le (𝔟 (pw two k) + 𝔟 (pw two l)) * sl c + sl a * 𝔟 (D (mhat u k x) (mhat u l x))

end Extraction

end LeanProofs.IPRA.Foundations.CoherentMinimizer
