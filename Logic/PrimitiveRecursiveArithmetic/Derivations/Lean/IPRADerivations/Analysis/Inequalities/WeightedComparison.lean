import IPRADerivations.Analysis.Inequalities.WeightedFeedback

/-!
# The a posteriori finite comparison for weighted feedback certificates

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/03_feedback.tex`, Theorem
`thm:feedback-residual` ("A posteriori finite comparison"): for `x, y ∈ D` with `d_w(Tx, x) ≤ r`,
`d_w(Sy, y) ≤ s` and `d_w(Ty, Sy) ≤ δ`, `d_w(x, y) ≤ 2(r + s + δ)` (`eq:perturbed-residual`); "the bounded
rational maximum `E = d_w(x, y)` is attained at a computed index `i₀`. Three triangle inequalities, with one
extra term in the perturbed case, give `E ≤ r + E/2 + s + δ`".

In the setting of `Analysis/WeightedFeedback` (`Cert`), with weights `w_i ≥ 1`:

* `max_exists`: for every nonempty list of indices, some index `i₀` maximizes `δ_i / w_i`, as the iPRA
  disjunction over `i₀` of the conjunctions `δ_j w_{i₀} ≤ δ_{i₀} w_j` (a bounded search by `le_total`, with
  transitivity of the cross-multiplied comparison after cancelling a weight, `cancel_w`);
* `comparison_perturbed` (`eq:perturbed-residual`): `|x_j − y_j| ≤ 2 (r + s + δ) w_j` for every `j`;
* `comparison` (`S = T`, `δ = 0`): `|x_j − y_j| ≤ 2 (r + s) w_j`.

The list-indexed conjunctions and disjunctions `lconj`, `ldisj` carry the bounded maximum search.
-/

namespace LeanProofs.IPRA.Analysis.WeightedComparison

open_ipra
open LeanProofs.IPRA.Analysis.WeightedFeedback (Cert contract_scaled)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.ClipLaws (ad_triangle)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of)
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum)

variable {n m : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## List-indexed connectives -/

/-- `⋀_{j ∈ L} φ j`. -/
def lconj {α : Type} : List α → (α → Fm PTm n) → Fm PTm n
  | [], _ => zero ≐ zero
  | j :: L, φ => φ j ⋏ lconj L φ

/-- `⋁_{j ∈ L} φ j`. -/
def ldisj {α : Type} : List α → (α → Fm PTm n) → Fm PTm n
  | [], _ => Fm.bot
  | j :: L, φ => φ j ⋎ ldisj L φ

theorem lconj_intro {α : Type} {φ : α → Fm PTm n} : {L : List α} → (∀ j ∈ L, Γ ⊢[PRAAx] φ j) →
    (Γ ⊢[PRAAx] lconj L φ)
  | [], _ => .eqRefl _
  | j :: L, h => .andI (h j List.mem_cons_self) (lconj_intro fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem lconj_elim {α : Type} {φ : α → Fm PTm n} : {L : List α} → (Γ ⊢[PRAAx] lconj L φ) →
    ∀ {j}, j ∈ L → (Γ ⊢[PRAAx] φ j)
  | [], _, _, hj => absurd hj List.not_mem_nil
  | i :: L, h, j, hj => by
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h.andE₁
    · exact lconj_elim h.andE₂ hj

theorem ldisj_intro {α : Type} {φ : α → Fm PTm n} : {L : List α} → ∀ {j}, j ∈ L → (Γ ⊢[PRAAx] φ j) →
    (Γ ⊢[PRAAx] ldisj L φ)
  | [], _, hj, _ => absurd hj List.not_mem_nil
  | i :: L, j, hj, h => by
    rcases List.mem_cons.mp hj with rfl | hj
    · exact .orI₁ h
    · exact .orI₂ (ldisj_intro hj h)

theorem ldisj_elim {α : Type} {φ : α → Fm PTm n} {χ : Fm PTm n} : {L : List α} →
    (∀ j ∈ L, Γ ⊢[PRAAx] φ j ⟶ χ) → (Γ ⊢[PRAAx] ldisj L φ ⟶ χ)
  | [], _ => .impI (.botE _ Prf.hyp0)
  | j :: L, h => .impI (.orE Prf.hyp0 (.impE (h j List.mem_cons_self).wk.wk Prf.hyp0)
      (.impE (ldisj_elim (L := L) fun i hi => h i (List.mem_cons_of_mem _ hi)).wk.wk Prf.hyp0))

/-! ## Cancellation and the bounded maximum -/

/-- Cancelling a positive factor. -/
theorem cancel_w {w a b : PTm n} (hw : Γ ⊢[PRAAx] le one w) (h : Γ ⊢[PRAAx] le (w * a) (w * b)) :
    Γ ⊢[PRAAx] le a b := by
  have h' : Γ ⊢[PRAAx] le (succ (monus w one) * a) (succ (monus w one) * b) := by
    ipra_le sl h with (𝔟 a - 𝔟 b) * natEq (eq_add_of_le hw)
  exact mul_le_cancel h'

/-- `δ_j / w_j ≤ δ_i / w_i`, cross-multiplied. -/
def R (δ w : Fin m → PTm n) (j i : Fin m) : Fm PTm n := le (δ j * w i) (δ i * w j)

/-- Some index of a nonempty list maximizes `δ_i / w_i`. -/
theorem max_exists (δ w : Fin m → PTm n) (hw : ∀ i, Γ ⊢[PRAAx] le one (w i)) :
    ∀ (a : Fin m) (L : List (Fin m)),
      Γ ⊢[PRAAx] ldisj (a :: L) (fun i => lconj (a :: L) (fun j => R δ w j i))
  | a, [] => .orI₁ (lconj_intro fun j hj => by
      rcases List.mem_singleton.mp hj with rfl
      exact le_refl _)
  | a, b :: L => by
    have ih := max_exists δ w hw b L
    refine .impE (ldisj_elim fun i0 hi0 => ?_) ih
    refine .impI (.orE (le_total (δ a * w i0) (δ i0 * w a)) ?_ ?_)
    · have hc : (le (δ a * w i0) (δ i0 * w a) :: lconj (b :: L) (fun j => R δ w j i0) :: Γ) ⊢[PRAAx]
          lconj (b :: L) (fun j => R δ w j i0) := Prf.hyp1
      have ha : (le (δ a * w i0) (δ i0 * w a) :: lconj (b :: L) (fun j => R δ w j i0) :: Γ) ⊢[PRAAx]
          R δ w a i0 := Prf.hyp0
      refine ldisj_intro (List.mem_cons_of_mem a hi0) (lconj_intro fun j hj => ?_)
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ha
      · exact lconj_elim hc hj
    · have hc : (le (δ i0 * w a) (δ a * w i0) :: lconj (b :: L) (fun j => R δ w j i0) :: Γ) ⊢[PRAAx]
          lconj (b :: L) (fun j => R δ w j i0) := Prf.hyp1
      have h2 : (le (δ i0 * w a) (δ a * w i0) :: lconj (b :: L) (fun j => R δ w j i0) :: Γ) ⊢[PRAAx]
          le (δ i0 * w a) (δ a * w i0) := Prf.hyp0
      refine ldisj_intro List.mem_cons_self (lconj_intro fun j hj => ?_)
      rcases List.mem_cons.mp hj with rfl | hj
      · exact le_refl _
      · have h1 : _ ⊢[PRAAx] le (δ j * w i0) (δ i0 * w j) := lconj_elim hc hj
        show _ ⊢[PRAAx] le (δ j * w a) (δ a * w j)
        exact cancel_w (hw i0).wk.wk (by ipra_le 𝔟 (w a) * sl h1 + 𝔟 (w j) * sl h2)

/-! ## The comparison -/

variable {a : Fin m → Fin m → PTm n} {w : Fin m → PTm n} {T : (Fin m → PTm n) → Fin m → PTm n}
  {D : (Fin m → PTm n) → Prop}

theorem Cert.wk (C : Cert Γ a w T D) (φ : Fm PTm n) : Cert (φ :: Γ) a w T D :=
  ⟨fun i => (C.half i).wk, C.dom, fun x y hx hy i => (C.gain x y hx hy i).wk⟩

/-- The hypothesis "`i₀` maximizes `|x_i − y_i| / w_i`". -/
def maxAt (x y w : Fin m → PTm n) (i0 : Fin m) : Fm PTm n :=
  lconj (List.finRange m) (fun k => R (fun i => ad (x i) (y i)) w k i0)

/-- `eq:perturbed-residual`: `|x_j − y_j| ≤ 2 (r + s + δ) w_j`. -/
theorem comparison_perturbed (C : Cert Γ a w T D) (hw : ∀ i, Γ ⊢[PRAAx] le one (w i))
    {S : (Fin m → PTm n) → Fin m → PTm n} {x y : Fin m → PTm n} (hx : D x) (hy : D y) {r s d : PTm n}
    (hr : ∀ i, Γ ⊢[PRAAx] le (ad (T x i) (x i)) (r * w i))
    (hs : ∀ i, Γ ⊢[PRAAx] le (ad (S y i) (y i)) (s * w i))
    (hd : ∀ i, Γ ⊢[PRAAx] le (ad (T y i) (S y i)) (d * w i)) (j : Fin m) :
    Γ ⊢[PRAAx] le (ad (x j) (y j)) (two * (r + s + d) * w j) := by
  have hL : List.finRange m ≠ [] := by
    intro h; have := List.mem_finRange j; rw [h] at this; exact List.not_mem_nil this
  obtain ⟨b, L, hbL⟩ : ∃ b L, List.finRange m = b :: L := by
    cases h : List.finRange m with
    | nil => exact absurd h hL
    | cons b L => exact ⟨b, L, rfl⟩
  have hmax := max_exists (Γ := Γ) (fun i => ad (x i) (y i)) w hw b L
  rw [← hbL] at hmax
  refine .impE (ldisj_elim fun i0 _ => ?_) hmax
  show Γ ⊢[PRAAx] maxAt x y w i0 ⟶ _
  refine .impI ?_
  have maxim : ∀ k, (maxAt x y w i0 :: Γ) ⊢[PRAAx] le (ad (x k) (y k) * w i0) (ad (x i0) (y i0) * w k) :=
    fun k => lconj_elim (Prf.hyp0 : (maxAt x y w i0 :: Γ) ⊢[PRAAx] maxAt x y w i0) (List.mem_finRange k)
  have C' := Cert.wk C (maxAt x y w i0)
  have c1 := contract_scaled C' hx hy (s := w i0) (r := ad (x i0) (y i0))
    (fun k => by have := maxim k; ipra_le sl this) i0
  have t1 := ad_triangle (Γ := maxAt x y w i0 :: Γ) (x i0) (T x i0) (y i0)
  have t2 := ad_triangle (Γ := maxAt x y w i0 :: Γ) (T x i0) (T y i0) (y i0)
  have t3 := ad_triangle (Γ := maxAt x y w i0 :: Γ) (T y i0) (S y i0) (y i0)
  have hr0 := (hr i0).wk (ψ := maxAt x y w i0)
  have hs0 := (hs i0).wk (ψ := maxAt x y w i0)
  have hd0 := (hd i0).wk (ψ := maxAt x y w i0)
  have hw0 := (hw i0).wk (ψ := maxAt x y w i0)
  have e0 : (maxAt x y w i0 :: Γ) ⊢[PRAAx]
      le (w i0 * ad (x i0) (y i0)) (w i0 * (two * (r + s + d) * w i0)) := by
    ipra_le 2 * 𝔟 (w i0) * (sl t1 + sl t2 + sl t3 + sl hr0 + sl hs0 + sl hd0) + sl c1
  have hδ0 := cancel_w hw0 e0
  have hmj := maxim j
  have hwj : (maxAt x y w i0 :: Γ) ⊢[PRAAx]
      le (w i0 * ad (x j) (y j)) (w i0 * (two * (r + s + d) * w j)) := by
    ipra_le sl hmj + 𝔟 (w j) * sl hδ0
  exact cancel_w hw0 hwj

/-- `thm:feedback-residual`: `d_w(Tx, x) ≤ r` and `d_w(Ty, y) ≤ s` give `|x_j − y_j| ≤ 2 (r + s) w_j`. -/
theorem comparison (C : Cert Γ a w T D) (hw : ∀ i, Γ ⊢[PRAAx] le one (w i)) {x y : Fin m → PTm n}
    (hx : D x) (hy : D y) {r s : PTm n} (hr : ∀ i, Γ ⊢[PRAAx] le (ad (T x i) (x i)) (r * w i))
    (hs : ∀ i, Γ ⊢[PRAAx] le (ad (T y i) (y i)) (s * w i)) (j : Fin m) :
    Γ ⊢[PRAAx] le (ad (x j) (y j)) (two * (r + s + zero) * w j) := by
  refine comparison_perturbed C hw (S := T) hx hy hr hs (fun i => ?_) j
  have h : Γ ⊢[PRAAx] le (ad (T y i) (T y i)) zero :=
    ad_le_of (a := T y i) (b := T y i) (c := zero) (by ipra_le 0) (by ipra_le 0)
  ipra_le sl h

end LeanProofs.IPRA.Analysis.WeightedComparison
