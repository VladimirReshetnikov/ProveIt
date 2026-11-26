import IPRADerivations.Core.Search
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# The bounded energy window

Packet: `foundations/ipra_measure_transport_2026-11-20`, `lean/Energy.lean`, `energy_window` (stated there as an
ordinary Lean theorem about rational sequences, "the object-iPRA translation remains a separate task"): "A
bounded energy budget gives a finite small-increment witness. For metastability apply `E` to iterated
endpoints `N(j+1) = N(j) + g(N(j))`, and put `δ = ε²`. The output is an actual bounded-search result."

Here the energy `E(j, x)` is any primitive recursive function and the increment threshold `δ(x)` any primitive
recursive function of the parameter, in common integer units. The witness is the bounded search
`w = μ_{j<N}[E(j + 1, x) ≤ E(j, x) + δ(x)]` of `Core/Search`, an explicit primitive recursive term:

* `growth`: below the search result every increment exceeds `δ`, so `w · δ ≤ E(w, x)` (quantifier-free
  induction);
* `energy_window`: if `E(N, x) ≤ B < N δ(x)` then `w < N` and `E(w + 1, x) ≤ E(w, x) + δ(x)`;
* `energy_window_closed`: the same as one closed sentence over `N, x, B`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.EnergyWindow

open_ipra
open LeanProofs.IPRA.Search (mu search_spec search_minimal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (E : PR 2) (D : PR 1)

/-- The search body `E(j + 1, x) ∸ (E(j, x) + δ(x))`, zero exactly at a small increment. -/
abbrev gap : PTm 2 := monus (ap2 E (succ (var 0)) (var 1)) (ap2 E (var 0) (var 1) + ap1 D (var 1))

/-- The window `w(N, x)`. -/
abbrev win (N x : PTm n) : PTm n := mu (gap E D) N x

theorem gap_at (i x : PTm n) :
    inst2 (gap E D) i x = monus (ap2 E (succ i) x) (ap2 E i x + ap1 D x) := by
  simp [inst2, gap, subst_ap2, subst_ap1]

variable {E D}

/-- Variables `0 = k` (induction), `1 = x`, `2 = N`. -/
private abbrev gF : Fm PTm 3 :=
  le (var 0) (win E D (var 2) (var 1)) ⟶ le (var 0 * ap1 D (var 1)) (ap2 E (var 0) (var 1))

private theorem g_step {k x N : PTm n}
    (ih : Γ ⊢[PRAAx] le k (win E D N x) ⟶ le (k * ap1 D x) (ap2 E k x)) :
    Γ ⊢[PRAAx] le (succ k) (win E D N x) ⟶ le (succ k * ap1 D x) (ap2 E (succ k) x) := by
  refine .impI ?_
  have h₁ : (le (succ k) (win E D N x) :: Γ) ⊢[PRAAx] lt k (win E D N x) := Prf.hyp0
  have hi : (le (succ k) (win E D N x) :: Γ) ⊢[PRAAx] le (k * ap1 D x) (ap2 E k x) :=
    .impE ih.wk (le_trans (le_succ_self k) Prf.hyp0)
  have hne := search_minimal (f := gap E D) h₁
  rw [gap_at] at hne
  have hlt : (le (succ k) (win E D N x) :: Γ) ⊢[PRAAx] lt (ap2 E k x + ap1 D x) (ap2 E (succ k) x) :=
    .orE (lt_or_le (ap2 E k x + ap1 D x) (ap2 E (succ k) x)) Prf.hyp0
      (.botE _ (.impE hne.wk Prf.hyp0))
  ipra_le sl hlt + 1 + sl hi

private theorem g₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] gF (E := E) (D := D) := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp
    exact .impI (le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _))
  · simp
    exact g_step Prf.hyp0

/-- Below the window every increment exceeds `δ`: `w δ ≤ E(w, x)`. -/
theorem growth (N x : PTm n) :
    Γ ⊢[PRAAx] le (win E D N x * ap1 D x) (ap2 E (win E D N x) x) := by
  have h := inst (Γ := Γ) (g₀ (E := E) (D := D)) (![win E D N x, x, N] : Fin 3 → PTm n)
  simp at h
  exact .impE h (le_refl _)

/-- The energy window: `E(N, x) ≤ B < N δ(x)` gives `w < N` with `E(w + 1, x) ≤ E(w, x) + δ(x)`. -/
theorem energy_window {N x B : PTm n} (hB : Γ ⊢[PRAAx] le (ap2 E N x) B)
    (hbud : Γ ⊢[PRAAx] lt B (N * ap1 D x)) :
    Γ ⊢[PRAAx] lt (win E D N x) N ⋏
      le (ap2 E (succ (win E D N x)) x) (ap2 E (win E D N x) x + ap1 D x) := by
  have s := search_spec (Γ := Γ) (f := gap E D) N zero x
  have hfound := Prf.andE₁ (Prf.andE₂ s)
  rw [gap_at] at hfound
  have hlt : Γ ⊢[PRAAx] lt (win E D N x) N := by
    refine .orE (lt_or_eq_of_le (Prf.andE₁ s)) Prf.hyp0 ?_
    have hg := (growth (Γ := (win E D N x ≐ N) :: Γ) (E := E) (D := D) N x)
    have hN : ((win E D N x ≐ N) :: Γ) ⊢[PRAAx] le (N * ap1 D x) (ap2 E N x) :=
      le_congr (congrMul Prf.hyp0 (.eqRefl _)) (congrAp2 E Prf.hyp0 (.eqRefl _)) hg
    exact le_lt_absurd _ (le_trans hN hB.wk) hbud.wk
  exact .andI hlt (.impE hfound hlt)

/-- Variables `0 = N`, `1 = x`, `2 = B`. -/
def windowBody (E : PR 2) (D : PR 1) : Fm PTm 3 :=
  le (ap2 E (var 0) (var 1)) (var 2) ⟶ lt (var 2) (var 0 * ap1 D (var 1)) ⟶
    (lt (win E D (var 0) (var 1)) (var 0) ⋏
      le (ap2 E (succ (win E D (var 0) (var 1))) (var 1)) (ap2 E (win E D (var 0) (var 1)) (var 1) +
        ap1 D (var 1)))

/-- The energy window as one closed sentence. -/
theorem energy_window_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (windowBody E D) :=
  closeUniv 3 (.impI (.impI (energy_window Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.EnergyWindow
