import IPRADerivations.Core.Evaluation
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Signum
import IPRADerivations.Core.Header

/-!
# Bounded decision of equations between terms

A reusable piece of the embedding framework: a finite case analysis performed in the metatheory
becomes a derivation in iPRA. If an equation `s = t` between terms in `m` variables holds at
every valuation by numerals `≤ B` (a fact about the standard values `PTm.ev`, checked in Lean by
any means, for example by `decide`), then iPRA derives `s[σ] = t[σ]` for all terms `σ i` with
`σ i ≤ B`.

* `cases_num`: from `c ≤ B` (a numeral) and derivations of `c = j ⟶ φ` for every `j ≤ B`,
  derive `φ`: the bounded case split, by recursion on `B` in the metatheory;
* `decide_at`: if `σ i = num (ρ i)` for every `i` and `ev ρ s = ev ρ t`, then `s[σ] = t[σ]`,
  through the evaluation theorem `eval_eq` of `Core/Evaluation`;
* `bounded_decide`: the theorem above, by case splits on the variables one at a time;
* `vals`, `mem_vals`, `bounded_decide_list`: the same with the hypothesis as a Boolean check over
  the explicit list of valuations, so that it can be discharged by `decide`;

Each instance is one derivation of iPRA; its size grows like `(B + 1)^m`, but the statement is
uniform in the context and in the terms `σ`.
-/

namespace LeanProofs.IPRA.Foundations.BoundedDecision

open_ipra exports

variable {n : ℕ}

/-- `c < j + 1` gives `c ≤ j`. -/
theorem le_of_lt_succ {Γ : List (Fm PTm n)} {i j : PTm n} (h : Γ ⊢[PRAAx] lt i (succ j)) :
    Γ ⊢[PRAAx] le i j :=
  (succ_monus_succ i j).eqSymm.eqTrans h

/-- The bounded case split: from `c ≤ B` and `c = j ⟶ φ` for every `j ≤ B`, derive `φ`. -/
theorem cases_num (B : ℕ) {Γ : List (Fm PTm n)} {c : PTm n} {φ : Fm PTm n}
    (hc : Γ ⊢[PRAAx] le c (num B)) (k : ∀ j, j ≤ B → (Γ ⊢[PRAAx] (c ≐ num j) ⟶ φ)) :
    Γ ⊢[PRAAx] φ := by
  induction B generalizing Γ with
  | zero => exact .impE (k 0 le_rfl) ((monus_zero c).eqSymm.eqTrans hc)
  | succ B ih =>
    refine .orE (lt_or_eq_of_le hc) ?_ ?_
    · exact ih (le_of_lt_succ Prf.hyp0) (fun j hj => (k j (by omega)).wk)
    · exact .impE (k (B + 1) le_rfl).wk Prf.hyp0

/-- If `σ i = num (ρ i)` and the two sides have the same value at `ρ`, then `s[σ] = t[σ]`. -/
theorem decide_at {m : ℕ} {Γ : List (Fm PTm n)} (s t : PTm m) (σ : Fin m → PTm n)
    (ρ : Fin m → ℕ) (hσ : ∀ i, Γ ⊢[PRAAx] σ i ≐ num (ρ i)) (h : PTm.ev ρ s = PTm.ev ρ t) :
    Γ ⊢[PRAAx] Syn.subst σ s ≐ Syn.subst σ t := by
  have c₁ := Prf.eqCongr (Γ := Γ) s (σ := σ) (σ' := fun i => num (ρ i)) hσ
  have c₂ := Prf.eqCongr (Γ := Γ) t (σ := σ) (σ' := fun i => num (ρ i)) hσ
  exact c₁.eqTrans ((eval_eq ρ s t h).eqTrans c₂.eqSymm)

/-- The induction behind `bounded_decide`: the variables with index `≥ k` are already fixed to
numerals by the context. -/
theorem decide_aux {m : ℕ} (B : ℕ) (s t : PTm m) (σ : Fin m → PTm n)
    (h : ∀ ρ : Fin m → ℕ, (∀ i, ρ i ≤ B) → PTm.ev ρ s = PTm.ev ρ t) (k : ℕ) (hk : k ≤ m)
    {Γ : List (Fm PTm n)} (ρ : Fin m → ℕ) (hρ : ∀ i, ρ i ≤ B)
    (hdet : ∀ i : Fin m, k ≤ i.val → (Γ ⊢[PRAAx] σ i ≐ num (ρ i)))
    (hle : ∀ i, Γ ⊢[PRAAx] le (σ i) (num B)) : Γ ⊢[PRAAx] Syn.subst σ s ≐ Syn.subst σ t := by
  induction k generalizing Γ ρ with
  | zero => exact decide_at s t σ ρ (fun i => hdet i (Nat.zero_le _)) (h ρ hρ)
  | succ k ih =>
    refine cases_num B (hle ⟨k, by omega⟩) (fun j hj => .impI ?_)
    refine ih (by omega) (fun i => if i.val = k then j else ρ i) ?_ ?_ (fun i => (hle i).wk)
    · intro i
      by_cases hi : i.val = k
      · simp [hi, hj]
      · simp [hi, hρ i]
    · intro i hi
      by_cases hik : i.val = k
      · have e : i = ⟨k, by omega⟩ := Fin.ext hik
        rw [if_pos hik, e]
        exact Prf.hyp0
      · have hi' : k + 1 ≤ i.val := by omega
        simpa [hik] using (hdet i hi').wk

/-- Bounded decision: if `s = t` holds at every valuation by numerals `≤ B`, then iPRA derives
`s[σ] = t[σ]` whenever every `σ i ≤ B`. -/
theorem bounded_decide {m : ℕ} (B : ℕ) (s t : PTm m)
    (h : ∀ ρ : Fin m → ℕ, (∀ i, ρ i ≤ B) → PTm.ev ρ s = PTm.ev ρ t)
    {Γ : List (Fm PTm n)} (σ : Fin m → PTm n) (hle : ∀ i, Γ ⊢[PRAAx] le (σ i) (num B)) :
    Γ ⊢[PRAAx] Syn.subst σ s ≐ Syn.subst σ t :=
  decide_aux B s t σ h m le_rfl (fun _ => 0) (fun _ => Nat.zero_le _)
    (fun i hi => absurd i.isLt (by omega)) hle

/-- The valuations of `m` variables by numerals `≤ B`, as a list. -/
def vals : (m : ℕ) → ℕ → List (Fin m → ℕ)
  | 0, _ => [Fin.elim0]
  | m + 1, B => (List.range (B + 1)).flatMap (fun j => (vals m B).map (fun ρ => Fin.cons j ρ))

theorem mem_vals : ∀ (m B : ℕ) (ρ : Fin m → ℕ), (∀ i, ρ i ≤ B) → ρ ∈ vals m B
  | 0, _, ρ, _ => by
    have e : ρ = Fin.elim0 := funext fun i => i.elim0
    simp [vals, e]
  | m + 1, B, ρ, hρ => by
    simp only [vals, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨ρ 0, by have := hρ 0; omega, Fin.tail ρ, mem_vals m B _ (fun i => hρ _), ?_⟩
    exact Fin.cons_self_tail ρ

/-- `bounded_decide` with the hypothesis as a Boolean check over the list `vals m B`, so that it
can be discharged by `decide`. -/
theorem bounded_decide_list {m : ℕ} (B : ℕ) (s t : PTm m)
    (h : (vals m B).all (fun ρ => PTm.ev ρ s == PTm.ev ρ t) = true)
    {Γ : List (Fm PTm n)} (σ : Fin m → PTm n) (hle : ∀ i, Γ ⊢[PRAAx] le (σ i) (num B)) :
    Γ ⊢[PRAAx] Syn.subst σ s ≐ Syn.subst σ t := by
  refine bounded_decide B s t (fun ρ hρ => ?_) σ hle
  have hm := List.all_eq_true.mp h ρ (mem_vals m B ρ hρ)
  simpa using hm

/-! ## Example: the door count of a coloured triangle

The simplex step of the Sperner parity lemma (`thm:sperner` of `topology/dimension_invariance_ipra`)
for `d = 2`, by `bounded_decide_list` and `decide` over the `27` colourings: for colours
`c₀, c₁, c₂ ∈ {0, 1, 2}`, with `full = [the colours are 0, 1, 2]` and `doors` the number of edges
coloured `{0, 1}`, `doors + full = 2 sg(doors)`, so `doors ≡ full (mod 2)`. -/

section DoorExample

/-- `[c_i = k]` over the colour variables `0, 1, 2`. -/
def ek (i : Fin 3) (k : ℕ) : PTm 3 := eqb (var i) (num k)

/-- The number of vertices of colour `k`. -/
def cnt (k : ℕ) : PTm 3 := ek 0 k + ek 1 k + ek 2 k

/-- The triangle is full: each colour `0, 1, 2` occurs once. -/
def full₃ : PTm 3 := eqb (cnt 0) (num 1) * eqb (cnt 1) (num 1) * eqb (cnt 2) (num 1)

/-- The edge opposite vertex `t` is a door: its colours are `0` and `1`. -/
def door (t : Fin 3) : PTm 3 :=
  eqb (monus (cnt 0) (ek t 0)) (num 1) * eqb (monus (cnt 1) (ek t 1)) (num 1)

/-- The number of doors. -/
def doors₃ : PTm 3 := door 0 + door 1 + door 2

/-- The door count of a coloured triangle: `doors + full = 2 sg(doors)` for colours `≤ 2`. -/
theorem triangle_doors {Γ : List (Fm PTm n)} (c : Fin 3 → PTm n)
    (hc : ∀ i, Γ ⊢[PRAAx] le (c i) (num 2)) :
    Γ ⊢[PRAAx] Syn.subst c (doors₃ + full₃) ≐ Syn.subst c (num 2 * Signum.sg doors₃) :=
  bounded_decide_list 2 _ _ (by decide) c hc

end DoorExample

end LeanProofs.IPRA.Foundations.BoundedDecision
