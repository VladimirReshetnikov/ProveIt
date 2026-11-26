import IPRADerivations.Core.Order
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Tactic
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.CommonLemmas

/-!
# Monotonicity of the lexicographic fuel bounds (`ipra_resources_and_elimination_2026-11-15`, Section 4)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, Section "Primitive-recursive fuel
for fixed-dimensional lexicographic descent": for a primitive recursive `h(x, t)` nondecreasing
in `t`,

`F_0(x, s) = s + 1`,   `F_{d+1}(x, s) = F_d(x, ·)^{[h(x, s) + 1]}(s)`,

and the lemma "Monotonicity of the bounds": "For every fixed `d`, iPRA proves
`F_d(x, s) ≥ s + 1`, and `s ≤ t ⟹ F_d(x, s) ≤ F_d(x, t)`. Proof: ... Iterating a nondecreasing
function preserves inequalities between starting points. Iterating a function `f(u) ≥ u + 1`
more times cannot decrease its value ... These two assertions follow by quantifier-free
induction on the iteration counter ... The induction on `d` here constructs a separate finite
iPRA proof for each fixed dimension."

* `itP f n x s`: the iterate `f(x, ·)^{[n]}(s)` of a binary term with parameter `x`, by one
  primitive recursion on the pair `⟨x, s⟩` (`itP_zero`, `itP_succ`);
* `Step f`: the two properties of a step, as rules: `f(x, ·)` is nondecreasing, and
  `f(x, u) ≥ u + 1`;
* `mono_start`: `u ≤ w` gives `f^{[n]}(u) ≤ f^{[n]}(w)` (quantifier-free induction on `n`);
* `grow_iter`: `s + n ≤ f^{[n]}(s)`;
* `mono_count`: `r ≤ r'` gives `f^{[r]}(s) ≤ f^{[r']}(s)` (induction on the difference);
* `F h d`: the fuel functions as terms, by recursion on the external number `d`
  (`F_zero_at`, `F_succ_at`);
* `fuel_step`: for every `d`, `F_d` is a step: `F_d(x, s) ≥ s + 1` and
  `s ≤ t ⟹ F_d(x, s) ≤ F_d(x, t)` (`fuel_grow`, `fuel_mono`): the lemma, for each fixed
  dimension.

The hypothesis on `h` is the packet's: a rule deriving `h(x, s) ≤ h(x, t)` from `s ≤ t`. Not
derived: the controlled chain bound `s + L ≤ F_d(x, s)` (`thm:controlled-lex`, which needs coded
sequences and blocks) and `thm:automatic-lex-fuel`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.LexFuelMonotone

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Iteration with a parameter -/

section Iterate

variable (f : PTm 2)

/-- The step of the iteration; variables `0 = n`, `1 = f^{[n]}(s)`, `2 = ⟨x, s⟩`. -/
def itStep : PTm 3 := inst2 f (fstT (var 2)) (var 1)

/-- `itP f n x s = f(x, ·)^{[n]}(s)`. -/
abbrev itP (n x s : PTm k) : PTm k := ap2 (rec2 (sndT (var 0)) (itStep f)) n (pairT x s)

theorem itP_zero (x s : PTm k) : Γ ⊢[PRAAx] itP f zero x s ≐ s := by
  have h := rec2_zero (Γ := Γ) (sndT (var 0)) (itStep f) (pairT x s)
  have e : Syn.subst ![pairT x s] (sndT (var 0) : PTm 1) = sndT (pairT x s) := by simp
  rw [e] at h
  exact h.eqTrans (snd_pair x s)

theorem itP_succ (n x s : PTm k) :
    Γ ⊢[PRAAx] itP f (succ n) x s ≐ inst2 f x (itP f n x s) := by
  have h := rec2_succ (Γ := Γ) (sndT (var 0)) (itStep f) n (pairT x s)
  have e : Syn.subst ![n, ap2 (rec2 (sndT (var 0)) (itStep f)) n (pairT x s), pairT x s]
      (itStep f) = inst2 f (fstT (pairT x s)) (itP f n x s) := by
    simp [itStep]
    rfl
  rw [e] at h
  exact h.eqTrans (congrInst2 f (fst_pair x s) (.eqRefl _))

/-- The two properties of a step function, as rules: it is nondecreasing in its argument and
exceeds it. -/
structure Step (f : PTm 2) : Prop where
  mono : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u w : PTm k},
    (Γ ⊢[PRAAx] le u w) → (Γ ⊢[PRAAx] le (inst2 f x u) (inst2 f x w))
  grow : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x u : PTm k),
    Γ ⊢[PRAAx] le (succ u) (inst2 f x u)

/-- `u ≤ w` gives `u + 1 ≤ w + 1`. -/
alias succ_le := Common.succ_le_succ

/-- Variables: `0 = n`, `1 = x`, `2 = u`, `3 = w`. -/
private abbrev m1F : Fm PTm 4 :=
  le (var 2) (var 3) ⟶ le (itP f (var 0) (var 1) (var 2)) (itP f (var 0) (var 1) (var 3))

private theorem m1₀ (hf : Step f) : ([] : List (Fm PTm 4)) ⊢[PRAAx] m1F f := by
  ipra_ind (⟨trivial, trivial⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (le_congr (itP_zero f _ _).eqSymm (itP_zero f _ _).eqSymm Prf.hyp0)
  · exact .impI (le_congr (itP_succ f _ _ _).eqSymm (itP_succ f _ _ _).eqSymm
      (hf.mono (.impE Prf.hyp1 Prf.hyp0)))

/-- Iterating a nondecreasing function preserves inequalities between starting points. -/
theorem mono_start (hf : Step f) {x u w : PTm k} (h : Γ ⊢[PRAAx] le u w) (n : PTm k) :
    Γ ⊢[PRAAx] le (itP f n x u) (itP f n x w) := by
  have i := inst (Γ := Γ) (m1₀ f hf) (![n, x, u, w] : Fin 4 → PTm k)
  simp at i
  exact .impE i h

/-- Variables: `0 = n`, `1 = x`, `2 = s`. -/
private abbrev m2F : Fm PTm 3 := le (var 2 + var 0) (itP f (var 0) (var 1) (var 2))

private theorem m2₀ (hf : Step f) : ([] : List (Fm PTm 3)) ⊢[PRAAx] m2F f := by
  ipra_ind [subst_le, subst_ap2, subst_pairT]
  · exact le_congr (add_zero _).eqSymm (itP_zero f _ _).eqSymm (le_refl _)
  · exact le_congr (add_succ _ _).eqSymm (itP_succ f _ _ _).eqSymm
      (le_trans (succ_le Prf.hyp0) (hf.grow _ _))

/-- `n` iterations of a function with `f(u) ≥ u + 1` add at least `n`. -/
theorem grow_iter (hf : Step f) (n x s : PTm k) : Γ ⊢[PRAAx] le (s + n) (itP f n x s) := by
  have i := inst (Γ := Γ) (m2₀ f hf) (![n, x, s] : Fin 3 → PTm k)
  simpa using i

/-- Variables: `0 = j`, `1 = n`, `2 = x`, `3 = s`. -/
private abbrev m3F : Fm PTm 4 :=
  le (itP f (var 1) (var 2) (var 3)) (itP f (var 1 + var 0) (var 2) (var 3))

private theorem m3₀ (hf : Step f) : ([] : List (Fm PTm 4)) ⊢[PRAAx] m3F f := by
  ipra_ind [subst_le, subst_ap2, subst_pairT]
  · exact le_congr (.eqRefl _)
      (congrAp2 (rec2 (sndT (var 0)) (itStep f)) (add_zero _).eqSymm (.eqRefl _)) (le_refl _)
  · refine le_congr (.eqRefl _)
      ((congrAp2 (rec2 (sndT (var 0)) (itStep f)) (add_succ _ _) (.eqRefl _)).eqTrans
        (itP_succ f _ _ _)).eqSymm ?_
    exact le_trans Prf.hyp0 (le_trans (le_succ_self _) (hf.grow _ _))

/-- Iterating a function with `f(u) ≥ u + 1` more times cannot decrease the value. -/
theorem mono_count (hf : Step f) {r r' : PTm k} (h : Γ ⊢[PRAAx] le r r') (x s : PTm k) :
    Γ ⊢[PRAAx] le (itP f r x s) (itP f r' x s) := by
  have i := inst (Γ := Γ) (m3₀ f hf) (![monus r' r, r, x, s] : Fin 4 → PTm k)
  simp at i
  exact le_congr (.eqRefl _)
    (congrAp2 (rec2 (sndT (var 0)) (itStep f)) (eq_add_of_le h).eqSymm (.eqRefl _)) i

end Iterate

/-! ## The fuel functions -/

/-- `F_0(x, s) = s + 1`, `F_{d+1}(x, s) = F_d(x, ·)^{[h(x, s) + 1]}(s)`; variables `0 = x`,
`1 = s`. -/
def F (h : PTm 2) : ℕ → PTm 2
  | 0 => succ (var 1)
  | d + 1 => ap2 (rec2 (sndT (var 0)) (itStep (F h d))) (succ h) (pairT (var 0) (var 1))

theorem F_zero_at (h : PTm 2) (x s : PTm k) : inst2 (F h 0) x s = succ s := by
  simp [inst2, F]

theorem F_succ_at (h : PTm 2) (d : ℕ) (x s : PTm k) :
    inst2 (F h (d + 1)) x s = itP (F h d) (succ (inst2 h x s)) x s := by
  simp [inst2, F]

/-- "Monotonicity of the bounds", for every fixed `d`: `F_d` is nondecreasing and exceeds its
argument. -/
theorem fuel_step {h : PTm 2}
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t))) :
    ∀ d, Step (F h d)
  | 0 =>
    { mono := fun {k Γ x u w} hle => by
        rw [F_zero_at, F_zero_at]
        exact succ_le hle
      grow := fun {k Γ} x u => by
        rw [F_zero_at]
        exact le_refl _ }
  | d + 1 =>
    { mono := fun {k Γ x u w} hle => by
        rw [F_succ_at, F_succ_at]
        exact le_trans (mono_start (F h d) (fuel_step hh d) hle _)
          (mono_count (F h d) (fuel_step hh d) (succ_le (hh hle)) x w)
      grow := fun {k Γ} x u => by
        rw [F_succ_at]
        refine le_trans ?_ (grow_iter (F h d) (fuel_step hh d) _ x u)
        refine le_of_eq_add (d := inst2 h x u) ?_
        ipra_ring }

/-- `F_d(x, s) ≥ s + 1`. -/
theorem fuel_grow {h : PTm 2}
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t)))
    (d : ℕ) (x s : PTm k) : Γ ⊢[PRAAx] le (succ s) (inst2 (F h d) x s) :=
  (fuel_step hh d).grow x s

/-- `s ≤ t ⟹ F_d(x, s) ≤ F_d(x, t)`. -/
theorem fuel_mono {h : PTm 2}
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t)))
    (d : ℕ) {x s t : PTm k} (hle : Γ ⊢[PRAAx] le s t) :
    Γ ⊢[PRAAx] le (inst2 (F h d) x s) (inst2 (F h d) x t) :=
  (fuel_step hh d).mono hle

end LeanProofs.IPRA.Foundations.LexFuelMonotone
