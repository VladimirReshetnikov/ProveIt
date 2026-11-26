import IPRADerivations.Foundations.LexFuelMonotone
import IPRADerivations.Core.InductionTactic

/-!
# A potential for controlled lexicographic descent (`ipra_resources_and_elimination_2026-11-15`, `thm:controlled-lex`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, theorem `thm:controlled-lex`: "Fix
`d`. Let `v_s, v_{s+1}, …, v_{s+L−1} ∈ ℕ^d` be a finite sequence such that
`v_t >_lex v_{t+1}` whenever both terms occur, and every coordinate of `v_t` is at most
`h(x, t)`. Then `s + L ≤ F_d(x, s)`."

The packet partitions the chain into blocks on which the first coordinate is constant. Here the
same bound is obtained from a potential that never increases along the chain, which needs no
block decomposition. For a `d`-tuple `c` and a time `t` put

`G_0(t) = t + 1`,   `G_{d+1}((a, c'), t) = F_d(x, ·)^{[a]}(G_d(c', t))`.

For every external `d` (each instance is one iPRA derivation), with `h` nondecreasing:

* `itP_comm`, `itP_shift`: `f^{[n]}(f(s)) = f(f^{[n]}(s)) = f^{[n+1]}(s)`;
* `le_itP`, `itP_congr_count`: iterates of a step are at least the start, and congruence in the
  counter;
* `G`, `lexgt`: the potential, and the strict lexicographic order as a formula;
* `G_lower`: `t + 1 ≤ G_d(c, t)`;
* `G_upper`: if every coordinate of `c` is at most `h(x, t)`, then `G_d(c, t) ≤ F_d(x, t)`;
* `G_descent`: if `c >_lex c'` and every coordinate of `c'` is at most `h(x, t + 1)`, then
  `G_d(c', t + 1) ≤ G_d(c, t)`: one step of a controlled chain does not increase the potential;
* `chain_step`: hence `t + 2 ≤ G_d(c, t)` for such a step, and with the envelope at `t`,
  `t + 2 ≤ F_d(x, t)`: a chain of length two starting at `t`.

`Foundations/LexChain` iterates `G_descent` along a whole chain. Not derived here:
`thm:automatic-lex-fuel`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.LexPotential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.LexFuelMonotone
  (itStep itP itP_zero itP_succ Step succ_le mono_start grow_iter mono_count F F_zero_at
    F_succ_at fuel_step)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## More on iterates -/

section Iterate

variable (f : PTm 2)

/-- Variables: `0 = n`, `1 = x`, `2 = s`. -/
private abbrev shF : Fm PTm 3 :=
  itP f (var 0) (var 1) (inst2 f (var 1) (var 2)) ≐
    inst2 f (var 1) (itP f (var 0) (var 1) (var 2))

private theorem sh₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] shF f := by
  ipra_ind [subst_ap2, subst_pairT, subst_inst2]
  · exact (itP_zero f _ _).eqTrans (congrInst2 f (.eqRefl _) (itP_zero f _ _).eqSymm)
  · exact (itP_succ f _ _ _).eqTrans ((congrInst2 f (.eqRefl _) Prf.hyp0).eqTrans
      (congrInst2 f (.eqRefl _) (itP_succ f _ _ _).eqSymm))

/-- `f^{[n]}(f(s)) = f(f^{[n]}(s))`. -/
theorem itP_comm (n x s : PTm k) :
    Γ ⊢[PRAAx] itP f n x (inst2 f x s) ≐ inst2 f x (itP f n x s) := by
  have i := inst (Γ := Γ) (sh₀ f) (![n, x, s] : Fin 3 → PTm k)
  simpa using i

/-- `f^{[n]}(f(s)) = f^{[n+1]}(s)`. -/
theorem itP_shift (n x s : PTm k) :
    Γ ⊢[PRAAx] itP f n x (inst2 f x s) ≐ itP f (succ n) x s :=
  (itP_comm f n x s).eqTrans (itP_succ f n x s).eqSymm

/-- An iterate of a step is at least its starting point. -/
theorem le_itP (hf : Step f) (n x s : PTm k) : Γ ⊢[PRAAx] le s (itP f n x s) :=
  le_trans (le_add_right s n) (grow_iter f hf n x s)

/-- The iterate depends only on the value of its counter. -/
theorem itP_congr_count {n n' : PTm k} (h : Γ ⊢[PRAAx] n ≐ n') (x s : PTm k) :
    Γ ⊢[PRAAx] itP f n x s ≐ itP f n' x s :=
  congrAp2 (rec2 (sndT (var 0)) (itStep f)) h (.eqRefl _)

end Iterate

/-! ## The potential -/

variable (h : PTm 2)

/-- `G_0(t) = t + 1`, `G_{d+1}((a, c'), t) = F_d(x, ·)^{[a]}(G_d(c', t))`. -/
def G : {d : ℕ} → (Fin d → PTm k) → PTm k → PTm k → PTm k
  | 0, _, _, t => succ t
  | d + 1, c, x, t => itP (F h d) (c 0) x (G (fun j => c j.succ) x t)

/-- The strict lexicographic order `c >_lex c'`, most significant coordinate first. -/
def lexgt : {d : ℕ} → (Fin d → PTm k) → (Fin d → PTm k) → Fm PTm k
  | 0, _, _ => Fm.bot
  | _ + 1, c, c' =>
    lt (c' 0) (c 0) ⋎ ((c 0 ≐ c' 0) ⋏ lexgt (fun j => c j.succ) (fun j => c' j.succ))

variable {h}

/-- `t + 1 ≤ G_d(c, t)`. -/
theorem G_lower
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t))) :
    {d : ℕ} → (c : Fin d → PTm k) → (x t : PTm k) → (Γ ⊢[PRAAx] le (succ t) (G h c x t))
  | 0, _, _, _ => le_refl _
  | d + 1, c, x, t =>
    le_trans (G_lower hh (fun j => c j.succ) x t) (le_itP (F h d) (fuel_step hh d) _ x _)

/-- Under the envelope, `G_d(c, t) ≤ F_d(x, t)`. -/
theorem G_upper
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t))) :
    {d : ℕ} → {c : Fin d → PTm k} → {x t : PTm k} →
      (∀ j, Γ ⊢[PRAAx] le (c j) (inst2 h x t)) →
      (Γ ⊢[PRAAx] le (G h c x t) (inst2 (F h d) x t))
  | 0, _, x, t, _ => by
    rw [F_zero_at]
    exact le_refl _
  | d + 1, c, x, t, hc => by
    rw [F_succ_at]
    have ih := G_upper hh (c := fun j => c j.succ) (x := x) (t := t) (fun j => hc j.succ)
    exact le_trans (mono_start (F h d) (fuel_step hh d) ih (c 0))
      (le_congr (itP_shift (F h d) (c 0) x t).eqSymm (.eqRefl _)
        (mono_count (F h d) (fuel_step hh d) (succ_le (hc 0)) x t))

/-- One step of a controlled chain does not increase the potential. -/
theorem G_descent
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t))) :
    {d : ℕ} → {Γ : List (Fm PTm k)} → {c c' : Fin d → PTm k} → {x t : PTm k} →
      (Γ ⊢[PRAAx] lexgt c c') → (∀ j, Γ ⊢[PRAAx] le (c' j) (inst2 h x (succ t))) →
      (Γ ⊢[PRAAx] le (G h c' x (succ t)) (G h c x t))
  | 0, _, _, _, _, _, hl, _ => .botE _ hl
  | d + 1, Γ, c, c', x, t, hl, hb => by
    refine .orE hl ?_ ?_
    · have up := G_upper (Γ := lt (c' 0) (c 0) :: Γ) hh (c := fun j => c' j.succ) (x := x)
        (t := succ t) (fun j => (hb j.succ).wk)
      have s₁ := mono_start (F h d) (fuel_step hh d) (x := x) up (c' 0)
      have s₂ := mono_count (F h d) (fuel_step hh d)
        (Prf.hyp0 : (lt (c' 0) (c 0) :: Γ) ⊢[PRAAx] lt (c' 0) (c 0)) x (succ t)
      have s₃ := mono_start (F h d) (fuel_step hh d) (x := x)
        (G_lower (Γ := lt (c' 0) (c 0) :: Γ) hh (fun j => c j.succ) x t) (c 0)
      exact le_trans s₁
        (le_trans (le_congr (itP_shift (F h d) (c' 0) x (succ t)).eqSymm (.eqRefl _) s₂) s₃)
    · have ih := G_descent hh
        (Γ := ((c 0 ≐ c' 0) ⋏ lexgt (fun j => c j.succ) (fun j => c' j.succ)) :: Γ)
        (c := fun j => c j.succ) (c' := fun j => c' j.succ) (x := x) (t := t)
        (Prf.andE₂ Prf.hyp0) (fun j => (hb j.succ).wk)
      exact le_congr (.eqRefl _)
        (itP_congr_count (F h d) (Prf.andE₁ Prf.hyp0).eqSymm x _)
        (mono_start (F h d) (fuel_step hh d) ih (c' 0))

/-- A chain of length two starting at `t`: `t + 2 ≤ F_d(x, t)`. -/
theorem chain_step
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t)))
    {d : ℕ} {c c' : Fin d → PTm k} {x t : PTm k} (hl : Γ ⊢[PRAAx] lexgt c c')
    (hb : ∀ j, Γ ⊢[PRAAx] le (c j) (inst2 h x t))
    (hb' : ∀ j, Γ ⊢[PRAAx] le (c' j) (inst2 h x (succ t))) :
    Γ ⊢[PRAAx] le (succ (succ t)) (inst2 (F h d) x t) :=
  le_trans (G_lower hh c' x (succ t)) (le_trans (G_descent hh hl hb') (G_upper hh hb))

end LeanProofs.IPRA.Foundations.LexPotential
