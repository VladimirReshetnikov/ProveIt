import IPRADerivations.Foundations.FilteredEnumeration
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# Bounded point-list correctness

Packet: `foundations/pcfm_ipra_framework_2026-11-16`, `paper/sections/12_examples.tex`, Theorem "Bounded
point-list correctness": the consumer scans `j < N(C)`, checks `W(C, E(C, j))` and keeps the qualifying
codes; from the `height` and `cover` modules iPRA proves `W(C, x) = 1 ⟺ ∃ j < ℓ(L_C) [L_C[j] ∼ x]`.
"Soundness follows from the append condition and extensionality of `W`. For completeness, the height
module gives the bounded region and the cover module gives an index `j < N(C)`."

Data (variables `0` = point or index, `1` = the parameter `C = p`): a test `W(x, p)` with values in
`{0, 1}`, candidate codes `E(j, p)` and a code equivalence `x ∼ y` given by a formula `R(x, y)`. The kept
indices are those with `K(j, p) = W(E(j, p), p) ≠ 0`; the list is `L[r] = E(sel r, p)`, `r < ℓ`, with the
rank and select of `Foundations/FilteredEnumeration` (no list code is needed). The hypotheses
(`PointData`) are rules: `W` is a bit, `W` respects `∼`, `∼` is symmetric.

* `sound`: `r < ℓ` and `L[r] ∼ x` give `W(x) = 1` (the kept condition and extensionality);
* `complete_at`: an index `j < N` with `E(j) ∼ x` and `W(x) = 1` gives `rank j < ℓ` and `L[rank j] ∼ x`;
* `complete`: from the cover module as an existential (`W(x) = 1 → ∃ j < N, E(j) ∼ x`), the existential
  `∃ r < ℓ, L[r] ∼ x`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.PointList

open_ipra
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size)
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (W E : PTm 2) (R : Fm PTm 2)

/-- `K(j, p) = W(E(j, p), p)`: the kept test. -/
def KB : PTm 2 := Syn.subst ![E, Syn.var 1] W

theorem inst2_KB {k : ℕ} (j p : PTm k) : inst2 (KB W E) j p = inst2 W (inst2 E j p) p := by
  simp only [inst2, KB, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- `x ∼ y`. -/
def Rel {k : ℕ} (a b : PTm k) : Fm PTm k := R.subst ![a, b]

/-- The `r`-th list entry `L[r] = E(sel r, p)`. -/
abbrev Lpt {k : ℕ} (r N p : PTm k) : PTm k := inst2 E (sel (KB W E) r N p) p

theorem rel_subst {k m : ℕ} (σ : Fin k → PTm m) (a b : PTm k) :
    (Rel R a b).subst σ = Rel R (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [Rel, Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

theorem subst_sel {k m : ℕ} (σ : Fin k → PTm m) (r N p : PTm k) :
    Syn.subst σ (sel (KB W E) r N p) = sel (KB W E) (Syn.subst σ r) (Syn.subst σ N) (Syn.subst σ p) := by
  simp [sel]

/-- The hypotheses: `W` is a bit, `W` respects `∼`, and `∼` is symmetric. -/
structure PointData : Prop where
  bit : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (x p : PTm k), Δ ⊢[PRAAx] le (inst2 W x p) one
  ext : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {a b p : PTm k}, (Δ ⊢[PRAAx] Rel R a b) →
    (Δ ⊢[PRAAx] inst2 W a p ≐ one) → (Δ ⊢[PRAAx] inst2 W b p ≐ one)
  symm : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {a b : PTm k}, (Δ ⊢[PRAAx] Rel R a b) → (Δ ⊢[PRAAx] Rel R b a)

variable {W E R}

/-- A nonzero bit is one. -/
theorem bit_one {k : ℕ} {Δ : List (Fm PTm k)} {w : PTm k} (hb : Δ ⊢[PRAAx] le w one)
    (hn : Δ ⊢[PRAAx] neg (w ≐ zero)) : Δ ⊢[PRAAx] w ≐ one := by
  refine .orE (zero_or_succ w) (.botE _ (.impE hn.wk Prf.hyp0)) ?_
  have hs : ((w ≐ succ (pred w)) :: Δ) ⊢[PRAAx] w ≐ succ (pred w) := Prf.hyp0
  have lo : ((w ≐ succ (pred w)) :: Δ) ⊢[PRAAx] le one w :=
    le_congr (.eqRefl _) hs.eqSymm (by ipra_le 𝔞 (pred w))
  exact le_antisymm hb.wk lo

/-- Soundness: a list entry equivalent to `x` makes `W(x) = 1`. -/
theorem sound (H : PointData W R) {k : ℕ} {Δ : List (Fm PTm k)} {r N p x : PTm k}
    (hr : Δ ⊢[PRAAx] lt r (rank (KB W E) N p)) (h : Δ ⊢[PRAAx] Rel R (Lpt W E r N p) x) :
    Δ ⊢[PRAAx] inst2 W x p ≐ one := by
  have s := sel_spec (KB W E) hr
  have kept := Prf.andE₁ (Prf.andE₂ s)
  rw [inst2_KB] at kept
  exact H.ext h (bit_one (H.bit _ _) kept)

/-- Completeness at a supplied cover index. -/
theorem complete_at (H : PointData W R) {k : ℕ} {Δ : List (Fm PTm k)} {j N p x : PTm k} (hj : Δ ⊢[PRAAx] lt j N)
    (hR : Δ ⊢[PRAAx] Rel R (inst2 E j p) x) (hW : Δ ⊢[PRAAx] inst2 W x p ≐ one) :
    Δ ⊢[PRAAx] lt (rank (KB W E) j p) (rank (KB W E) N p) ⋏
      Rel R (Lpt W E (rank (KB W E) j p) N p) x := by
  have hWj : Δ ⊢[PRAAx] inst2 W (inst2 E j p) p ≐ one := H.ext (H.symm hR) hW
  have kept : Δ ⊢[PRAAx] neg (inst2 (KB W E) j p ≐ zero) := by
    rw [inst2_KB]
    exact .impI (one_ne_zero _ (hWj.wk.eqSymm.eqTrans Prf.hyp0))
  have sr := sel_rank (KB W E) hj kept
  refine .andI (rank_lt_size (KB W E) hj kept) ?_
  refine Prf.eqSubst R ![inst2 E j p, x] ![Lpt W E (rank (KB W E) j p) N p, x] ?_ hR
  intro i; fin_cases i
  · exact (congrInst2 E sr (.eqRefl p)).eqSymm
  · exact .eqRefl x

/-- Completeness from the cover module as an existential. -/
theorem complete (H : PointData W R) {k : ℕ} {Δ : List (Fm PTm k)} {N p x : PTm k}
    (cover : Δ ⊢[PRAAx] Fm.ex (lt (Syn.var 0) (Syn.shift N) ⋏
      Rel R (inst2 E (Syn.var 0) (Syn.shift p)) (Syn.shift x)))
    (hW : Δ ⊢[PRAAx] inst2 W x p ≐ one) :
    Δ ⊢[PRAAx] Fm.ex (lt (Syn.var 0) (Syn.shift (rank (KB W E) N p)) ⋏
      Rel R (Lpt W E (Syn.var 0) (Syn.shift N) (Syn.shift p)) (Syn.shift x)) := by
  refine .exE cover ?_
  have hW' := hW.shift
  simp only [Fm.shift, Fm.subst_eq, subst_inst2, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at hW'
  let B : Fm PTm (k + 1) := lt (Syn.var 0) (Syn.shift N) ⋏ Rel R (inst2 E (Syn.var 0) (Syn.shift p)) (Syn.shift x)
  have h0 : (B :: Δ.map Fm.shift) ⊢[PRAAx] B := Prf.hyp0
  have c := complete_at (E := E) H (Prf.andE₁ h0) (Prf.andE₂ h0) (hW'.wk (ψ := B))
  rw [Fm.shift, Fm.subst_ex]
  refine .exI (rank (KB W E) (Syn.var 0) (Syn.shift p)) ?_
  rw [Fm.subst_subst]
  have eρ : (fun i => Syn.subst (Syn.inst (rank (KB W E) (Syn.var 0) (Syn.shift p)))
      (Syn.up (fun i => (Syn.var i.succ : PTm (k + 1))) i)) = Syn.repl (rank (KB W E) (Syn.var 0) (Syn.shift p)) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [eρ]
  simp only [Fm.subst_and, subst_lt, rel_subst, subst_inst2, subst_sel, Syn.subst_var, Syn.repl_zero,
    subst_repl_shift]
  have er : Syn.shift (rank (KB W E) N p) = rank (KB W E) (Syn.shift N) (Syn.shift p) := by
    simp [Syn.shift, rank]
  rw [er]
  exact c

end LeanProofs.IPRA.Foundations.PointList
