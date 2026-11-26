import IPRADerivations.Combinatorics.Stirling
import IPRADerivations.Core.Search
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# No universal PR evaluator, and bounded choice of witnesses

Packet: `foundations/ipra_embedding_framework`, Proposition `prop:no-universal-pr-evaluator` and Lemma
`lem:bounded-choice`.

* `no_universal_evaluator`: for every binary symbol `E`, the unary symbol `d(n) = E(n, n) + 1`
  (`diagB E`) has no index: for every term `e`, `iPRA ⊢ ¬ ∀ n. E(e, n) = d(n)` (at `n = e` this would
  give `E(e, e) = E(e, e) + 1`);
* `least_witness` (`lem:bounded-choice`, first part): for a PR relation `R(x, y) :≡ f(y, x) = 0` the
  least-witness function `ℓ(x, b) = μ y < b. f(y, x) = 0` (with sentinel `b`, `Core/Search`) satisfies
  `ℓ ≤ b`, `ℓ < b → R(x, ℓ)`, `y < ℓ → ¬R(x, y)`, and `R(x, y), y < b → ℓ < b`; the first and last give
  `ℓ < b ↔ ∃ y < b R(x, y)`;
* `witness_list` (second part): one PR list `W = ⟨ℓ_{N−1}, …, ⟨ℓ_0, 0⟩⟩` with
  `ℓ_i = μ y < B(i, x). f(y, ⟨i, x⟩) = 0` (`Stirling.build`) holds a witness for every `i < N` that has
  one: if `y < B(i, x)` and `f(y, ⟨i, x⟩) = 0`, then the entry `nth(W, (N − 1) − i)` is a witness below
  `B(i, x)`. No choice axiom is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.EmbeddingBasics

open_ipra
open LeanProofs.IPRA.Combinatorics.Stirling (build nth_build)
open LeanProofs.IPRA.Combinatorics.Bell (nth monus_monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## No universal evaluator -/

/-- The diagonal symbol `d(n) = E(n, n) + 1`. -/
def diagB (E : PR 2) : PR 1 := PR.comp PR.succ (fun _ => PR.comp E (fun _ => PR.proj 0))

theorem diag_at (E : PR 2) (t : PTm n) : Γ ⊢[PRAAx] app (diagB E) (fun _ => t) ≐ succ (app E ![t, t]) := by
  refine (PRA.comp _ _ _).eqTrans ?_
  refine congrApp PR.succ (fun _ => ?_)
  refine (PRA.comp _ _ _).eqTrans (congrApp E (fun j => ?_))
  fin_cases j <;> exact PRA.proj _ _

/-- `prop:no-universal-pr-evaluator`: no index `e` makes `E(e, ·)` agree with `d = E(n, n) + 1`. -/
theorem no_universal_evaluator (E : PR 2) (e : PTm n) :
    Γ ⊢[PRAAx] neg (Fm.all (app E ![Syn.shift e, var 0] ≐ app (diagB E) (fun _ => var 0))) := by
  refine .impI ?_
  let C := Fm.all (app E ![Syn.shift e, var 0] ≐ app (diagB E) (fun _ => var 0)) :: Γ
  have h : C ⊢[PRAAx] app E ![e, e] ≐ app (diagB E) (fun _ => e) := by
    have h₀ := Prf.allE e (Prf.hyp0 : C ⊢[PRAAx] _)
    have e₁ : (app E ![Syn.shift e, var 0] ≐ app (diagB E) (fun _ => var 0) : Fm PTm (n + 1)).subst (Syn.inst e) =
        (app E ![e, e] ≐ app (diagB E) (fun _ => e)) := by
      simp only [Fm.subst_eq, ConciseIPRA.PTm.subst_app]
      congr 2
      funext j; fin_cases j <;> simp
    rwa [e₁] at h₀
  have loop := h.eqTrans (diag_at E e)
  exact not_succ_le_self _ _ (le_congr (.eqRefl _) loop.eqSymm (le_refl _))

/-! ## Bounded choice -/

section Choice

variable (f : PTm 2)

/-- `lem:bounded-choice`, the least witness `ℓ = μ y < b. f(y, x) = 0`. -/
theorem least_witness (b x y : PTm n) :
    Γ ⊢[PRAAx] le (Search.mu f b x) b ⋏ ((lt (Search.mu f b x) b ⟶ (inst2 f (Search.mu f b x) x ≐ zero)) ⋏
      ((lt y (Search.mu f b x) ⟶ neg (inst2 f y x ≐ zero)) ⋏
      ((inst2 f y x ≐ zero) ⟶ lt y b ⟶ lt (Search.mu f b x) b))) := by
  have s := Search.search_spec (Γ := Γ) (f := f) b y x
  refine .andI (Prf.andE₁ s) (.andI (Prf.andE₁ (Prf.andE₂ s)) (.andI (Prf.andE₂ (Prf.andE₂ s)) ?_))
  refine .impI (.impI ?_)
  exact Prf.andE₁ (Search.search_found (f := f) Prf.hyp1 Prf.hyp0)

/-- The witness body `ℓ_i = μ y < B(i, x). f(y, ⟨i, x⟩) = 0`, over `0 = i`, `1 = x`. -/
abbrev wB (Bd : PTm 2) : PTm 2 := ap2 (Search.muF f) Bd (pairT (var 0) (var 1))

theorem inst2_wB (Bd : PTm 2) (i x : PTm n) :
    inst2 (wB f Bd) i x = Search.mu f (inst2 Bd i x) (pairT i x) := by
  simp [inst2, wB, Search.mu]

/-- `lem:bounded-choice`, the list part: one PR list holds witnesses for all `i ≤ M` that have one. -/
theorem witness_list (Bd : PTm 2) {M i y x : PTm n} (hi : Γ ⊢[PRAAx] le i M)
    (hy : Γ ⊢[PRAAx] lt y (inst2 Bd i x)) (hR : Γ ⊢[PRAAx] inst2 f y (pairT i x) ≐ zero) :
    Γ ⊢[PRAAx] (inst2 f (nth (build (wB f Bd) (succ M) x) (monus M i)) (pairT i x) ≐ zero) ⋏
      lt (nth (build (wB f Bd) (succ M) x) (monus M i)) (inst2 Bd i x) := by
  have hj : Γ ⊢[PRAAx] le (monus M i) M := le_of_eq_add (d := i) (by
    ipra_lc natEq (eq_add_of_le hi))
  have back : Γ ⊢[PRAAx] monus M (monus M i) ≐ i := monus_monus hi
  have nb := (nth_build (wB f Bd) x hj).eqTrans (congrInst2 (wB f Bd) back (.eqRefl _))
  rw [inst2_wB] at nb
  have found := Search.search_found (f := f) (N := inst2 Bd i x) (x := pairT i x) hR hy
  exact .andI ((congrInst2 f nb (.eqRefl _)).eqTrans (Prf.andE₁ (Prf.andE₂ found)))
    (lt_congr nb.eqSymm (.eqRefl _) (Prf.andE₁ found))

end Choice

end LeanProofs.IPRA.Foundations.EmbeddingBasics
