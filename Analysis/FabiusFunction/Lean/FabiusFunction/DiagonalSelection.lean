import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Find

/-!
# Diagonal selection along eventual families

The diagonalization mechanism of the audits' gauge constructions
(Document 8's flattening lemma `lem:flattening`, Document 7's
`j(k) → ∞` selection): a family of approximations indexed by a *depth*
`j`, each valid *eventually* in the running index `k`, can be composed
into a single sequence in which the depth `j(k)` tends to infinity
while every chosen estimate holds.  This is what defeats the
stabilizing-class obstruction: no fixed depth works, but a slowly
increasing depth does.

Formalized in full abstraction over an arbitrary predicate — the
construction is `φ k = ` the greatest `j` whose activation threshold
`K j` has been passed, with `K j = j + max_{i ≤ j} N i` dominating both
the depth and every eventuality bound.

* `exists_tendsto_atTop_eventually` — the selection principle: from
  `∀ j, ∀ᶠ k, P j k` produce `φ → ∞` with `∀ᶠ k, P (φ k) k`.
* `tendsto_zero_of_eventually_abs_le_comp` — squeeze along a diagonal:
  bounds `|f k| ≤ ε (φ k)` with `ε → 0`, `φ → ∞` force `f → 0`.
* `exists_diagonal_tendsto_zero` — the two combined: per-depth
  estimates `|g j k| ≤ ε j` (eventually in `k`) with `ε j → 0` yield a
  diagonal `k ↦ g (φ k) k` converging to zero — the exact shape of the
  flattening lemma's conclusion `‖log r_k‖ = o(k)` and of its CDF
  discrepancy `sup_z |∫₀ᶻ r_k dμ_k − z| → 0`.
-/

set_option autoImplicit false

open Filter

namespace Fabius

/-- **Diagonal selection principle**: if each depth `j` has its
property `P j k` eventually in `k`, then some depth assignment
`φ : ℕ → ℕ` with `φ k → ∞` satisfies `P (φ k) k` for all large `k`. -/
theorem exists_tendsto_atTop_eventually {P : ℕ → ℕ → Prop}
    (hP : ∀ j, ∀ᶠ k in atTop, P j k) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ ∀ᶠ k in atTop, P (φ k) k := by
  choose N hN using fun j => eventually_atTop.mp (hP j)
  set K : ℕ → ℕ := fun j => j + (Finset.range (j + 1)).sup N
  have hKN : ∀ j, N j ≤ K j := fun j =>
    (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self j))).trans
      (Nat.le_add_left _ _)
  have hKj : ∀ j, j ≤ K j := fun j => Nat.le_add_right _ _
  refine ⟨fun k => Nat.findGreatest (fun j => K j ≤ k) k, ?_, ?_⟩
  · refine tendsto_atTop_atTop.mpr (fun b => ⟨K b, fun k hk => ?_⟩)
    exact Nat.le_findGreatest ((hKj b).trans hk) hk
  · refine eventually_atTop.mpr ⟨K 0, fun k hk => ?_⟩
    have hspec : K (Nat.findGreatest (fun j => K j ≤ k) k) ≤ k :=
      Nat.findGreatest_spec (P := fun j => K j ≤ k) (Nat.zero_le k)
        (show K 0 ≤ k from hk)
    exact hN _ k ((hKN _).trans hspec)

/-- **Squeeze along a diagonal**: if `|f k| ≤ ε (φ k)` eventually,
with `ε → 0` and `φ → ∞`, then `f → 0`. -/
theorem tendsto_zero_of_eventually_abs_le_comp {f ε : ℕ → ℝ} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (hε : Tendsto ε atTop (nhds 0))
    (h : ∀ᶠ k in atTop, |f k| ≤ ε (φ k)) :
    Tendsto f atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (hε.comp hφ)
  simpa only [Real.norm_eq_abs, Function.comp_apply] using h

/-- **The diagonal core of the flattening lemma**: per-depth
approximation errors `|g j k| ≤ ε j` (each eventually in `k`) with
quality `ε j → 0` diagonalize into a single vanishing sequence
`g (φ k) k → 0` along some depth assignment `φ k → ∞`. -/
theorem exists_diagonal_tendsto_zero {g : ℕ → ℕ → ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (nhds 0))
    (hg : ∀ j, ∀ᶠ k in atTop, |g j k| ≤ ε j) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      Tendsto (fun k => g (φ k) k) atTop (nhds 0) := by
  obtain ⟨φ, hφ, hev⟩ := exists_tendsto_atTop_eventually
    (P := fun j k => |g j k| ≤ ε j) hg
  exact ⟨φ, hφ, tendsto_zero_of_eventually_abs_le_comp hφ hε hev⟩

end Fabius
