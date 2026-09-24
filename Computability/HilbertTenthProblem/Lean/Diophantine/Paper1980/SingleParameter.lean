import Diophantine.Paper1980.IndexCode
import Diophantine.Paper1982.RecursivelyEnumerableSystems

/-!
# Adjoining the single-parameter index equation

Jones's 1980 announcement replaces the three positive parameters `z, u, y`
by one parameter `v`, adjoining the equation `indexCode z u y = v` and
quantifying the former parameters as positive unknowns. Injectivity of the
code shows that this preserves the represented set at every coded triple.

The three printed systems therefore represent every recursively enumerable
set on positive inputs using the same single positive parameter. This
construction adds three existential witnesses. It makes no assertion about
a decoding algorithm, a computable enumeration equivalence, or preservation
of the original witness counts.
-/

namespace Jones1980

open Jones1982

/-- Adjoin the index equation and quantify the three former parameters. -/
def SingleParameterSolvable (T : ℕ → ℕ → ℕ → ℕ → Prop) (x v : ℕ) : Prop :=
  ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧
    indexCode z u y = v ∧ T x z u y

/-- Positivity of the last coordinate already makes the code positive. -/
theorem indexCode_pos {z u y : ℕ} (hy : 0 < y) : 0 < indexCode z u y := by
  unfold indexCode
  omega

/-- At the code of a positive triple, adjoining the code equation recovers
exactly the original predicate at that triple. -/
theorem singleParameterSolvable_indexCode_iff
    (T : ℕ → ℕ → ℕ → ℕ → Prop) (x : ℕ) {z u y : ℕ}
    (hz : 0 < z) (hu : 0 < u) (hy : 0 < y) :
    SingleParameterSolvable T x (indexCode z u y) ↔ T x z u y := by
  constructor
  · rintro ⟨z', u', y', hz', hu', hy', hcode, hT⟩
    obtain ⟨hzz, huu, hyy⟩ := indexCode_injective hz' hu' hy' hz hu hy hcode
    simpa only [hzz, huu, hyy] using hT
  · intro hT
    exact ⟨z, u, y, hz, hu, hy, rfl, hT⟩

/-- Every solution of an adjoined-code system has positive index. -/
theorem SingleParameterSolvable.code_pos
    {T : ℕ → ℕ → ℕ → ℕ → Prop} {x v : ℕ}
    (h : SingleParameterSolvable T x v) : 0 < v := by
  obtain ⟨z, u, y, _, _, hy, hcode, _⟩ := h
  rw [← hcode]
  exact indexCode_pos hy

/-- One positive parameter represents a recursively enumerable set by
each of the three printed systems, after adjoining the index equation.
The parameter is fixed before the positive input is quantified. -/
theorem rePred_single_parameter_systems {S : Set ℕ} (hS : REPred S) :
    ∃ v : ℕ, 0 < v ∧ ∀ x : ℕ, 0 < x →
      (x ∈ S ↔ SingleParameterSolvable Theorem1Solvable58 x v) ∧
      (x ∈ S ↔ SingleParameterSolvable Theorem2Solvable58 x v) ∧
      (x ∈ S ↔ SingleParameterSolvable Theorem3Solvable58 x v) := by
  obtain ⟨z, u, y, hz, hu, hy, hsystems⟩ := rePred_printed_systems hS
  refine ⟨indexCode z u y, indexCode_pos hy, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsystems x hx
  exact ⟨h1.trans (singleParameterSolvable_indexCode_iff Theorem1Solvable58 x hz hu hy).symm,
    h2.trans (singleParameterSolvable_indexCode_iff Theorem2Solvable58 x hz hu hy).symm,
    h3.trans (singleParameterSolvable_indexCode_iff Theorem3Solvable58 x hz hu hy).symm⟩

end Jones1980
