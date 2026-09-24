import CoarseDegrees.Published
import CoarseDegrees.GenericDensity

/-!
# The negative answer to C1

`C1` says that every nonuniform coarse-equivalence class of total functions contains a
representative of least Turing degree.  It is false, and so is its uniform analogue.

The argument is the literature route recorded in Section 1 of the synthesis and in all nine
research reports: every coarse description of `X` lies in the coarse class of `X`, so a least
representative is computable from all of them; if the core of `X` is trivial it is therefore
computable, and then `X` would be coarsely computable.  The Lean proof makes explicit the two
steps that the informal deduction passes over:

* C1 quantifies over arbitrary total *functions* `g : ℕ → ℕ`, whereas the core consists of
  *sets*; the passage is by graph coding (`computable_of_core_trivial`);
* a coarse description of `χ X` may be numerical, whereas coarse computability of a set asks
  for a computable *set*; the passage is binary normalization
  (`setCoarselyComputable_of_coarselyComputable`).

Two witnesses are given, by disjoint sets of admitted published theorems.  Route G uses any
1-generic set; its only admitted ingredient is Theorem 4.2 of Hirschfeldt--Jockusch--Kuyper--
Schupp, since the existence of 1-generic sets and the fact that they are not coarsely computable
are proved in `CoarseDegrees.Generic` and `CoarseDegrees.GenericDensity`.  Route C uses a c.e. set
and two admitted theorems.
-/

noncomputable section

open scoped Classical
open TuringDegrees

namespace CoarseDegrees

/-- The general criterion: a set with trivial core that is not coarsely computable has no
representative of least Turing degree in its nonuniform coarse class, nor in its uniform one,
even when representatives range over all total functions `ℕ → ℕ`. -/
theorem no_least_of_core_trivial {X : Set ℕ}
    (hcore : ∀ A ∈ core X, ComputablePred (fun n => n ∈ A))
    (hX : ¬ SetCoarselyComputable X) :
    (¬ ∃ g, IsLeastNC (χ X) g) ∧ (¬ ∃ g, IsLeastUC (χ X) g) :=
  no_least_of_trivial_core
    (fun h => hX (setCoarselyComputable_of_coarselyComputable h))
    (computable_of_core_trivial hcore)

/-- Route G: the coarse classes of a 1-generic set have no least Turing degree. -/
theorem OneGeneric.no_least {X : Set ℕ} (hX : OneGeneric X) :
    (¬ ∃ g, IsLeastNC (χ X) g) ∧ (¬ ∃ g, IsLeastUC (χ X) g) :=
  no_least_of_core_trivial (fun _ hA => hX.core_trivial hA) hX.not_setCoarselyComputable

/-- Route C: there is a c.e. set whose coarse classes have no least Turing degree. -/
theorem exists_re_no_least :
    ∃ X : Set ℕ, REPred (fun n => n ∈ X) ∧
      (¬ ∃ g, IsLeastNC (χ X) g) ∧ (¬ ∃ g, IsLeastUC (χ X) g) := by
  obtain ⟨X, hre, hgen, hnc⟩ := exists_re_genericallyComputable_not_coarselyComputable
  exact ⟨X, hre, no_least_of_core_trivial (fun _ hA => hgen.core_trivial hA) hnc⟩

/-- **C1 is false** (via a 1-generic set). -/
theorem not_C1 : ¬ C1 := by
  obtain ⟨X, hX⟩ := exists_oneGeneric
  intro h
  exact hX.no_least.1 (h (χ X))

/-- **C1 is false**, second derivation (via a c.e. set); it shares no admitted statement with
`not_C1`. -/
theorem not_C1' : ¬ C1 := by
  obtain ⟨X, -, hX, -⟩ := exists_re_no_least
  intro h
  exact hX (h (χ X))

/-- The uniform analogue of C1 is false as well. -/
theorem not_C1Uniform : ¬ C1Uniform := by
  obtain ⟨X, hX⟩ := exists_oneGeneric
  intro h
  exact hX.no_least.2 (h (χ X))

/-- The uniform analogue of C1 is false, second derivation. -/
theorem not_C1Uniform' : ¬ C1Uniform := by
  obtain ⟨X, -, -, hX⟩ := exists_re_no_least
  intro h
  exact hX (h (χ X))

/-- The counterexample can be taken binary and computably enumerable. -/
theorem exists_binary_counterexample :
    ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ ¬ ∃ g, IsLeastNC f g := by
  obtain ⟨X, -, hX, -⟩ := exists_re_no_least
  refine ⟨χ X, fun n => ?_, hX⟩
  by_cases hn : n ∈ X <;> simp [characteristicValue, hn]

end CoarseDegrees
