import CoarseDegrees.Spectrum

/-!
# The dyadic route to the failure of C1

The two routes of `CoarseDegrees.C1` both go through the core-triviality theorems of
Hirschfeldt--Jockusch--Kuyper--Schupp and Jockusch--Schupp.  The dyadic code gives a third,
which uses neither, and which is the route of research reports 03, 04 and Section 6 of the
synthesis.  It rests on the criterion of `CoarseDegrees.Majority`:

* `not_setCoarselyComputable_Rc`: if `A` is not the limit of a computable approximation — that
  is, if `A ≰ᵀ ∅′` — then `R(A)` is not coarsely computable.  A computable coarse description
  would *be* a computable approximation.
* `no_least_of_dyadic`: if in addition `A` is limit-computable in each half of a minimal pair,
  then neither coarse class of `R(A)` has a representative of least Turing degree.  The two
  descriptions supplied by the criterion form the two witnesses of
  `no_least_of_two_witnesses`.

* `exists_not_limitComputable`: a set that is not limit-computable exists, because only
  countably many are (the countability of a lower cone comes from `C:\ProveIt`) while there are
  continuum many sets.

What this file does *not* supply is the minimal pair, which is where the mathematical content
of the route sits; see `CoarseDegrees.Published` for the statement admitted from the literature
and `not_C1_dyadic` for the conclusion.

Everything in this file is proved except the minimal pair itself, which is admitted from the
literature (`exists_minimal_pair_limit`, a consequence of Cooper 1973) with its derivation in
the docstring.
-/

noncomputable section

open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-- **A dyadic code of a non-`Δ⁰₂` set is not coarsely computable.**  A computable coarse
description of `R(A)` is, by the criterion, a computable approximation converging to `A`. -/
theorem not_setCoarselyComputable_Rc {A : Set ℕ} (hA : ¬ LimitComputableIn ∅ A) :
    ¬ SetCoarselyComputable (Rc A) := by
  rintro ⟨C, hC, hCA⟩
  exact hA (limit_of_description (setTuringReducible_of_computablePred hC) hCA)

/-- **The dyadic route.**  If `A` is not limit-computable, but is limit-computable in each of two
sets whose common lower cone is trivial, then neither coarse class of `R(A)` has a representative
of least Turing degree — even when representatives range over all total functions `ℕ → ℕ`. -/
theorem no_least_of_dyadic {A M₀ M₁ : Set ℕ} (hA : ¬ LimitComputableIn ∅ A)
    (h₀ : LimitComputableIn M₀ A) (h₁ : LimitComputableIn M₁ A)
    (hmin : ∀ X : Set ℕ, X ≤ᵀₛ M₀ → X ≤ᵀₛ M₁ → ComputablePred (fun n => n ∈ X)) :
    (¬ ∃ g, IsLeastNC (χ (Rc A)) g) ∧ (¬ ∃ g, IsLeastUC (χ (Rc A)) g) := by
  obtain ⟨D₀, hD₀, hD₀A⟩ := exists_description_of_limit h₀
  obtain ⟨D₁, hD₁, hD₁A⟩ := exists_description_of_limit h₁
  refine no_least_of_two_witnesses
    (fun h => not_setCoarselyComputable_Rc hA (setCoarselyComputable_of_coarselyComputable h))
    (setCoarseEq_iff.mp hD₀A) (setCoarseEq_iff.mp hD₁A) fun g hg₀ hg₁ => ?_
  refine computable_of_graph (hmin (graph g) ?_ ?_)
  · exact (tRed_chi_iff.mp ((graph_tRed g).trans hg₀)).trans hD₀
  · exact (tRed_chi_iff.mp ((graph_tRed g).trans hg₁)).trans hD₁

/-! ## A set that is not limit-computable -/

/-- The limit of the approximation coded by `L`. -/
def limOf (L : Set ℕ) : Set ℕ := {k | ∃ s, ∀ t, s ≤ t → Nat.pair k t ∈ L}

theorem limOf_eq {L A : Set ℕ} (h : ∀ k, ∃ s, ∀ t, s ≤ t → (Nat.pair k t ∈ L ↔ k ∈ A)) :
    limOf L = A := by
  ext k
  obtain ⟨s, hs⟩ := h k
  constructor
  · rintro ⟨s₁, hs₁⟩
    exact (hs (max s s₁) (le_max_left _ _)).mp (hs₁ (max s s₁) (le_max_right _ _))
  · intro hk
    exact ⟨s, fun t ht => (hs t ht).mpr hk⟩

/-- **Not every set is limit-computable.**  The computable sets form a countable lower cone
(`TuringDegrees.lowerConeSets_countable`, from `C:\ProveIt`), each of them determines the limit
of the approximation it codes, and there are continuum many subsets of `ℕ`. -/
theorem exists_not_limitComputable : ∃ A : Set ℕ, ¬ LimitComputableIn ∅ A := by
  by_contra hcon
  push_neg at hcon
  have hsurj : Function.Surjective
      (fun L : {L : Set ℕ // L ≤ᵀₛ (∅ : Set ℕ)} => limOf L.1) := by
    intro A
    obtain ⟨L, hL, hlim⟩ := hcon A
    exact ⟨⟨L, hL⟩, limOf_eq hlim⟩
  haveI : Countable {L : Set ℕ // L ≤ᵀₛ (∅ : Set ℕ)} := lowerConeSets_countable ∅
  haveI : Nonempty {L : Set ℕ // L ≤ᵀₛ (∅ : Set ℕ)} :=
    ⟨⟨∅, RecursiveIn.oracle _ (Set.mem_singleton _)⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat {L : Set ℕ // L ≤ᵀₛ (∅ : Set ℕ)}
  exact Function.cantor_surjective (fun n => limOf (e n).1) (hsurj.comp he)

/-! ## The minimal pair, from the literature -/

/-- **A minimal pair whose jumps both compute `A`.**  This is the only statement the dyadic
route admits, and it is a *consequence* of a published theorem rather than one of its verbatim
statements.

*Source.*  S. B. Cooper, *Minimal degrees and the jump operator*, J. Symb. Log. 38 (1973),
249--271: every Turing degree `≥ 0′` is the jump of a minimal degree.  (Checked against the
journal record on 19 September 2026; see `docs/coarse-degrees/research-plan/validation.txt`.)

*Derivation.*  Put `c₀ = deg(A ⊕ ∅′)` and `c₁ = c₀′`; both are above `0′`, and they are distinct
because the jump is strictly increasing.  Cooper gives minimal degrees `m₀`, `m₁` with
`mᵢ′ = cᵢ`; from `m₀′ ≠ m₁′` we get `m₀ ≠ m₁`, and two distinct minimal degrees form a minimal
pair, because a nonzero degree below a minimal degree *is* that degree.  Finally
`A ≤ᵀ c₀ ≤ᵀ c₁`, so `A ≤ᵀ mᵢ′` for both `i`.

*Why the limit form.*  No jump operator is available in Mathlib or in `C:\ProveIt`, so `A ≤ᵀ Mᵢ′`
is written as limit computability in `Mᵢ`; the two are equivalent by Shoenfield's limit lemma
relativized (Soare, *Recursively Enumerable Sets and Degrees*, Lemma III.3.3).  This is the same
reading of the jump used throughout `CoarseDegrees.Dyadic`. -/
theorem exists_minimal_pair_limit (A : Set ℕ) :
    ∃ M₀ M₁ : Set ℕ, LimitComputableIn M₀ A ∧ LimitComputableIn M₁ A ∧
      ∀ X : Set ℕ, X ≤ᵀₛ M₀ → X ≤ᵀₛ M₁ → ComputablePred (fun n => n ∈ X) := by
  admit

/-- The dyadic route, assembled: there is a set whose dyadic code has no representative of least
Turing degree in either of its coarse classes. -/
theorem exists_dyadic_no_least :
    ∃ A : Set ℕ, (¬ ∃ g, IsLeastNC (χ (Rc A)) g) ∧ (¬ ∃ g, IsLeastUC (χ (Rc A)) g) := by
  obtain ⟨A, hA⟩ := exists_not_limitComputable
  obtain ⟨M₀, M₁, h₀, h₁, hmin⟩ := exists_minimal_pair_limit A
  exact ⟨A, no_least_of_dyadic hA h₀ h₁ hmin⟩

/-- **C1 is false**, third derivation: the dyadic code of a set that is not `Δ⁰₂`.  It shares no
admitted statement with `not_C1` (which uses HJKS, Theorem 4.2) or with `not_C1'` (which uses
JS, Theorem 2.26 and HJKS, Theorem 4.3). -/
theorem not_C1_dyadic : ¬ C1 := by
  obtain ⟨A, hnc, -⟩ := exists_dyadic_no_least
  exact fun h => hnc (h (χ (Rc A)))

/-- **C1Uniform is false**, third derivation. -/
theorem not_C1Uniform_dyadic : ¬ C1Uniform := by
  obtain ⟨A, -, huc⟩ := exists_dyadic_no_least
  exact fun h => huc (h (χ (Rc A)))

end CoarseDegrees
