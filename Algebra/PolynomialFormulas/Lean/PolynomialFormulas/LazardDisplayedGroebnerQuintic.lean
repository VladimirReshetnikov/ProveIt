import PolynomialFormulas.LazardInvariantArtinModuleBasis
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Tactic

/-!
# Lazard's displayed triangular relations in degree five

This file records the literal `d = 5` specialization of Lemma 1 in Lazard's
paper.  It is deliberately labelled as a quintic specialization: the general
Artin-basis theorem already used elsewhere proves the quotient substance in
all degrees, but it is not silently advertised here as the paper's literal
reduced-Gröbner-basis computation.

The coefficient variables `e₁,…,e₅` form the inner multivariate
polynomial ring and the root variables `x₀,…,x₄` form the outer one.
The five displayed relations are expanded versions of

`Cₖ⁽ⁱ⁺¹⁾ - e₁ Cₖ₋₁⁽ⁱ⁺¹⁾ + ⋯ + (-1)ᵏ eₖ`,  where `k = 5 - i`.

Two explicit change-of-generator matrices prove that these relations generate
exactly Lazard's ideal `( σᵢ - eᵢ )`.  The final Artin-coordinate clause is
explicitly a statement after the specialization `eᵢ := σᵢ`; it is not passed
off as uniqueness of remainder for an arbitrary element of the formal
two-level quotient.
-/

namespace LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerQuintic

open scoped BigOperators
open scoped MonomialOrder
open Finset MvPolynomial

set_option autoImplicit false

noncomputable section

open LazardInvariantArtinBasis
open LazardInvariantArtinModuleBasis

abbrev Coeff := MvPolynomial (Fin 5) ℚ
abbrev Ambient := MvPolynomial (Fin 5) Coeff
abbrev RootRing := MvPolynomial (Fin 5) ℚ
abbrev Index := ArtinIndex 5

local instance (priority := 3000) displayedSymmetricRootAlgebra :
    Algebra (MvPolynomial.symmetricSubalgebra (Fin 5) ℚ) RootRing :=
  (MvPolynomial.symmetricSubalgebra (Fin 5) ℚ).val.toRingHom.toAlgebra

local instance (priority := 3000) displayedSymmetricRootModule :
    Module (MvPolynomial.symmetricSubalgebra (Fin 5) ℚ) RootRing :=
  Algebra.toModule

/-- The `i`th root variable. -/
def x (i : Fin 5) : Ambient := X i

/-- The paper's `e_(i+1)`, embedded as an outer coefficient. -/
def e (i : Fin 5) : Ambient := C (X i : Coeff)

/-- The literal five displayed members of Lazard's `J`, in expanded form. -/
def displayedJ : Fin 5 → Ambient := ![
  x 0 ^ 5 - e 0 * x 0 ^ 4 + e 1 * x 0 ^ 3 - e 2 * x 0 ^ 2 + e 3 * x 0 - e 4,
  (x 0 ^ 4 + x 0 ^ 3 * x 1 + x 0 ^ 2 * x 1 ^ 2 + x 0 * x 1 ^ 3 + x 1 ^ 4) -
    e 0 * (x 0 ^ 3 + x 0 ^ 2 * x 1 + x 0 * x 1 ^ 2 + x 1 ^ 3) +
    e 1 * (x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2) - e 2 * (x 0 + x 1) + e 3,
  (x 0 ^ 3 + x 0 ^ 2 * x 1 + x 0 ^ 2 * x 2 + x 0 * x 1 ^ 2 +
      x 0 * x 1 * x 2 + x 0 * x 2 ^ 2 + x 1 ^ 3 + x 1 ^ 2 * x 2 +
      x 1 * x 2 ^ 2 + x 2 ^ 3) -
    e 0 * (x 0 ^ 2 + x 0 * x 1 + x 0 * x 2 + x 1 ^ 2 +
      x 1 * x 2 + x 2 ^ 2) + e 1 * (x 0 + x 1 + x 2) - e 2,
  (x 0 ^ 2 + x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 ^ 2 +
      x 1 * x 2 + x 1 * x 3 + x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2) -
    e 0 * (x 0 + x 1 + x 2 + x 3) + e 1,
  x 0 + x 1 + x 2 + x 3 + x 4 - e 0]

/-- The paper's original generators `σ_(i+1) - e_(i+1)`. -/
def vietaRelation (i : Fin 5) : Ambient :=
  esymm (Fin 5) Coeff (i.1 + 1) - e i

/-- Coefficients expressing every displayed `J` relation in the Vieta
generators. -/
def jToVieta : Fin 5 → Fin 5 → Ambient := ![
  ![x 0 ^ 4, -x 0 ^ 3, x 0 ^ 2, -x 0, 1],
  ![(x 0 + x 1) * (x 0 ^ 2 + x 1 ^ 2),
    -(x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2), x 0 + x 1, -1, 0],
  ![x 0 ^ 2 + x 0 * x 1 + x 0 * x 2 + x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2,
    -(x 0 + x 1 + x 2), 1, 0, 0],
  ![x 0 + x 1 + x 2 + x 3, -1, 0, 0, 0],
  ![1, 0, 0, 0, 0]]

/-- Coefficients expressing every Vieta generator in the displayed `J`
relations. -/
def vietaToJ : Fin 5 → Fin 5 → Ambient := ![
  ![0, 0, 0, 0, 1],
  ![0, 0, 0, -1, x 0 + x 1 + x 2 + x 3],
  ![0, 0, 1, -(x 0 + x 1 + x 2),
    x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3],
  ![0, -1, x 0 + x 1,
    -(x 0 * x 1 + x 0 * x 2 + x 1 * x 2),
    x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 2 * x 3 + x 1 * x 2 * x 3],
  ![1, -x 0, x 0 * x 1, -(x 0 * x 1 * x 2), x 0 * x 1 * x 2 * x 3]]

private lemma fin5_powersetCard_one :
    Finset.powersetCard 1 ({0, 1, 2, 3, 4} : Finset (Fin 5)) =
      {{0}, {1}, {2}, {3}, {4}} := by
  decide

private lemma fin5_powersetCard_two :
    Finset.powersetCard 2 ({0, 1, 2, 3, 4} : Finset (Fin 5)) =
      {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4},
        {2, 3}, {2, 4}, {3, 4}} := by
  decide

private lemma fin5_powersetCard_three :
    Finset.powersetCard 3 ({0, 1, 2, 3, 4} : Finset (Fin 5)) =
      {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4},
        {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}} := by
  decide

private lemma fin5_powersetCard_four :
    Finset.powersetCard 4 ({0, 1, 2, 3, 4} : Finset (Fin 5)) =
      {{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4},
        {1, 2, 3, 4}} := by
  decide

private lemma fin5_powersetCard_five :
    Finset.powersetCard 5 ({0, 1, 2, 3, 4} : Finset (Fin 5)) =
      {{0, 1, 2, 3, 4}} := by
  decide

theorem displayedJ_eq_vieta_combination (i : Fin 5) :
    displayedJ i = ∑ k : Fin 5, jToVieta i k * vietaRelation k := by
  have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by
    decide
  fin_cases i <;>
    simp +decide [displayedJ, jToVieta, vietaRelation, x, e,
      MvPolynomial.esymm, huniv, fin5_powersetCard_one,
      fin5_powersetCard_two, fin5_powersetCard_three,
      fin5_powersetCard_four, fin5_powersetCard_five] <;>
    ring

theorem vietaRelation_eq_displayedJ_combination (i : Fin 5) :
    vietaRelation i = ∑ k : Fin 5, vietaToJ i k * displayedJ k := by
  have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by
    decide
  fin_cases i <;>
    simp +decide [displayedJ, vietaToJ, vietaRelation, x, e,
      MvPolynomial.esymm, huniv, fin5_powersetCard_one,
      fin5_powersetCard_two, fin5_powersetCard_three,
      fin5_powersetCard_four, fin5_powersetCard_five] <;>
    ring

/-- Lazard's ideal `I = (σ₁-e₁,…,σ₅-e₅)`. -/
def vietaIdeal : Ideal Ambient := Ideal.span (Set.range vietaRelation)

/-- The ideal generated by the literal displayed family `J`. -/
def displayedIdeal : Ideal Ambient := Ideal.span (Set.range displayedJ)

lemma vietaRelation_mem_vietaIdeal (i : Fin 5) :
    vietaRelation i ∈ vietaIdeal :=
  Ideal.subset_span (Set.mem_range_self i)

lemma displayedJ_mem_displayedIdeal (i : Fin 5) :
    displayedJ i ∈ displayedIdeal :=
  Ideal.subset_span (Set.mem_range_self i)

theorem displayedIdeal_eq_vietaIdeal : displayedIdeal = vietaIdeal := by
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    rw [displayedJ_eq_vieta_combination]
    exact Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ (vietaRelation_mem_vietaIdeal k)
  · apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    rw [vietaRelation_eq_displayedJ_combination]
    exact Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ (displayedJ_mem_displayedIdeal k)

/-- The displayed leading exponent `x_i^(5-i)`. -/
def paperLeadingExponent (i : Fin 5) : Fin 5 →₀ ℕ :=
  Finsupp.single i (5 - i.1)

/-- Lazard's ordering condition, specialized to five root variables: compare
root degree first and, at equal degree, compare from `x₄` back to `x₀`.
Coefficient variables are scalars and therefore do not enter this comparison. -/
def PaperLT (a b : Fin 5 →₀ ℕ) : Prop :=
  a.degree < b.degree ∨
    (a.degree = b.degree ∧
      ∃ i : Fin 5, a i < b i ∧ ∀ j : Fin 5, i < j → a j = b j)

instance paperLTDecidable (a b : Fin 5 →₀ ℕ) : Decidable (PaperLT a b) :=
  by
    unfold PaperLT
    infer_instance

/-- The actual monomial order behind `PaperLT`: degree-lexicographic order
with the root-variable order reversed, so `x₄ > x₃ > ⋯ > x₀`. -/
noncomputable def paperMonomialOrder : MonomialOrder (Fin 5) :=
  MonomialOrder.degLex (σ := OrderDual (Fin 5))

theorem paperLT_iff_orderLT (a b : Fin 5 →₀ ℕ) :
    PaperLT a b ↔ a ≺[paperMonomialOrder] b := by
  change PaperLT a b ↔
    @LT.lt (DegLex ((OrderDual (Fin 5)) →₀ ℕ)) inferInstance
      (toDegLex a) (toDegLex b)
  rw [Finsupp.DegLex.lt_iff]
  simp only [ofDegLex_toDegLex, Finsupp.Lex.lt_iff, ofLex_toLex]
  constructor
  · rintro (hdegree | ⟨hdegree, i, hi, htail⟩)
    · exact Or.inl hdegree
    · exact Or.inr ⟨hdegree, i, fun j hj ↦ htail j hj, hi⟩
  · rintro (hdegree | ⟨hdegree, i, htail, hi⟩)
    · exact Or.inl hdegree
    · exact Or.inr ⟨hdegree, i, hi, fun j hj ↦ htail j hj⟩

private abbrev ListedExponent := Fin 5 →₀ ℕ
private abbrev ListedTerm := ListedExponent × Coeff

private def exp5 (a0 a1 a2 a3 a4 : ℕ) : ListedExponent :=
  0 + Finsupp.single 0 a0 + Finsupp.single 1 a1 +
    Finsupp.single 2 a2 + Finsupp.single 3 a3 + Finsupp.single 4 a4

private theorem monomial_exp5 (a0 a1 a2 a3 a4 : ℕ) (c : Coeff) :
    monomial (exp5 a0 a1 a2 a3 a4) c =
      C c * x 0 ^ a0 * x 1 ^ a1 * x 2 ^ a2 * x 3 ^ a3 * x 4 ^ a4 := by
  unfold exp5 x
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single]
  rfl

private def sparseSum : List ListedTerm → Ambient
  | [] => 0
  | (d, c) :: ts => monomial d c + sparseSum ts

private theorem mem_map_fst_of_mem_support_sparseSum
    (ts : List ListedTerm) {a : ListedExponent}
    (ha : a ∈ (sparseSum ts).support) : a ∈ ts.map Prod.fst := by
  induction ts with
  | nil => simpa [sparseSum] using ha
  | cons t ts ih =>
      change a ∈ (monomial t.1 t.2 + sparseSum ts).support at ha
      rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with ht | hts
      · have hat : a = t.1 :=
          Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
        simp [hat]
      · exact List.mem_cons_of_mem _ (ih hts)

private theorem coeff_sparseSum_eq_zero_of_not_mem
    (ts : List ListedTerm) (a : ListedExponent)
    (ha : a ∉ ts.map Prod.fst) : coeff a (sparseSum ts) = 0 := by
  induction ts with
  | nil => simp [sparseSum]
  | cons t ts ih =>
      have ht : t.1 ≠ a := by
        intro h
        exact ha (by simp [h])
      have hts : a ∉ ts.map Prod.fst := by
        intro h
        exact ha (List.mem_cons_of_mem _ h)
      simp [sparseSum, ht, ih hts]

private def displayedTailTerms : Fin 5 → List ListedTerm := ![
  [(exp5 4 0 0 0 0, -(X 0 : Coeff)),
   (exp5 3 0 0 0 0,  (X 1 : Coeff)),
   (exp5 2 0 0 0 0, -(X 2 : Coeff)),
   (exp5 1 0 0 0 0,  (X 3 : Coeff)),
   (exp5 0 0 0 0 0, -(X 4 : Coeff))],
  [(exp5 4 0 0 0 0, 1), (exp5 3 1 0 0 0, 1),
   (exp5 2 2 0 0 0, 1), (exp5 1 3 0 0 0, 1),
   (exp5 3 0 0 0 0, -(X 0 : Coeff)),
   (exp5 2 1 0 0 0, -(X 0 : Coeff)),
   (exp5 1 2 0 0 0, -(X 0 : Coeff)),
   (exp5 0 3 0 0 0, -(X 0 : Coeff)),
   (exp5 2 0 0 0 0,  (X 1 : Coeff)),
   (exp5 1 1 0 0 0,  (X 1 : Coeff)),
   (exp5 0 2 0 0 0,  (X 1 : Coeff)),
   (exp5 1 0 0 0 0, -(X 2 : Coeff)),
   (exp5 0 1 0 0 0, -(X 2 : Coeff)),
   (exp5 0 0 0 0 0,  (X 3 : Coeff))],
  [(exp5 3 0 0 0 0, 1), (exp5 2 1 0 0 0, 1),
   (exp5 2 0 1 0 0, 1), (exp5 1 2 0 0 0, 1),
   (exp5 1 1 1 0 0, 1), (exp5 1 0 2 0 0, 1),
   (exp5 0 3 0 0 0, 1), (exp5 0 2 1 0 0, 1),
   (exp5 0 1 2 0 0, 1),
   (exp5 2 0 0 0 0, -(X 0 : Coeff)),
   (exp5 1 1 0 0 0, -(X 0 : Coeff)),
   (exp5 1 0 1 0 0, -(X 0 : Coeff)),
   (exp5 0 2 0 0 0, -(X 0 : Coeff)),
   (exp5 0 1 1 0 0, -(X 0 : Coeff)),
   (exp5 0 0 2 0 0, -(X 0 : Coeff)),
   (exp5 1 0 0 0 0,  (X 1 : Coeff)),
   (exp5 0 1 0 0 0,  (X 1 : Coeff)),
   (exp5 0 0 1 0 0,  (X 1 : Coeff)),
   (exp5 0 0 0 0 0, -(X 2 : Coeff))],
  [(exp5 2 0 0 0 0, 1), (exp5 1 1 0 0 0, 1),
   (exp5 1 0 1 0 0, 1), (exp5 1 0 0 1 0, 1),
   (exp5 0 2 0 0 0, 1), (exp5 0 1 1 0 0, 1),
   (exp5 0 1 0 1 0, 1), (exp5 0 0 2 0 0, 1),
   (exp5 0 0 1 1 0, 1),
   (exp5 1 0 0 0 0, -(X 0 : Coeff)),
   (exp5 0 1 0 0 0, -(X 0 : Coeff)),
   (exp5 0 0 1 0 0, -(X 0 : Coeff)),
   (exp5 0 0 0 1 0, -(X 0 : Coeff)),
   (exp5 0 0 0 0 0,  (X 1 : Coeff))],
  [(exp5 1 0 0 0 0, 1), (exp5 0 1 0 0 0, 1),
   (exp5 0 0 1 0 0, 1), (exp5 0 0 0 1 0, 1),
   (exp5 0 0 0 0 0, -(X 0 : Coeff))]
]

private def displayedTerms (i : Fin 5) : List ListedTerm :=
  (paperLeadingExponent i, 1) :: displayedTailTerms i

private theorem monomial_paperLeadingExponent (i : Fin 5) :
    monomial (paperLeadingExponent i) (1 : Coeff) = x i ^ (5 - i.1) := by
  simp [paperLeadingExponent, x, MvPolynomial.X_pow_eq_monomial]

private theorem displayedJ_eq_sparseSum (i : Fin 5) :
    displayedJ i = sparseSum (displayedTerms i) := by
  fin_cases i <;>
    simp [displayedJ, displayedTerms, displayedTailTerms, sparseSum,
      monomial_exp5, monomial_paperLeadingExponent, x, e] <;>
    ring

private theorem leading_not_mem_displayedTailTerms (i : Fin 5) :
    paperLeadingExponent i ∉ (displayedTailTerms i).map Prod.fst := by
  fin_cases i <;>
    simp [displayedTailTerms, paperLeadingExponent, exp5,
      Finsupp.ext_iff, Fin.forall_fin_succ]

private theorem displayedTailTerms_paperLT (i : Fin 5) :
    (displayedTailTerms i).Forall
      (fun t => PaperLT t.1 (paperLeadingExponent i)) := by
  fin_cases i <;>
    simp [displayedTailTerms, PaperLT, paperLeadingExponent, exp5,
      Finsupp.degree_eq_sum, Fin.sum_univ_succ,
      Fin.exists_fin_succ, Fin.forall_fin_succ]

private theorem displayedTailTerms_reduced (i : Fin 5) :
    (displayedTailTerms i).Forall
      (fun t => ∀ j : Fin 5, ¬ paperLeadingExponent j ≤ t.1) := by
  fin_cases i <;>
    simp [displayedTailTerms, paperLeadingExponent, exp5,
      Finsupp.single_le_iff, Fin.forall_fin_succ]

private theorem property_of_mem_map_fst
    {P : ListedExponent → Prop} {ts : List ListedTerm}
    (hP : List.Forall (fun t => P t.1) ts)
    {a : ListedExponent} (ha : a ∈ ts.map Prod.fst) : P a := by
  rcases List.mem_map.mp ha with ⟨t, ht, hta⟩
  rw [← hta]
  exact (List.forall_iff_forall_mem.mp hP) t ht

/-- The coefficient and strict-dominance facts which say that the literal
leading monomial of `J_i` is `x_i^(5-i)`. -/
theorem displayedJ_leading_data (i : Fin 5) :
    coeff (paperLeadingExponent i) (displayedJ i) = 1 ∧
      ∀ a ∈ (displayedJ i).support,
        a ≠ paperLeadingExponent i → PaperLT a (paperLeadingExponent i) := by
  classical
  constructor
  · rw [displayedJ_eq_sparseSum]
    change coeff (paperLeadingExponent i)
      (monomial (paperLeadingExponent i) 1 +
        sparseSum (displayedTailTerms i)) = 1
    have hzero : coeff (paperLeadingExponent i)
        (sparseSum (displayedTailTerms i)) = 0 :=
      coeff_sparseSum_eq_zero_of_not_mem _ _
        (leading_not_mem_displayedTailTerms i)
    simp [hzero]
  · intro a ha hne
    rw [displayedJ_eq_sparseSum] at ha
    have hmem := mem_map_fst_of_mem_support_sparseSum _ ha
    change a ∈ paperLeadingExponent i ::
      (displayedTailTerms i).map Prod.fst at hmem
    rcases List.mem_cons.mp hmem with hlead | htail
    · exact (hne hlead).elim
    · exact property_of_mem_map_fst
        (P := fun d => PaperLT d (paperLeadingExponent i))
        (displayedTailTerms_paperLT i) htail

/-- Remove the displayed monic leading term. -/
def displayedTail (i : Fin 5) : Ambient :=
  displayedJ i - monomial (paperLeadingExponent i) 1

private theorem displayedTail_eq_sparseSum (i : Fin 5) :
    displayedTail i = sparseSum (displayedTailTerms i) := by
  rw [displayedTail, displayedJ_eq_sparseSum]
  change (monomial (paperLeadingExponent i) 1 +
      sparseSum (displayedTailTerms i)) -
    monomial (paperLeadingExponent i) 1 = sparseSum (displayedTailTerms i)
  ring

/-- No monomial in any displayed tail is divisible by a displayed leading
monomial.  Together with `displayedJ_leading_data`, this is the literal
"monic and reduced tails" part of the reduced-Gröbner certificate. -/
theorem displayedJ_reduced_tails (i : Fin 5) :
    ∀ a ∈ (displayedTail i).support, ∀ j : Fin 5,
      ¬ paperLeadingExponent j ≤ a := by
  classical
  intro a ha j
  rw [displayedTail_eq_sparseSum] at ha
  have hmem := mem_map_fst_of_mem_support_sparseSum (displayedTailTerms i) ha
  exact property_of_mem_map_fst
    (P := fun d => ∀ j : Fin 5, ¬ paperLeadingExponent j ≤ d)
    (displayedTailTerms_reduced i) hmem j

/-- The degree selected by the actual paper monomial order is the displayed
power `x_i^(5-i)`. -/
theorem paperMonomialOrder_degree_displayedJ (i : Fin 5) :
    paperMonomialOrder.degree (displayedJ i) = paperLeadingExponent i := by
  apply paperMonomialOrder.toSyn.injective
  apply le_antisymm
  · rw [paperMonomialOrder.degree_le_iff]
    intro a ha
    by_cases hai : a = paperLeadingExponent i
    · subst a
      exact le_rfl
    · exact le_of_lt ((paperLT_iff_orderLT a (paperLeadingExponent i)).1
        ((displayedJ_leading_data i).2 a ha hai))
  · apply paperMonomialOrder.le_degree
    rw [MvPolynomial.mem_support_iff, (displayedJ_leading_data i).1]
    exact one_ne_zero

theorem paperMonomialOrder_leadingCoeff_displayedJ (i : Fin 5) :
    paperMonomialOrder.leadingCoeff (displayedJ i) = 1 := by
  rw [MonomialOrder.leadingCoeff,
    paperMonomialOrder_degree_displayedJ,
    (displayedJ_leading_data i).1]

/-- Division in the full formal coefficient/root polynomial ring.  Unlike
`realize_normalCoordinates`, this theorem applies before specializing the
formal `eᵢ`.  It gives a remainder supported on standard monomials; the
separate Gröbner argument is what upgrades this existence statement to
uniqueness modulo the generated ideal. -/
theorem exists_standard_formal_remainder (p : Ambient) :
    ∃ (g : Fin 5 →₀ Ambient) (r : Ambient),
      p = Finsupp.linearCombination Ambient displayedJ g + r ∧
      (∀ i, paperMonomialOrder.degree (displayedJ i * g i)
        ≼[paperMonomialOrder] paperMonomialOrder.degree p) ∧
      (∀ a ∈ r.support, ∀ i : Fin 5,
        ¬ paperLeadingExponent i ≤ a) := by
  obtain ⟨g, r, hp, hg, hr⟩ := paperMonomialOrder.div
    (b := displayedJ) (fun i => by
      rw [paperMonomialOrder_leadingCoeff_displayedJ]
      exact isUnit_one) p
  refine ⟨g, r, hp, hg, ?_⟩
  intro a ha i
  simpa [paperMonomialOrder_degree_displayedJ] using hr a ha i

/-- Standard exponents are exactly the exponent vectors not divisible by a
displayed leading monomial. -/
theorem standardExponent_iff (a : Fin 5 →₀ ℕ) :
    (∀ i : Fin 5, a i < 5 - i.1) ↔
      ∀ i : Fin 5, ¬ paperLeadingExponent i ≤ a := by
  constructor <;> intro h i
  · intro hi
    have hlt := h i
    have hle := hi i
    simp [paperLeadingExponent] at hle
    have hii := i.isLt
    omega
  · have hi := h i
    have hi' : a i + i.1 < 5 := by
      simpa [paperLeadingExponent, Finsupp.single_le_iff] using hi
    have hii := i.isLt
    omega

/-- The direct elementary-symmetric coordinate ring used by the paper. -/
def coefficientEquiv : Coeff ≃ₐ[ℚ]
    MvPolynomial.symmetricSubalgebra (Fin 5) ℚ :=
  MvPolynomial.esymmAlgEquiv (Fin 5) ℚ (by simp)

/-- Specialize the formal coefficient `e_(i+1)` to the actual elementary
symmetric polynomial `σ_(i+1)` in the five root variables. -/
def coefficientSpecialization : Coeff →ₐ[ℚ] RootRing :=
  (MvPolynomial.symmetricSubalgebra (Fin 5) ℚ).val.comp
    coefficientEquiv.toAlgHom

/-- The quotient specialization from the two-level formal polynomial ring to
the root polynomial ring.  It fixes every root variable and sends the formal
coefficient variables to the corresponding elementary symmetric
polynomials. -/
def formalSpecialization : Ambient →+* RootRing :=
  MvPolynomial.eval₂Hom coefficientSpecialization.toRingHom
    (fun i => MvPolynomial.X i)

@[simp]
theorem formalSpecialization_C (c : Coeff) :
    formalSpecialization (C c) = coefficientSpecialization c := by
  simp [formalSpecialization]

@[simp]
theorem formalSpecialization_X (i : Fin 5) :
    formalSpecialization (X i) = (X i : RootRing) := by
  simp [formalSpecialization]

/-- A formal polynomial is standard when none of its monomials is divisible
by one of the five displayed leading monomials. -/
def IsStandardFormal (p : Ambient) : Prop :=
  ∀ d ∈ p.support, ∀ i : Fin 5, d i < 5 - i.1

/-- Turn a standard exponent vector back into its Artin staircase index. -/
def artinIndexOfStandard (d : Fin 5 →₀ ℕ)
    (h : ∀ i : Fin 5, d i < 5 - i.1) : Index :=
  fun i => ⟨d i, h i⟩

@[simp]
theorem artinExponent_artinIndexOfStandard (d : Fin 5 →₀ ℕ)
    (h : ∀ i : Fin 5, d i < 5 - i.1) :
    artinExponent (artinIndexOfStandard d h) = d := by
  ext i
  simp [artinIndexOfStandard]

theorem artinExponent_injective :
    Function.Injective (artinExponent : Index → Fin 5 →₀ ℕ) := by
  intro a b hab
  funext i
  apply Fin.ext
  simpa using congrArg (fun d => d i) hab

/-- A formal Artin coordinate family, realized with the sign occurring in
the recursively constructed Artin basis. -/
def realizeFormalCoordinates (c : Index → Coeff) : Ambient :=
  ∑ a : Index, monomial (artinExponent a)
    (((-1 : Coeff) ^ artinDegree a) * c a)

/-- Read the signed Artin coordinate at a standard exponent.  The same sign
appears twice in a round trip and hence cancels. -/
def formalCoordinates (p : Ambient) (a : Index) : Coeff :=
  ((-1 : Coeff) ^ artinDegree a) * coeff (artinExponent a) p

/-- Canonical Artin coordinates, transported back from symmetric
polynomials to the formal variables `e₁,…,e₅`. -/
def normalCoordinates (p : RootRing) : Index → Coeff :=
  fun a => (coefficientEquiv.symm
    ((symmetricArtinBasis ℚ 5).equivFun p a))

/-- Evaluate an arbitrary family of formal Artin coordinates.  The basis
vectors are the signed staircase monomials constructed by the ordered-root
tower; their exponents are the standard Artin exponents. -/
def realizeCoordinates (c : Index → Coeff) : RootRing :=
  (symmetricArtinBasis ℚ 5).equivFun.symm
    (fun a => coefficientEquiv (c a))

theorem realize_normalCoordinates (p : RootRing) :
    realizeCoordinates (normalCoordinates p) = p := by
  unfold realizeCoordinates normalCoordinates
  rw [show
    (fun a => coefficientEquiv
      (coefficientEquiv.symm ((symmetricArtinBasis ℚ 5).equivFun p a))) =
        (symmetricArtinBasis ℚ 5).equivFun p by
      funext a
      exact coefficientEquiv.apply_symm_apply _]
  exact (symmetricArtinBasis ℚ 5).equivFun.symm_apply_apply p

theorem normalCoordinates_unique (p : RootRing) (c : Index → Coeff)
    (h : realizeCoordinates c = p) : c = normalCoordinates p := by
  have h' : (fun a => coefficientEquiv (c a)) =
      (symmetricArtinBasis ℚ 5).equivFun p := by
    apply (symmetricArtinBasis ℚ 5).equivFun.symm.injective
    change (symmetricArtinBasis ℚ 5).equivFun.symm
        (fun a => coefficientEquiv (c a)) =
      (symmetricArtinBasis ℚ 5).equivFun.symm
        ((symmetricArtinBasis ℚ 5).equivFun p)
    exact h.trans
      ((symmetricArtinBasis ℚ 5).equivFun.symm_apply_apply p).symm
  funext a
  apply coefficientEquiv.injective
  simpa [normalCoordinates] using congrFun h' a

/-- Every Artin coordinate has precisely the standard exponent bounds forced
by the five leading monomials. -/
theorem normal_index_is_standard (a : Index) (i : Fin 5) :
    artinExponent a i < 5 - i.1 := by
  simpa using (a i).2

theorem coeff_realizeFormalCoordinates (c : Index → Coeff) (a : Index) :
    coeff (artinExponent a) (realizeFormalCoordinates c) =
      ((-1 : Coeff) ^ artinDegree a) * c a := by
  classical
  simp only [realizeFormalCoordinates, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [artinExponent_injective.eq_iff, hba]
  · simp

/-- A standard formal polynomial is recovered from its signed Artin
coordinates.  This is the missing formal-`e` statement, before any
specialization to actual elementary symmetric polynomials. -/
theorem realize_formalCoordinates_of_standard (p : Ambient)
    (hp : IsStandardFormal p) :
    realizeFormalCoordinates (formalCoordinates p) = p := by
  classical
  ext d
  by_cases hd : d ∈ p.support
  · let a : Index := artinIndexOfStandard d (fun i => hp d hd i)
    have ha : artinExponent a = d :=
      artinExponent_artinIndexOfStandard d (fun i => hp d hd i)
    rw [← ha, coeff_realizeFormalCoordinates, formalCoordinates,
      ← mul_assoc, ← pow_add,
      (Even.add_self (artinDegree a)).neg_one_pow, one_mul]
  · have hcoeff : coeff d p = 0 := MvPolynomial.notMem_support_iff.mp hd
    rw [hcoeff]
    simp only [realizeFormalCoordinates, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : artinExponent a = d
    · rw [if_pos ha, formalCoordinates, ha, hcoeff, mul_zero, mul_zero]
      simp
    · rw [if_neg ha]
      simp

@[simp]
theorem coefficientSpecialization_X (i : Fin 5) :
    coefficientSpecialization (X i) =
      (MvPolynomial.esymm (Fin 5) ℚ (i.1 + 1) : RootRing) := by
  change ((coefficientEquiv (X i)).1 : RootRing) = _
  simp [coefficientEquiv,
    MvPolynomial.esymmAlgEquiv, MvPolynomial.esymmAlgHom]

theorem formalSpecialization_monomial (d : Fin 5 →₀ ℕ) (c : Coeff) :
    formalSpecialization (monomial d c) =
      coefficientSpecialization c * monomial d (1 : ℚ) := by
  rw [formalSpecialization, MvPolynomial.eval₂Hom_monomial,
    ← MvPolynomial.monic_monomial_eq]
  rfl

/-- Specialization sends the formal Artin realization to the actual
symmetric-module Artin realization, coordinate for coordinate. -/
theorem formalSpecialization_realizeFormalCoordinates (c : Index → Coeff) :
    formalSpecialization (realizeFormalCoordinates c) = realizeCoordinates c := by
  classical
  rw [realizeFormalCoordinates, map_sum, realizeCoordinates,
    Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [formalSpecialization_monomial,
    symmetricArtinBasis_apply_eq_monomial]
  simp [coefficientSpecialization, Algebra.smul_def,
    MvPolynomial.monomial_eq, mul_assoc, mul_left_comm, mul_comm]
  left
  exact (Subalgebra.algebraMap_apply
    (MvPolynomial.symmetricSubalgebra (Fin 5) ℚ)
    (coefficientEquiv (c a))).symm

theorem formalSpecialization_esymm (k : ℕ) :
    formalSpecialization (MvPolynomial.esymm (Fin 5) Coeff k) =
      MvPolynomial.esymm (Fin 5) ℚ k := by
  simp [formalSpecialization, MvPolynomial.esymm]

theorem formalSpecialization_vietaRelation (i : Fin 5) :
    formalSpecialization (vietaRelation i) = 0 := by
  rw [vietaRelation, map_sub, formalSpecialization_esymm]
  simp [e]

/-- The displayed ideal lies in the kernel of the formal specialization. -/
theorem displayedIdeal_le_formalSpecialization_ker :
    displayedIdeal ≤ RingHom.ker formalSpecialization := by
  rw [displayedIdeal_eq_vietaIdeal]
  apply Ideal.span_le.2
  rintro _ ⟨i, rfl⟩
  change formalSpecialization (vietaRelation i) = 0
  exact formalSpecialization_vietaRelation i

theorem IsStandardFormal.sub {p q : Ambient}
    (hp : IsStandardFormal p) (hq : IsStandardFormal q) :
    IsStandardFormal (p - q) := by
  intro d hd i
  rcases Finset.mem_union.mp
      ((MvPolynomial.support_sub (Fin 5) p q) hd) with hdp | hdq
  · exact hp d hdp i
  · exact hq d hdq i

theorem formalSpecialization_injective_on_standard {p q : Ambient}
    (hp : IsStandardFormal p) (hq : IsStandardFormal q)
    (hmap : formalSpecialization p = formalSpecialization q) : p = q := by
  have hpcoords :
      realizeCoordinates (formalCoordinates p) = formalSpecialization p := by
    rw [← formalSpecialization_realizeFormalCoordinates,
      realize_formalCoordinates_of_standard p hp]
  have hqcoords :
      realizeCoordinates (formalCoordinates q) = formalSpecialization q := by
    rw [← formalSpecialization_realizeFormalCoordinates,
      realize_formalCoordinates_of_standard q hq]
  have hcoords : formalCoordinates p = formalCoordinates q := by
    have h : (fun a => coefficientEquiv (formalCoordinates p a)) =
        (fun a => coefficientEquiv (formalCoordinates q a)) := by
      apply (symmetricArtinBasis ℚ 5).equivFun.symm.injective
      simpa [realizeCoordinates] using
        (hpcoords.trans (hmap.trans hqcoords.symm))
    funext a
    apply coefficientEquiv.injective
    exact congrFun h a
  rw [← realize_formalCoordinates_of_standard p hp,
    ← realize_formalCoordinates_of_standard q hq, hcoords]

theorem linearCombination_displayedJ_mem (g : Fin 5 →₀ Ambient) :
    Finsupp.linearCombination Ambient displayedJ g ∈ displayedIdeal := by
  classical
  rw [Finsupp.linearCombination_apply]
  change (∑ i ∈ g.support, g i • displayedJ i) ∈ displayedIdeal
  apply Ideal.sum_mem
  intro i _
  change g i * displayedJ i ∈ displayedIdeal
  exact Ideal.mul_mem_left _ _ (displayedJ_mem_displayedIdeal i)

/-- Two standard formal remainders congruent modulo the displayed ideal are
equal.  This is uniqueness in the actual formal two-level quotient, rather
than uniqueness only after assuming concrete root values. -/
theorem standard_formal_remainder_unique (p r s : Ambient)
    (hr : IsStandardFormal r) (hs : IsStandardFormal s)
    (hpr : p - r ∈ displayedIdeal) (hps : p - s ∈ displayedIdeal) :
    r = s := by
  have hrs : r - s ∈ displayedIdeal := by
    have h := Ideal.sub_mem displayedIdeal hps hpr
    convert h using 1 <;> ring
  have hzero : formalSpecialization (r - s) = 0 :=
    RingHom.mem_ker.mp (displayedIdeal_le_formalSpecialization_ker hrs)
  apply formalSpecialization_injective_on_standard hr hs
  rw [← sub_eq_zero, ← map_sub]
  exact hzero

/-- Every formal polynomial has a unique standard remainder modulo the
displayed ideal. -/
theorem exists_unique_standard_formal_remainder (p : Ambient) :
    ∃ (g : Fin 5 →₀ Ambient) (r : Ambient),
      p = Finsupp.linearCombination Ambient displayedJ g + r ∧
      IsStandardFormal r ∧
      ∀ s : Ambient, IsStandardFormal s → p - s ∈ displayedIdeal → s = r := by
  obtain ⟨g, r, hdecomp, _, hstandard⟩ := exists_standard_formal_remainder p
  have hr : IsStandardFormal r := by
    intro d hd
    exact (standardExponent_iff d).2 (hstandard d hd)
  have hpr : p - r ∈ displayedIdeal := by
    rw [hdecomp]
    simpa using linearCombination_displayedJ_mem g
  refine ⟨g, r, hdecomp, hr, ?_⟩
  intro s hs hps
  exact (standard_formal_remainder_unique p s r hs hr hps hpr)

/-- The formal specialization has exactly Lazard's displayed ideal as its
kernel.  Thus its restriction to standard remainders is not merely an
after-specialization certificate: it identifies the formal quotient. -/
theorem formalSpecialization_ker_eq_displayedIdeal :
    RingHom.ker formalSpecialization = displayedIdeal := by
  apply le_antisymm
  · intro p hp
    obtain ⟨g, r, hdecomp, hr, _⟩ := exists_unique_standard_formal_remainder p
    have hgmem := linearCombination_displayedJ_mem g
    have hpg : formalSpecialization
        (Finsupp.linearCombination Ambient displayedJ g) = 0 :=
      RingHom.mem_ker.mp (displayedIdeal_le_formalSpecialization_ker hgmem)
    have hpzero : formalSpecialization p = 0 := RingHom.mem_ker.mp hp
    have hrzero : formalSpecialization r = 0 := by
      have h := congrArg formalSpecialization hdecomp
      rw [map_add, hpzero, hpg, zero_add] at h
      exact h.symm
    have hr0 : r = 0 :=
      formalSpecialization_injective_on_standard hr
        (by simp [IsStandardFormal]) (by simpa using hrzero)
    rw [hr0, add_zero] at hdecomp
    rw [hdecomp]
    exact hgmem
  · exact displayedIdeal_le_formalSpecialization_ker

/-- The literal finite displayed-basis data, together with the canonical
Artin reconstruction after specializing the formal `eᵢ` to `σᵢ`. -/
structure QuinticDisplayedSpecializationCertificate : Prop where
  generatedIdeal : displayedIdeal = vietaIdeal
  leading : ∀ i, coeff (paperLeadingExponent i) (displayedJ i) = 1 ∧
    ∀ a ∈ (displayedJ i).support,
      a ≠ paperLeadingExponent i → PaperLT a (paperLeadingExponent i)
  reducedTails : ∀ i a, a ∈ (displayedTail i).support → ∀ j,
    ¬ paperLeadingExponent j ≤ a
  normalForm : ∀ p, realizeCoordinates (normalCoordinates p) = p
  normalFormUnique : ∀ p c, realizeCoordinates c = p →
    c = normalCoordinates p

theorem quinticDisplayedSpecializationCertificate :
    QuinticDisplayedSpecializationCertificate where
  generatedIdeal := displayedIdeal_eq_vietaIdeal
  leading := displayedJ_leading_data
  reducedTails := fun i a ha j => displayedJ_reduced_tails i a ha j
  normalForm := realize_normalCoordinates
  normalFormUnique := normalCoordinates_unique

/-- The exact fixed-degree content of Lazard's Lemma 1.  Besides identifying
the displayed and Vieta ideals, this records the paper-order leading terms,
reduced tails, existence and uniqueness of the formal `(x,e)` remainder, and
the resulting quotient-kernel statement.  Thus no correctness property of
the remainder is supplied by a caller. -/
structure QuinticDisplayedReducedGroebnerCertificate : Prop where
  generatedIdeal : displayedIdeal = vietaIdeal
  monicLeading : ∀ i, coeff (paperLeadingExponent i) (displayedJ i) = 1
  leading : ∀ i a, a ∈ (displayedJ i).support →
    a ≠ paperLeadingExponent i →
    PaperLT a (paperLeadingExponent i)
  reducedTails : ∀ i a, a ∈ (displayedTail i).support → ∀ j,
    ¬ paperLeadingExponent j ≤ a
  uniqueDivision : ∀ p : Ambient,
    ∃ (g : Fin 5 →₀ Ambient) (r : Ambient),
      p = Finsupp.linearCombination Ambient displayedJ g + r ∧
      IsStandardFormal r ∧
      ∀ s : Ambient, IsStandardFormal s →
        p - s ∈ displayedIdeal → s = r
  specializationKernel : RingHom.ker formalSpecialization = displayedIdeal

theorem quinticDisplayedReducedGroebnerCertificate :
    QuinticDisplayedReducedGroebnerCertificate where
  generatedIdeal := displayedIdeal_eq_vietaIdeal
  monicLeading i := (displayedJ_leading_data i).1
  leading i a ha hne := (displayedJ_leading_data i).2 a ha hne
  reducedTails := fun i a ha j => displayedJ_reduced_tails i a ha j
  uniqueDivision := exists_unique_standard_formal_remainder
  specializationKernel := formalSpecialization_ker_eq_displayedIdeal

end

end LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerQuintic
