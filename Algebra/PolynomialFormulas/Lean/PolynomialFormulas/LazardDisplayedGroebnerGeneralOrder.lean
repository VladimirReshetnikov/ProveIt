import PolynomialFormulas.LazardDisplayedGroebnerGeneralIdeal
import PolynomialFormulas.LazardInvariantArtinModuleBasis
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Tactic

/-!
# Lazard's displayed family for every admissible paper order

This file isolates the order-theoretic half of Lemma 1 in Lazard's paper.
Unlike the older quintic specialization, the variables here really are the
combined variables

`x₀, ..., x_(n-1), e₁, ..., e_n`.

The order is an arbitrary `MonomialOrder (Fin n ⊕ Fin n)`.  Thus
well-foundedness, the least-monomial axiom, and compatibility with
multiplication are supplied by the `MonomialOrder` structure itself.  The
only extra hypotheses are exactly the two hypotheses printed before
Lazard's Lemma 1:

* `x_i < x_j` whenever `i < j`;
* strict inequality of total root degree decides the comparison, independently
  of the exponents of the `e` variables.

In particular, `PaperOrderHypotheses` does *not* assume that a preselected
term dominates the support of a displayed relation.  That dominance is
proved below from the two hypotheses and additivity of a monomial order.

The displayed polynomial is written as a finite, collision-free sum of
monomials indexed by symmetric powers.  This is the literal combined-ring
version of

`sum_r (-1)^r e_r h_(k+1-r)(x₀,...,x_(n-k-1))`.

The final section proves the separate algebraic bridge to the nested
coefficient-ring presentation in
`LazardDisplayedGroebnerGeneralIdeal`.  It extracts the finite coefficient
formula identifying the power-series-defined `prefixHsymm` with the
symmetric-power sum used here.  The bridge is kept as an explicit
order-independent proposition; it is not hidden in the order hypotheses and
is never used to prove support dominance.
-/

namespace LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerGeneralOrder

open scoped BigOperators MonomialOrder
open Finset MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GeneralIdeal
export LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerGeneralIdeal
  (Ambient Coeff displayedJ e formalE geometricSeries_coeff
    prefixCompleteSeries prefixEmbedding prefixHsymm printedDisplayedJ
    printedDisplayedJ_eq_displayedJ vietaRelation x)
end GeneralIdeal

namespace ArtinBasis
export LeanProofs.PolynomialFormulas.LazardInvariantArtinBasis
  (ArtinIndex artinDegree artinExponent artinExponent_apply)
end ArtinBasis

namespace ArtinModule
export LeanProofs.PolynomialFormulas.LazardInvariantArtinModuleBasis
  (symmetricArtinBasis symmetricArtinBasis_apply_eq_monomial)
end ArtinModule

variable (R : Type*) [CommRing R]
variable (n : ℕ)

/-- The variables in the literal ring: roots on the left and formal
elementary-symmetric coefficients on the right. -/
abbrev Variable := Fin n ⊕ Fin n

abbrev Exponent := Variable n →₀ ℕ

abbrev Combined := MvPolynomial (Variable n) R

/-- Restriction of a combined exponent to the root block. -/
def rootPart (a : Exponent n) : Fin n →₀ ℕ :=
  Finsupp.comapDomain Sum.inl a Sum.inl_injective.injOn

/-- Restriction of a combined exponent to the formal-`e` block. -/
def coefficientPart (a : Exponent n) : Fin n →₀ ℕ :=
  Finsupp.comapDomain Sum.inr a Sum.inr_injective.injOn

/-- Total degree in the root variables only. -/
def rootDegree (a : Exponent n) : ℕ := (rootPart n a).degree

@[simp]
theorem rootPart_sumElim (a b : Fin n →₀ ℕ) :
    rootPart n (a.sumElim b) = a := by
  exact Finsupp.comapDomain_inl_sumElim a b

@[simp]
theorem coefficientPart_sumElim (a b : Fin n →₀ ℕ) :
    coefficientPart n (a.sumElim b) = b := by
  exact Finsupp.comapDomain_inr_sumElim a b

@[simp]
theorem rootDegree_sumElim (a b : Fin n →₀ ℕ) :
    rootDegree n (a.sumElim b) = a.degree := by
  simp [rootDegree]

/-- The root variable in the leading monomial of the relation indexed by
`k`.  Its value is `n-1-k`. -/
def pivot (k : Fin n) : Fin n := ⟨n - 1 - k.1, by omega⟩

@[simp]
theorem pivot_val (k : Fin n) : (pivot n k).1 = n - 1 - k.1 := rfl

theorem pivot_injective : Function.Injective (pivot n) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [pivot_val] at this
  omega

/-- The pure root exponent `x_(n-1-k)^(k+1)`. -/
def leadingRootExponent (k : Fin n) : Fin n →₀ ℕ :=
  Finsupp.single (pivot n k) (k.1 + 1)

/-- The same exponent in all `2n` variables. -/
def leadingExponent (k : Fin n) : Exponent n :=
  (leadingRootExponent n k).sumElim 0

@[simp]
theorem leadingExponent_eq_single (k : Fin n) :
    leadingExponent n k =
      Finsupp.single (Sum.inl (pivot n k)) (k.1 + 1) := by
  simp only [leadingExponent, leadingRootExponent,
    Finsupp.sumElim_single_zero]

@[simp]
theorem rootDegree_leadingExponent (k : Fin n) :
    rootDegree n (leadingExponent n k) = k.1 + 1 := by
  simp [leadingExponent, leadingRootExponent, rootDegree]

/-! ## A collision-free expansion of the printed family -/

/-- The injection of the first `n-k` roots into the full root block. -/
def prefixRootEmbedding (k : Fin n) : Fin (n - k.1) ↪ Fin n :=
  Fin.castLEEmb (Nat.sub_le n k.1)

@[simp]
theorem prefixRootEmbedding_val (k : Fin n) (i : Fin (n - k.1)) :
    (prefixRootEmbedding n k i).1 = i.1 := rfl

/-- The last variable in the prefix `x₀,...,x_(n-k-1)`. -/
def prefixPivot (k : Fin n) : Fin (n - k.1) :=
  ⟨n - 1 - k.1, by omega⟩

@[simp]
theorem prefixRootEmbedding_prefixPivot (k : Fin n) :
    prefixRootEmbedding n k (prefixPivot n k) = pivot n k := by
  apply Fin.ext
  rfl

/-- The exponent vector represented by a symmetric-power element, embedded
in the first `n-k` roots. -/
def prefixRootExponent (k : Fin n) (d : ℕ)
    (s : Sym (Fin (n - k.1)) d) : Fin n →₀ ℕ :=
  Finsupp.mapDomain (prefixRootEmbedding n k)
    (Sym.equivNatSum (Fin (n - k.1)) d s).1

@[simp]
theorem prefixRootExponent_degree (k : Fin n) (d : ℕ)
    (s : Sym (Fin (n - k.1)) d) :
    (prefixRootExponent n k d s).degree = d := by
  rw [prefixRootExponent, Finsupp.degree_mapDomain]
  exact (Sym.equivNatSum (Fin (n - k.1)) d s).2

theorem prefixRootExponent_eq_zero_of_ge (k : Fin n) (d : ℕ)
    (s : Sym (Fin (n - k.1)) d) (i : Fin n)
    (hi : n - k.1 ≤ i.1) :
    prefixRootExponent n k d s i = 0 := by
  rw [prefixRootExponent, Finsupp.mapDomain_notin_range]
  rintro ⟨j, hj⟩
  have hval := congrArg Fin.val hj
  simp only [prefixRootEmbedding_val] at hval
  omega

theorem prefixRootExponent_support_le_pivot (k : Fin n) (d : ℕ)
    (s : Sym (Fin (n - k.1)) d) (i : Fin n)
    (hi : prefixRootExponent n k d s i ≠ 0) :
    i ≤ pivot n k := by
  have hirange : i ∈ Set.range (prefixRootEmbedding n k) :=
    Finsupp.mem_range_of_mapDomain_ne_zero hi
  rcases hirange with ⟨j, rfl⟩
  apply Fin.mk_le_mk.mpr
  omega

/-- The exponent of `e_r`, with `e_0=1`.  The range of `r` and `k<n`
ensure that the positive index is a member of `Fin n`. -/
def formalEExponent (k : Fin n) (r : Fin (k.1 + 2)) : Fin n →₀ ℕ :=
  if hr : r.1 = 0 then 0
  else Finsupp.single ⟨r.1 - 1, by omega⟩ 1

@[simp]
theorem formalEExponent_zero (k : Fin n) :
    formalEExponent n k 0 = 0 := by
  simp [formalEExponent]

/-- A monomial occurring in the `r`th summand of the printed relation. -/
def printedExponent (k : Fin n) (r : Fin (k.1 + 2))
    (s : Sym (Fin (n - k.1)) (k.1 + 1 - r.1)) : Exponent n :=
  (prefixRootExponent n k (k.1 + 1 - r.1) s).sumElim
    (formalEExponent n k r)

@[simp]
theorem rootDegree_printedExponent (k : Fin n) (r : Fin (k.1 + 2))
    (s : Sym (Fin (n - k.1)) (k.1 + 1 - r.1)) :
    rootDegree n (printedExponent n k r s) = k.1 + 1 - r.1 := by
  simp [printedExponent, rootDegree]

/-- The literal printed member, now in the polynomial ring on all `2n`
variables.  `Sym` supplies each degree-`d` root monomial exactly once. -/
def printedDisplayedJ (k : Fin n) : Combined R n :=
  ∑ r : Fin (k.1 + 2),
    ∑ s : Sym (Fin (n - k.1)) (k.1 + 1 - r.1),
      monomial (printedExponent n k r s) ((-1 : R) ^ r.1)

/-- The symmetric-power representative of the pure pivot power. -/
def leadingSym (k : Fin n) : Sym (Fin (n - k.1)) (k.1 + 1) :=
  Sym.replicate (k.1 + 1) (prefixPivot n k)

theorem equivNatSum_leadingSym (k : Fin n) :
    (Sym.equivNatSum (Fin (n - k.1)) (k.1 + 1)
      (leadingSym n k)).1 =
        Finsupp.single (prefixPivot n k) (k.1 + 1) := by
  ext i
  rw [Sym.coe_equivNatSum_apply_apply]
  change Multiset.count i
      (Multiset.replicate (k.1 + 1) (prefixPivot n k)) =
    Finsupp.single (prefixPivot n k) (k.1 + 1) i
  rw [Multiset.count_replicate, Finsupp.single_apply]

@[simp]
theorem prefixRootExponent_leadingSym (k : Fin n) :
    prefixRootExponent n k (k.1 + 1) (leadingSym n k) =
      leadingRootExponent n k := by
  rw [prefixRootExponent, equivNatSum_leadingSym,
    Finsupp.mapDomain_single, prefixRootEmbedding_prefixPivot]
  rfl

@[simp]
theorem printedExponent_zero_leadingSym (k : Fin n) :
    printedExponent n k 0 (leadingSym n k) = leadingExponent n k := by
  simp [printedExponent, leadingExponent]

theorem prefixRootExponent_injective (k : Fin n) (d : ℕ) :
    Function.Injective (prefixRootExponent n k d) := by
  intro s t hst
  apply (Sym.equivNatSum (Fin (n - k.1)) d).injective
  apply Subtype.ext
  exact Finsupp.mapDomain_injective
    (prefixRootEmbedding n k).injective hst

theorem printedExponent_zero_injective (k : Fin n) :
    Function.Injective
      (printedExponent n k (0 : Fin (k.1 + 2))) := by
  intro s t hst
  apply prefixRootExponent_injective n k (k.1 + 1)
  have := congrArg (rootPart n) hst
  simpa [printedExponent] using this

theorem printedExponent_ne_leading_of_pos (k : Fin n)
    (r : Fin (k.1 + 2)) (hr : r.1 ≠ 0)
    (s : Sym (Fin (n - k.1)) (k.1 + 1 - r.1)) :
    printedExponent n k r s ≠ leadingExponent n k := by
  intro h
  have hdegree := congrArg (rootDegree n) h
  simp only [rootDegree_printedExponent,
    rootDegree_leadingExponent] at hdegree
  omega

/-! ## The two genuine paper-order hypotheses -/

/-- Extra assumptions imposed by the paper on an otherwise arbitrary
admissible monomial order on all `2n` variables. -/
structure PaperOrderHypotheses
    (m : MonomialOrder (Variable n)) : Prop where
  /-- A smaller total degree in the root block is always smaller, whatever
  happens in the formal-`e` block. -/
  rootDegree_primary :
    ∀ a b : Exponent n, rootDegree n a < rootDegree n b → a ≺[m] b
  /-- The root variables occur in the printed order
  `x₀ < x₁ < ... < x_(n-1)`. -/
  rootVariable_strictMono :
    StrictMono (fun i : Fin n ↦
      m.toSyn (Finsupp.single (Sum.inl i) 1))

/-- Lazard's additional refinement for Lemma 2: after root total degree,
the formal-`e` block is compared before any remaining root-block tie breaker.
The last field states the comparison exactly when the two formal exponents
differ; when they agree, the ambient admissible order `m` supplies the
remaining tie breaker. -/
structure PaperLemmaTwoOrderHypotheses
    (m : MonomialOrder (Variable n)) extends PaperOrderHypotheses n m where
  formalOrder : MonomialOrder (Fin n)
  formalBlock_primary :
    ∀ a b : Exponent n,
      rootDegree n a = rootDegree n b →
      coefficientPart n a ≠ coefficientPart n b →
      (a ≺[m] b ↔
        coefficientPart n a ≺[formalOrder] coefficientPart n b)

/-- The order-free support form of the stronger certificate produced by
Lazard's homogeneous invariant construction.  It says that `d` is the
largest root-block degree occurring in `p`, that this degree really occurs,
and that every monomial in that whole top root-degree row has zero
formal-`e` exponent.

The last clause is deliberately about every top-row support monomial, not a
preselected Artin coordinate.  This is the form needed to pass honestly to
the actual leading monomial of an arbitrary combined monomial order. -/
structure LiteralTopRowConstant (p : Combined R n) (d : ℕ) : Prop where
  rootDegree_le :
    ∀ a ∈ p.support, rootDegree n a ≤ d
  top_exists :
    ∃ a ∈ p.support,
      rootDegree n a = d ∧ coefficientPart n a = 0
  top_coefficientPart_zero :
    ∀ a ∈ p.support, rootDegree n a = d → coefficientPart n a = 0

/-- The actual leading exponent of a combined polynomial satisfying the
whole-top-row certificate has root degree `d` and contains no formal
elementary-symmetric variable.

Only the root-degree-primary part of the paper's block order is used.  The
paper additionally refines equal root degrees by the formal-`e` block, but
that tie breaker is unnecessary here because *every* monomial in the top
row is already formal-`e`-free. -/
theorem actualLeadingExponent_rootDegree_eq_and_coefficientPart_eq_zero
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) {p : Combined R n} {d : ℕ}
    (hp : LiteralTopRowConstant R n p d) :
    rootDegree n (m.degree p) = d ∧
      coefficientPart n (m.degree p) = 0 := by
  obtain ⟨a, ha, hadegree, _⟩ := hp.top_exists
  have hp0 : p ≠ 0 := by
    intro hzero
    subst p
    simpa using ha
  have hleading : m.degree p ∈ p.support := m.degree_mem_support hp0
  have hdegree_le : rootDegree n (m.degree p) ≤ d :=
    hp.rootDegree_le (m.degree p) hleading
  have hdegree_ge : d ≤ rootDegree n (m.degree p) := by
    apply Nat.le_of_not_gt
    intro hlt
    have horder : m.degree p ≺[m] a := by
      apply hm.rootDegree_primary
      simpa [hadegree] using hlt
    exact (not_lt_of_ge (m.le_degree ha)) horder
  have hdegree : rootDegree n (m.degree p) = d :=
    Nat.le_antisymm hdegree_le hdegree_ge
  exact ⟨hdegree,
    hp.top_coefficientPart_zero (m.degree p) hleading hdegree⟩

/-- Exact-paper-block-order corollary.  The additional equal-root-degree
formal-block comparison is intentionally unused: the whole-top-row
certificate proves the stronger, tie-break-independent conclusion. -/
theorem actualLeadingExponent_of_paperLemmaTwoOrder
    {m : MonomialOrder (Variable n)}
    (hm : PaperLemmaTwoOrderHypotheses n m)
    {p : Combined R n} {d : ℕ}
    (hp : LiteralTopRowConstant R n p d) :
    rootDegree n (m.degree p) = d ∧
      coefficientPart n (m.degree p) = 0 :=
  actualLeadingExponent_rootDegree_eq_and_coefficientPart_eq_zero
    R n hm.toPaperOrderHypotheses hp

theorem rootVariable_le {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) {i j : Fin n} (hij : i ≤ j) :
    Finsupp.single (Sum.inl i) 1 ≼[m]
      Finsupp.single (Sum.inl j) 1 := by
  by_cases h : i = j
  · subst j
    exact le_rfl
  · exact le_of_lt (hm.rootVariable_strictMono (lt_of_le_of_ne hij h))

/-- Additive compatibility of an actual monomial order upgrades the chain
of root variables to the corresponding statement for every pure root
monomial supported below a pivot. -/
theorem rootMonomial_le_purePivot {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (p : Fin n) (u : Fin n →₀ ℕ)
    (hu : ∀ i : Fin n, u i ≠ 0 → i ≤ p) :
    u.sumElim (0 : Fin n →₀ ℕ) ≼[m]
      Finsupp.single (Sum.inl p) u.degree := by
  induction u using Finsupp.induction with
  | zero => simp
  | single_add i c u hi hc ih =>
      have hip : i ≤ p := by
        apply hu i
        simp [hi, hc]
      have hi_le := rootVariable_le n hm hip
      have hi_smul :
          m.toSyn (c • Finsupp.single (Sum.inl i) 1) ≤
            m.toSyn (c • Finsupp.single (Sum.inl p) 1) := by
        simpa only [map_nsmul] using nsmul_le_nsmul_right hi_le c
      have hu' : ∀ j : Fin n, u j ≠ 0 → j ≤ p := by
        intro j hj
        apply hu j
        simp only [Finsupp.add_apply]
        omega
      have hrec := ih hu'
      have hleft :
          (Finsupp.single i c + u).sumElim (0 : Fin n →₀ ℕ) =
            c • Finsupp.single (Sum.inl i) 1 +
              u.sumElim (0 : Fin n →₀ ℕ) := by
        ext z
        cases z <;> simp [Finsupp.single_apply]
      have hright :
          Finsupp.single (Sum.inl p : Variable n)
              (Finsupp.single i c + u).degree =
            c • Finsupp.single (Sum.inl p : Variable n) 1 +
              Finsupp.single (Sum.inl p : Variable n) u.degree := by
        rw [map_add, Finsupp.degree_single]
        ext z
        simp [Finsupp.single_apply, add_comm]
      rw [hleft, hright, map_add, map_add]
      exact add_le_add hi_smul hrec

theorem prefixRootMonomial_le_leading
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (k : Fin n)
    (s : Sym (Fin (n - k.1)) (k.1 + 1)) :
    printedExponent n k 0 s ≼[m] leadingExponent n k := by
  have h := rootMonomial_le_purePivot n hm (pivot n k)
    (prefixRootExponent n k (k.1 + 1) s)
    (prefixRootExponent_support_le_pivot n k (k.1 + 1) s)
  rw [prefixRootExponent_degree] at h
  simpa only [printedExponent, formalEExponent_zero, Fin.val_zero, Nat.sub_zero,
    leadingExponent_eq_single, Nat.succ_eq_add_one] using h

/-- Every non-leading monomial in a printed relation is strictly below the
displayed pure power for *every* admissible order satisfying the two paper
hypotheses. -/
theorem printedExponent_lt_leading
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (k : Fin n)
    (r : Fin (k.1 + 2))
    (s : Sym (Fin (n - k.1)) (k.1 + 1 - r.1))
    (hne : printedExponent n k r s ≠ leadingExponent n k) :
    printedExponent n k r s ≺[m] leadingExponent n k := by
  by_cases hr : r.1 = 0
  · have hr0 : r = 0 := Fin.ext hr
    subst r
    have hle := prefixRootMonomial_le_leading n hm k s
    exact lt_of_le_of_ne hle (fun h ↦ hne (m.toSyn.injective h))
  · apply hm.rootDegree_primary
    rw [rootDegree_printedExponent, rootDegree_leadingExponent]
    omega

/-! ## Support, leading monomial, and reduced tails -/

theorem mem_support_printedDisplayedJ_witness [Nontrivial R]
    (k : Fin n) {a : Exponent n}
    (ha : a ∈ (printedDisplayedJ R n k).support) :
    ∃ (r : Fin (k.1 + 2))
        (s : Sym (Fin (n - k.1)) (k.1 + 1 - r.1)),
      a = printedExponent n k r s := by
  classical
  have hr := MvPolynomial.support_sum ha
  rcases Finset.mem_biUnion.mp hr with ⟨r, -, hr⟩
  have hs := MvPolynomial.support_sum hr
  rcases Finset.mem_biUnion.mp hs with ⟨s, -, hs⟩
  have hmono := MvPolynomial.support_monomial_subset hs
  exact ⟨r, s, Finset.mem_singleton.mp hmono⟩

theorem coeff_leading_printedDisplayedJ [Nontrivial R] (k : Fin n) :
    coeff (leadingExponent n k) (printedDisplayedJ R n k) = 1 := by
  classical
  simp only [printedDisplayedJ, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Fin.sum_univ_succ]
  have hzero :
      (∑ s : Sym (Fin (n - k.1)) (k.1 + 1),
          if printedExponent n k 0 s = leadingExponent n k
          then ((-1 : R) ^ (0 : Fin (k.1 + 2)).1) else 0) = 1 := by
    rw [Finset.sum_eq_single (leadingSym n k)]
    · simp
    · intro s _ hs
      rw [if_neg]
      intro hlead
      apply hs
      apply printedExponent_zero_injective n k
      exact hlead.trans (printedExponent_zero_leadingSym n k).symm
    · simp
  have hsucc (r : Fin (k.1 + 1)) :
      (∑ s : Sym (Fin (n - k.1))
          (k.1 + 1 - (Fin.succ r : Fin (k.1 + 2)).1),
        if printedExponent n k (Fin.succ r) s = leadingExponent n k
        then ((-1 : R) ^ (Fin.succ r : Fin (k.1 + 2)).1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    exact printedExponent_ne_leading_of_pos n k (Fin.succ r) (by simp) s
  have hrest :
      (∑ r : Fin (k.1 + 1),
        ∑ s : Sym (Fin (n - k.1))
            (k.1 + 1 - (Fin.succ r : Fin (k.1 + 2)).1),
          if printedExponent n k (Fin.succ r) s = leadingExponent n k
          then ((-1 : R) ^ (Fin.succ r : Fin (k.1 + 2)).1) else 0) = 0 := by
    exact Finset.sum_eq_zero fun r _ ↦ hsucc r
  rw [hrest, add_zero]
  exact hzero

theorem printedDisplayedJ_support_strict [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (k : Fin n)
    {a : Exponent n} (ha : a ∈ (printedDisplayedJ R n k).support)
    (hne : a ≠ leadingExponent n k) :
    a ≺[m] leadingExponent n k := by
  rcases mem_support_printedDisplayedJ_witness R n k ha with ⟨r, s, rfl⟩
  exact printedExponent_lt_leading n hm k r s hne

/-- The leading monomial is `x_(n-1-k)^(k+1)` for every paper order. -/
theorem degree_printedDisplayedJ [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (k : Fin n) :
    m.degree (printedDisplayedJ R n k) = leadingExponent n k := by
  apply m.toSyn.injective
  apply le_antisymm
  · rw [m.degree_le_iff]
    intro a ha
    by_cases h : a = leadingExponent n k
    · subst a
      exact le_rfl
    · exact le_of_lt (printedDisplayedJ_support_strict R n hm k ha h)
  · apply m.le_degree
    rw [MvPolynomial.mem_support_iff,
      coeff_leading_printedDisplayedJ]
    exact one_ne_zero

/-- The displayed family is monic for every paper order. -/
theorem leadingCoeff_printedDisplayedJ [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (k : Fin n) :
    m.leadingCoeff (printedDisplayedJ R n k) = 1 := by
  rw [MonomialOrder.leadingCoeff, degree_printedDisplayedJ R n hm,
    coeff_leading_printedDisplayedJ]

/-- Removing the monic leading term. -/
def printedTail [Nontrivial R] (k : Fin n) : Combined R n :=
  printedDisplayedJ R n k - monomial (leadingExponent n k) 1

theorem printedTail_support_strict [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (k : Fin n)
    {a : Exponent n} (ha : a ∈ (printedTail R n k).support) :
    a ≺[m] leadingExponent n k := by
  classical
  have hne : a ≠ leadingExponent n k := by
    intro h
    subst a
    rw [MvPolynomial.mem_support_iff] at ha
    apply ha
    simp only [printedTail, MvPolynomial.coeff_sub,
      coeff_leading_printedDisplayedJ, MvPolynomial.coeff_monomial,
      if_pos, sub_self]
  have hsupport : a ∈ (printedDisplayedJ R n k).support := by
    rw [MvPolynomial.mem_support_iff] at ha ⊢
    simpa only [printedTail, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial, if_neg hne.symm, sub_zero] using ha
  exact printedDisplayedJ_support_strict R n hm k hsupport hne

theorem degree_printedTail_lt [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (k : Fin n) :
    m.degree (printedTail R n k) ≺[m] leadingExponent n k := by
  have hlead : leadingExponent n k ≠ 0 := by
    intro h
    have hv := congrArg
      (fun a : Exponent n ↦ a (Sum.inl (pivot n k))) h
    simp [leadingExponent, leadingRootExponent,
      Finsupp.single_apply] at hv
  have hpos : 0 ≺[m] leadingExponent n k := by
    apply lt_of_le_of_ne
    · change m.toSyn 0 ≤ m.toSyn (leadingExponent n k)
      rw [map_zero]
      exact bot_le
    · intro h
      apply hlead
      exact (m.toSyn.injective h).symm
  rw [m.degree_lt_iff hpos]
  intro a ha
  exact printedTail_support_strict R n hm k ha

theorem eq_single_of_single_le_of_degree_le
    {u : Fin n →₀ ℕ} {i : Fin n} {d : ℕ}
    (hdiv : Finsupp.single i d ≤ u) (hdegree : u.degree ≤ d) :
    u = Finsupp.single i d := by
  have hsplit := tsub_add_cancel_of_le hdiv
  have hdegreeSplit := congrArg Finsupp.degree hsplit
  simp only [map_add, Finsupp.degree_single] at hdegreeSplit
  have hz : (u - Finsupp.single i d).degree = 0 := by omega
  have hzero : u - Finsupp.single i d = 0 :=
    (Finsupp.degree_eq_zero_iff _).mp hz
  simpa [hzero] using hsplit.symm

/-- The combinatorial reduced-tail fact.  It is independent of the
monomial order: no tail exponent is divisible by any displayed leading
exponent. -/
theorem printedExponent_not_divisible
    (k : Fin n) (r : Fin (k.1 + 2))
    (s : Sym (Fin (n - k.1)) (k.1 + 1 - r.1))
    (hne : printedExponent n k r s ≠ leadingExponent n k)
    (j : Fin n) :
    ¬ leadingExponent n j ≤ printedExponent n k r s := by
  intro hdiv
  have hpivot :
      j.1 + 1 ≤
        prefixRootExponent n k (k.1 + 1 - r.1) s (pivot n j) := by
    have h := hdiv (Sum.inl (pivot n j))
    simpa [leadingExponent, leadingRootExponent, printedExponent,
      Finsupp.single_apply] using h
  by_cases hjk : j.1 < k.1
  · have hzero := prefixRootExponent_eq_zero_of_ge n k
      (k.1 + 1 - r.1) s (pivot n j) (by
        simp only [pivot_val]
        omega)
    rw [hzero] at hpivot
    omega
  · have hcoordDegree := Finsupp.le_degree (pivot n j)
      (prefixRootExponent n k (k.1 + 1 - r.1) s)
    rw [prefixRootExponent_degree] at hcoordDegree
    have hjk_le : k.1 ≤ j.1 := Nat.le_of_not_gt hjk
    have hj_eq : j = k := by
      apply Fin.ext
      omega
    subst j
    have hr0 : r.1 = 0 := by omega
    have hr_eq : r = 0 := Fin.ext hr0
    subst r
    have hrootDiv :
        leadingRootExponent n k ≤
          prefixRootExponent n k (k.1 + 1) s := by
      intro i
      have h := hdiv (Sum.inl i)
      simpa [leadingExponent, printedExponent] using h
    have hrootEq :
        prefixRootExponent n k (k.1 + 1) s =
          leadingRootExponent n k := by
      apply eq_single_of_single_le_of_degree_le n hrootDiv
      simp [leadingRootExponent]
    apply hne
    simpa [printedExponent, leadingExponent, hrootEq]

/-- Literal reducedness of every displayed tail. -/
theorem printedDisplayedJ_reduced_tails [Nontrivial R]
    (k : Fin n) {a : Exponent n}
    (ha : a ∈ (printedTail R n k).support) (j : Fin n) :
    ¬ leadingExponent n j ≤ a := by
  classical
  have hne : a ≠ leadingExponent n k := by
    intro h
    subst a
    rw [MvPolynomial.mem_support_iff] at ha
    apply ha
    simp only [printedTail, MvPolynomial.coeff_sub,
      coeff_leading_printedDisplayedJ, MvPolynomial.coeff_monomial,
      if_pos, sub_self]
  have hsupport : a ∈ (printedDisplayedJ R n k).support := by
    rw [MvPolynomial.mem_support_iff] at ha ⊢
    simpa only [printedTail, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial, if_neg hne.symm, sub_zero] using ha
  rcases mem_support_printedDisplayedJ_witness R n k hsupport with
    ⟨r, s, rfl⟩
  exact printedExponent_not_divisible n k r s hne j

/-- Distinct leading exponents have disjoint variable support, the
monomial form of pairwise coprimality. -/
theorem leadingExponent_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (leadingExponent n i) (leadingExponent n j) := by
  have hpivot : pivot n i ≠ pivot n j := (pivot_injective n).ne hij
  have hkey : (Sum.inl (pivot n i) : Variable n) ≠
      Sum.inl (pivot n j) := fun h ↦ hpivot (Sum.inl.inj h)
  rw [leadingExponent_eq_single, leadingExponent_eq_single,
    Finsupp.disjoint_iff]
  exact (Finsupp.support_single_disjoint (by omega) (by omega)).2 hkey

/-- Distinct displayed leading monomials do not divide one another.  This
is the leading-term part of reducedness, complementary to
`printedDisplayedJ_reduced_tails`. -/
theorem leadingExponent_not_divides_of_ne {i j : Fin n} (hij : i ≠ j) :
    ¬ leadingExponent n i ≤ leadingExponent n j := by
  intro hdiv
  have hcoordinate := hdiv (Sum.inl (pivot n i))
  have hpivot : pivot n i ≠ pivot n j := (pivot_injective n).ne hij
  simp [leadingExponent_eq_single, Finsupp.single_apply, hpivot] at hcoordinate

theorem leadingExponent_tsub_of_ne {i j : Fin n} (hij : i ≠ j) :
    leadingExponent n i - leadingExponent n j = leadingExponent n i := by
  have hpivot : pivot n i ≠ pivot n j := (pivot_injective n).ne hij
  ext z
  rw [Finsupp.tsub_apply]
  by_cases hz : z = Sum.inl (pivot n i)
  · subst z
    simp [leadingExponent_eq_single, Finsupp.single_apply, hpivot]
  · simp [leadingExponent_eq_single, Finsupp.single_apply, hz]

/-- Multiplying a tail by another displayed relation stays strictly below
the product of the two displayed leading monomials.  Only the general
degree-of-a-product upper bound is needed, so this remains valid over a
commutative ring with zero divisors. -/
theorem degree_printedTail_mul_lt_leading_add [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (i j : Fin n) :
    m.degree (printedTail R n i * printedDisplayedJ R n j) ≺[m]
      leadingExponent n i + leadingExponent n j := by
  change m.toSyn
      (m.degree (printedTail R n i * printedDisplayedJ R n j)) <
    m.toSyn (leadingExponent n i + leadingExponent n j)
  calc
    m.toSyn (m.degree
        (printedTail R n i * printedDisplayedJ R n j)) ≤
        m.toSyn (m.degree (printedTail R n i)) +
          m.toSyn (m.degree (printedDisplayedJ R n j)) :=
      m.toSyn_degree_mul_le
    _ = m.toSyn (m.degree (printedTail R n i)) +
          m.toSyn (leadingExponent n j) := by
      rw [degree_printedDisplayedJ R n hm]
    _ < m.toSyn (leadingExponent n i) +
          m.toSyn (leadingExponent n j) :=
      add_lt_add_left (degree_printedTail_lt R n hm i) _
    _ = m.toSyn (leadingExponent n i + leadingExponent n j) := by
      rw [map_add]

/-- For coprime leading monomials, the S-polynomial has the familiar
two-generator standard representation

`S(J_i,J_j) = tail_i J_j - tail_j J_i`.

This is an equality in the polynomial ring, not a certificate supplied by
the caller. -/
theorem sPolynomial_eq_tail_representation [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) {i j : Fin n} (hij : i ≠ j) :
    m.sPolynomial (printedDisplayedJ R n i)
        (printedDisplayedJ R n j) =
      printedTail R n i * printedDisplayedJ R n j -
        printedTail R n j * printedDisplayedJ R n i := by
  rw [MonomialOrder.sPolynomial,
    degree_printedDisplayedJ R n hm, degree_printedDisplayedJ R n hm,
    leadingCoeff_printedDisplayedJ R n hm,
    leadingCoeff_printedDisplayedJ R n hm,
    leadingExponent_tsub_of_ne n (Ne.symm hij),
    leadingExponent_tsub_of_ne n hij]
  unfold printedTail
  ring

/-- The precise Buchberger input supplied by the pairwise-coprime leading
monomials.  Both terms in the displayed representation are strictly below
the common product leading exponent. -/
structure PairSPolynomialStandardRepresentation [Nontrivial R]
    (m : MonomialOrder (Variable n)) (i j : Fin n) : Prop where
  identity :
    m.sPolynomial (printedDisplayedJ R n i)
        (printedDisplayedJ R n j) =
      printedTail R n i * printedDisplayedJ R n j -
        printedTail R n j * printedDisplayedJ R n i
  leftBelow :
    m.degree (printedTail R n i * printedDisplayedJ R n j) ≺[m]
      leadingExponent n i + leadingExponent n j
  rightBelow :
    m.degree (printedTail R n j * printedDisplayedJ R n i) ≺[m]
      leadingExponent n i + leadingExponent n j

/-- Every pair of distinct printed relations has a strict standard
S-polynomial representation.  This is the pairwise-coprime case of
Buchberger's criterion, stated without pretending that Mathlib currently
has a bundled `IsGroebnerBasis` predicate. -/
theorem pairSPolynomial_standardRepresentation [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) {i j : Fin n} (hij : i ≠ j) :
    PairSPolynomialStandardRepresentation R n m i j where
  identity := sPolynomial_eq_tail_representation R n hm hij
  leftBelow := degree_printedTail_mul_lt_leading_add R n hm i j
  rightBelow := by
    rw [add_comm]
    exact degree_printedTail_mul_lt_leading_add R n hm j i

/-- Division by the displayed monic family gives a remainder supported on
the Artin staircase, uniformly for every paper order.  This is the exact
normal-form *existence* consequence available from Mathlib's current
`MonomialOrder.div` API. -/
theorem exists_standard_remainder [Nontrivial R]
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (p : Combined R n) :
    ∃ (g : Fin n →₀ Combined R n) (r : Combined R n),
      p = Finsupp.linearCombination (Combined R n)
          (printedDisplayedJ R n) g + r ∧
      (∀ k, m.degree (printedDisplayedJ R n k * g k) ≼[m]
        m.degree p) ∧
      (∀ a ∈ r.support, ∀ k : Fin n,
        ¬ leadingExponent n k ≤ a) := by
  obtain ⟨g, r, hdecomp, hdegree, hrem⟩ := m.div
    (b := printedDisplayedJ R n) (fun k ↦ by
      rw [leadingCoeff_printedDisplayedJ R n hm]
      exact isUnit_one) p
  refine ⟨g, r, hdecomp, hdegree, ?_⟩
  intro a ha k
  simpa [degree_printedDisplayedJ R n hm] using hrem a ha k

/-! ## Separate bridge to the nested coefficient-ring presentation -/

/-- Flatten `R[e][x]` to the literal ring `R[x,e]`. -/
def flatten : GeneralIdeal.Ambient R n →+* Combined R n :=
  (MvPolynomial.sumRingEquiv R (Fin n) (Fin n)).symm.toRingHom

/-- The same complete homogeneous sum before flattening the coefficient
ring. -/
def nestedPrefixH (k : Fin n) (d : ℕ) : GeneralIdeal.Ambient R n :=
  ∑ s : Sym (Fin (n - k.1)) d,
    monomial (prefixRootExponent n k d s) 1

/-- The combined-ring complete homogeneous sum used by the explicit
display above. -/
def combinedPrefixH (k : Fin n) (d : ℕ) : Combined R n :=
  ∑ s : Sym (Fin (n - k.1)) d,
    monomial
      ((prefixRootExponent n k d s).sumElim (0 : Fin n →₀ ℕ)) 1

/-- For the full finite index set, a finitely-supported antidiagonal is
the same data as a symmetric-power exponent vector. -/
def univAntidiagEquivSym (q d : ℕ) :
    ↑((Finset.univ : Finset (Fin q)).finsuppAntidiag d) ≃
      Sym (Fin q) d where
  toFun l :=
    (Sym.equivNatSum (Fin q) d).symm
      ⟨l.1, (Finset.mem_finsuppAntidiag'.mp l.2).1⟩
  invFun s :=
    ⟨(Sym.equivNatSum (Fin q) d s).1,
      Finset.mem_finsuppAntidiag'.mpr
        ⟨(Sym.equivNatSum (Fin q) d s).2,
          Finset.subset_univ _⟩⟩
  left_inv l := by
    apply Subtype.ext
    simp
  right_inv s := by
    apply (Sym.equivNatSum (Fin q) d).injective
    apply Subtype.ext
    simp

@[simp]
theorem equivNatSum_univAntidiagEquivSym (q d : ℕ)
    (l : ↑((Finset.univ : Finset (Fin q)).finsuppAntidiag d)) :
    (Sym.equivNatSum (Fin q) d (univAntidiagEquivSym q d l)).1 =
      l.1 := by
  simp [univAntidiagEquivSym]

/-- A product of powers of the prefix variables is the monomial obtained
by embedding the corresponding exponent vector. -/
theorem prod_prefix_x_pow_eq_monomial (k : Fin n)
    (u : Fin (n - k.1) →₀ ℕ) :
    (∏ i : Fin (n - k.1),
        GeneralIdeal.x R n (prefixRootEmbedding n k i) ^ u i) =
      monomial (Finsupp.mapDomain (prefixRootEmbedding n k) u) 1 := by
  calc
    (∏ i : Fin (n - k.1),
        GeneralIdeal.x R n (prefixRootEmbedding n k i) ^ u i) =
        MvPolynomial.rename (prefixRootEmbedding n k)
          (∏ i : Fin (n - k.1),
            (X i : MvPolynomial (Fin (n - k.1))
              (GeneralIdeal.Coeff R n)) ^ u i) := by
          simp [GeneralIdeal.x]
    _ = MvPolynomial.rename (prefixRootEmbedding n k)
          (monomial u (1 : GeneralIdeal.Coeff R n)) := by
          congr 1
          have h := MvPolynomial.prod_X_pow
            (R := GeneralIdeal.Coeff R n)
            (fun i : Fin (n - k.1) ↦ u i) Finset.univ
          have hind : Finsupp.indicator (Finset.univ : Finset (Fin (n - k.1)))
              (fun i _ ↦ u i) = u := by
            ext i
            simp [Finsupp.indicator]
          rw [hind] at h
          simpa using h
    _ = monomial (Finsupp.mapDomain (prefixRootEmbedding n k) u) 1 := by
          rw [MvPolynomial.rename_monomial]

/-- Direct finite coefficient extraction from the already-used product of
geometric series.  This discharges the algebraic content of the former
`PrefixCoefficientBridge`: no formal power-series inverse is needed. -/
theorem prefixHsymm_eq_nestedPrefixH (k : Fin n) (d : ℕ) :
    GeneralIdeal.prefixHsymm R n k d = nestedPrefixH R n k d := by
  classical
  rw [GeneralIdeal.prefixHsymm, GeneralIdeal.prefixCompleteSeries,
    PowerSeries.coeff_prod]
  simp only [GeneralIdeal.geometricSeries_coeff]
  rw [← Finset.sum_attach]
  change
    (∑ l : ↑((Finset.univ : Finset (Fin (n - k.1))).finsuppAntidiag d),
      ∏ i : Fin (n - k.1),
        GeneralIdeal.x R n (prefixRootEmbedding n k i) ^ l.1 i) =
      ∑ s : Sym (Fin (n - k.1)) d,
        monomial (prefixRootExponent n k d s) 1
  apply Fintype.sum_equiv (univAntidiagEquivSym (n - k.1) d)
  intro l
  rw [prod_prefix_x_pow_eq_monomial]
  congr 1
  rw [prefixRootExponent,
    equivNatSum_univAntidiagEquivSym]

/-- Flattening a pure outer/root monomial only inserts a zero exponent in
the coefficient block. -/
theorem flatten_monomial_root (u : Fin n →₀ ℕ) :
    flatten R n (monomial u (1 : GeneralIdeal.Coeff R n)) =
      monomial (u.sumElim (0 : Fin n →₀ ℕ)) 1 := by
  classical
  simp [flatten, MvPolynomial.monomial_eq,
    Finsupp.prod_sumElim]

theorem flatten_nestedPrefixH (k : Fin n) (d : ℕ) :
    flatten R n (nestedPrefixH R n k d) =
      combinedPrefixH R n k d := by
  classical
  rw [nestedPrefixH, combinedPrefixH, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact flatten_monomial_root R n (prefixRootExponent n k d s)

/-- The algebraic transport interface kept separate from the order argument:
coefficients of the finite product of geometric series are the collision-free
symmetric-power sums.  This proposition mentions no order and no desired
leading term.  `prefixCoefficientBridge` immediately below proves the
interface using `prefixHsymm_eq_nestedPrefixH`. -/
def PrefixCoefficientBridge : Prop :=
  ∀ (k : Fin n) (d : ℕ),
    flatten R n (GeneralIdeal.prefixHsymm R n k d) =
      combinedPrefixH R n k d

/-- The bridge is a theorem, obtained by finite coefficient extraction. -/
theorem prefixCoefficientBridge : PrefixCoefficientBridge R n := by
  intro k d
  rw [prefixHsymm_eq_nestedPrefixH, flatten_nestedPrefixH]

/-- The coefficient bridge transports the nested printed formula to the
literal combined-variable formula term by term. -/
theorem combined_printedDisplayedJ_eq
    (hbridge : PrefixCoefficientBridge R n) (k : Fin n) :
    flatten R n (GeneralIdeal.printedDisplayedJ R n k) =
      printedDisplayedJ R n k := by
  classical
  rw [GeneralIdeal.printedDisplayedJ, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_mul, map_mul, map_pow, hbridge]
  by_cases hr : r.1 = 0
  · have hr0 : r = 0 := Fin.ext hr
    subst r
    simp [GeneralIdeal.formalE, flatten, combinedPrefixH,
      printedDisplayedJ, printedExponent]
  · have hrn : r.1 ≤ n := by omega
    simp [GeneralIdeal.formalE, GeneralIdeal.e, hr, hrn, flatten, combinedPrefixH,
      printedDisplayedJ, printedExponent, formalEExponent, hr,
      MvPolynomial.sumRingEquiv_symm_C_X,
      MvPolynomial.sumRingEquiv_symm_X, mul_comm, mul_left_comm,
      mul_assoc]
    simp_rw [mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp [MvPolynomial.X, MvPolynomial.C, MvPolynomial.monomial_mul,
      Finsupp.sumElim_eq_add, add_comm, add_left_comm, add_assoc]
    rw [show (-1 : Combined R n) = C (-1 : R) by simp,
      ← map_pow, MvPolynomial.C_mul_monomial, mul_one]

/-- Unconditional transport of the general nested printed relation to its
literal polynomial in all `2n` variables. -/
theorem combined_printedDisplayedJ_eq_unconditional (k : Fin n) :
    flatten R n (GeneralIdeal.printedDisplayedJ R n k) =
      printedDisplayedJ R n k :=
  combined_printedDisplayedJ_eq R n (prefixCoefficientBridge R n) k

/-! ## The arbitrary-degree normal-form endpoint over a domain

The Artin-module basis currently available in the project is stated over an
integral domain.  That is enough for Lazard's characteristic-zero
application, and it gives a short, independent proof of the one fact missing
from the bare division theorem: a standard polynomial cannot lie nontrivially
in the displayed ideal.  We keep the assumption visible on every theorem
which uses this endpoint.  The leading-term, reduced-tail, and strict
S-polynomial results above remain valid over every nontrivial commutative
ring.
-/

/-- Put a polynomial in the combined variables back into the nested
coefficient/root presentation `R[e][x]`. -/
def unflatten : Combined R n →+* GeneralIdeal.Ambient R n :=
  (MvPolynomial.sumRingEquiv R (Fin n) (Fin n)).toRingHom

@[simp]
theorem flatten_unflatten (p : Combined R n) :
    flatten R n (unflatten R n p) = p :=
  (MvPolynomial.sumRingEquiv R (Fin n) (Fin n)).symm_apply_apply p

@[simp]
theorem unflatten_flatten (p : GeneralIdeal.Ambient R n) :
    unflatten R n (flatten R n p) = p :=
  (MvPolynomial.sumRingEquiv R (Fin n) (Fin n)).apply_symm_apply p

theorem sumElim_eq_sumElim_iff
    (u v u' v' : Fin n →₀ ℕ) :
    u.sumElim v = u'.sumElim v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    constructor
    · simpa using congrArg (rootPart n) h
    · simpa using congrArg (coefficientPart n) h
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Currying a combined monomial separates its root and formal-coefficient
exponents. -/
theorem unflatten_monomial_sumElim (u v : Fin n →₀ ℕ) (c : R) :
    unflatten R n (monomial (u.sumElim v) c) =
      monomial u (monomial v c) := by
  change (MvPolynomial.sumRingEquiv R (Fin n) (Fin n))
      (monomial (u.sumElim v) c) = monomial u (monomial v c)
  simp [MvPolynomial.sumRingEquiv, MvPolynomial.monomial]

/-- Coefficients under currying: the outer coefficient at root exponent
`u`, followed by the inner coefficient at formal-`e` exponent `v`, is the
coefficient of the combined exponent `u.sumElim v`. -/
theorem coeff_coeff_unflatten (p : Combined R n)
    (u v : Fin n →₀ ℕ) :
    coeff v (coeff u (unflatten R n p)) = coeff (u.sumElim v) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      let u' := rootPart n a
      let v' := coefficientPart n a
      have ha : u'.sumElim v' = a := by
        exact Finsupp.comapDomain_sumElim_comapDomain a
      rw [← ha, unflatten_monomial_sumElim]
      simp only [MvPolynomial.coeff_monomial, sumElim_eq_sumElim_iff]
      by_cases hu : u' = u
      · simp only [hu, if_true, true_and, MvPolynomial.coeff_monomial]
      · simp only [hu, if_false, false_and, MvPolynomial.coeff_zero]
  | add p q hp hq =>
      simp [map_add, hp, hq]

/-- A combined polynomial is standard when no support monomial is divisible
by any displayed leading monomial. -/
def IsStandard (p : Combined R n) : Prop :=
  ∀ a ∈ p.support, ∀ k : Fin n, ¬ leadingExponent n k ≤ a

theorem pivot_involutive (i : Fin n) :
    pivot n (pivot n i) = i := by
  apply Fin.ext
  simp only [pivot_val]
  omega

theorem pivot_succ_eq_bound (i : Fin n) :
    (pivot n i).1 + 1 = n - i.1 := by
  simp only [pivot_val]
  omega

/-- The no-leading-divisor condition is exactly the usual Artin staircase
bound on the root coordinates. -/
theorem standardExponent_iff_root_bounds (a : Exponent n) :
    (∀ i : Fin n, a (Sum.inl i) < n - i.1) ↔
      ∀ k : Fin n, ¬ leadingExponent n k ≤ a := by
  constructor
  · intro h k hdiv
    have hcoord :
        k.1 + 1 ≤ a (Sum.inl (pivot n k)) := by
      rw [leadingExponent_eq_single, Finsupp.single_le_iff] at hdiv
      exact hdiv
    have hbound := h (pivot n k)
    rw [← pivot_succ_eq_bound, pivot_involutive] at hbound
    omega
  · intro h i
    apply Nat.lt_of_not_ge
    intro hge
    apply h (pivot n i)
    rw [leadingExponent_eq_single, Finsupp.single_le_iff,
      pivot_involutive, pivot_succ_eq_bound]
    exact hge

theorem isStandard_iff_root_bounds (p : Combined R n) :
    IsStandard R n p ↔
      ∀ a ∈ p.support, ∀ i : Fin n,
        a (Sum.inl i) < n - i.1 := by
  simp only [IsStandard, standardExponent_iff_root_bounds]

theorem IsStandard.sub {p q : Combined R n}
    (hp : IsStandard R n p) (hq : IsStandard R n q) :
    IsStandard R n (p - q) := by
  intro a ha
  rcases Finset.mem_union.mp
      ((MvPolynomial.support_sub (Variable n) p q) ha) with hap | haq
  · exact hp a hap
  · exact hq a haq

theorem isStandard_zero : IsStandard R n (0 : Combined R n) := by
  simp [IsStandard]

/-- The corresponding staircase condition in the nested ring `R[e][x]`. -/
def IsNestedStandard (p : GeneralIdeal.Ambient R n) : Prop :=
  ∀ u ∈ p.support, ∀ i : Fin n, u i < n - i.1

/-- Currying a standard combined polynomial produces a standard outer/root
polynomial. -/
theorem isNestedStandard_unflatten_of_isStandard [Nontrivial R]
    {p : Combined R n} (hp : IsStandard R n p) :
    IsNestedStandard R n (unflatten R n p) := by
  classical
  intro u hu i
  rw [MvPolynomial.mem_support_iff] at hu
  obtain ⟨v, hv⟩ := MvPolynomial.support_nonempty.mpr hu
  have hvcoeff : coeff v (coeff u (unflatten R n p)) ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hv
  have hcombined : u.sumElim v ∈ p.support := by
    rw [MvPolynomial.mem_support_iff, ← coeff_coeff_unflatten]
    exact hvcoeff
  have hbound := (isStandard_iff_root_bounds R n p).mp hp
    (u.sumElim v) hcombined i
  simpa using hbound

section DomainEndpoint

variable [IsDomain R]

abbrev RootRing := MvPolynomial (Fin n) R

abbrev ArtinIndex := ArtinBasis.ArtinIndex n

local instance (priority := 3000) generalSymmetricRootAlgebra :
    Algebra (MvPolynomial.symmetricSubalgebra (Fin n) R) (RootRing R n) :=
  (MvPolynomial.symmetricSubalgebra (Fin n) R).val.toRingHom.toAlgebra

local instance (priority := 3000) generalSymmetricRootModule :
    Module (MvPolynomial.symmetricSubalgebra (Fin n) R) (RootRing R n) :=
  Algebra.toModule

/-- The formal coefficient ring is the symmetric subalgebra generated by
the elementary symmetric polynomials. -/
def coefficientEquiv : GeneralIdeal.Coeff R n ≃ₐ[R]
    MvPolynomial.symmetricSubalgebra (Fin n) R :=
  MvPolynomial.esymmAlgEquiv (Fin n) R (by simp)

/-- Substitute the actual elementary symmetric polynomials for the formal
coefficient variables. -/
def coefficientSpecialization : GeneralIdeal.Coeff R n →ₐ[R] RootRing R n :=
  (MvPolynomial.symmetricSubalgebra (Fin n) R).val.comp
    (coefficientEquiv R n).toAlgHom

/-- Specialization in the nested presentation. -/
def nestedSpecialization : GeneralIdeal.Ambient R n →+* RootRing R n :=
  MvPolynomial.eval₂Hom (coefficientSpecialization R n).toRingHom
    (fun i => MvPolynomial.X i)

/-- The same specialization directly from the combined ring. -/
def combinedSpecialization : Combined R n →+* RootRing R n :=
  (nestedSpecialization R n).comp (unflatten R n)

@[simp]
theorem nestedSpecialization_C (c : GeneralIdeal.Coeff R n) :
    nestedSpecialization R n (C c) = coefficientSpecialization R n c := by
  simp [nestedSpecialization]

@[simp]
theorem nestedSpecialization_X (i : Fin n) :
    nestedSpecialization R n (X i) = (X i : RootRing R n) := by
  simp [nestedSpecialization]

@[simp]
theorem coefficientSpecialization_X (i : Fin n) :
    coefficientSpecialization R n (X i) =
      (MvPolynomial.esymm (Fin n) R (i.1 + 1) : RootRing R n) := by
  change (((coefficientEquiv R n) (X i)).1 : RootRing R n) = _
  simp [coefficientEquiv, MvPolynomial.esymmAlgEquiv,
    MvPolynomial.esymmAlgHom]

/-- Turn a staircase exponent into its Artin index. -/
def artinIndexOfStandard (u : Fin n →₀ ℕ)
    (h : ∀ i : Fin n, u i < n - i.1) : ArtinIndex n :=
  fun i => ⟨u i, h i⟩

@[simp]
theorem artinExponent_artinIndexOfStandard (u : Fin n →₀ ℕ)
    (h : ∀ i : Fin n, u i < n - i.1) :
    ArtinBasis.artinExponent (artinIndexOfStandard n u h) = u := by
  ext i
  simp [artinIndexOfStandard, ArtinBasis.artinExponent_apply]

theorem artinExponent_injective :
    Function.Injective
      (ArtinBasis.artinExponent : ArtinIndex n → Fin n →₀ ℕ) := by
  intro a b hab
  funext i
  apply Fin.ext
  simpa [ArtinBasis.artinExponent_apply] using
    congrArg (fun u : Fin n →₀ ℕ => u i) hab

/-- Reassemble a nested standard polynomial from formal Artin
coordinates.  The sign matches the project's symmetric Artin basis. -/
def realizeFormalCoordinates
    (c : ArtinIndex n → GeneralIdeal.Coeff R n) :
    GeneralIdeal.Ambient R n :=
  ∑ a : ArtinIndex n,
    monomial (ArtinBasis.artinExponent a)
      (((-1 : GeneralIdeal.Coeff R n) ^ ArtinBasis.artinDegree a) * c a)

/-- Read the signed coordinate at an Artin exponent. -/
def formalCoordinates (p : GeneralIdeal.Ambient R n)
    (a : ArtinIndex n) : GeneralIdeal.Coeff R n :=
  ((-1 : GeneralIdeal.Coeff R n) ^ ArtinBasis.artinDegree a) *
    coeff (ArtinBasis.artinExponent a) p

/-- Evaluate formal Artin coordinates in the root polynomial ring. -/
def realizeCoordinates (c : ArtinIndex n → GeneralIdeal.Coeff R n) :
    RootRing R n :=
  (ArtinModule.symmetricArtinBasis R n).equivFun.symm
    (fun a => coefficientEquiv R n (c a))

theorem coeff_realizeFormalCoordinates
    (c : ArtinIndex n → GeneralIdeal.Coeff R n) (a : ArtinIndex n) :
    coeff (ArtinBasis.artinExponent a) (realizeFormalCoordinates R n c) =
      ((-1 : GeneralIdeal.Coeff R n) ^ ArtinBasis.artinDegree a) * c a := by
  classical
  simp only [realizeFormalCoordinates, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [(artinExponent_injective n).eq_iff, hba]
  · simp

/-- A nested staircase polynomial is recovered from its formal Artin
coordinates. -/
theorem realize_formalCoordinates_of_nestedStandard
    (p : GeneralIdeal.Ambient R n) (hp : IsNestedStandard R n p) :
    realizeFormalCoordinates R n (formalCoordinates R n p) = p := by
  classical
  ext u
  by_cases hu : u ∈ p.support
  · let a : ArtinIndex n :=
      artinIndexOfStandard n u (fun i => hp u hu i)
    have ha : ArtinBasis.artinExponent a = u :=
      artinExponent_artinIndexOfStandard n u (fun i => hp u hu i)
    rw [← ha, coeff_realizeFormalCoordinates, formalCoordinates,
      ← mul_assoc, ← pow_add,
      (Even.add_self (ArtinBasis.artinDegree a)).neg_one_pow, one_mul]
  · have hcoeff : coeff u p = 0 := MvPolynomial.notMem_support_iff.mp hu
    rw [hcoeff]
    simp only [realizeFormalCoordinates, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : ArtinBasis.artinExponent a = u
    · rw [if_pos ha, formalCoordinates, ha, hcoeff, mul_zero, mul_zero]
      simp
    · rw [if_neg ha]
      simp

theorem nestedSpecialization_monomial (u : Fin n →₀ ℕ)
    (c : GeneralIdeal.Coeff R n) :
    nestedSpecialization R n (monomial u c) =
      coefficientSpecialization R n c * monomial u (1 : R) := by
  rw [nestedSpecialization, MvPolynomial.eval₂Hom_monomial,
    ← MvPolynomial.monic_monomial_eq]
  rfl

/-- Specialization takes formal Artin realization to the actual symmetric
Artin-basis realization, coordinate by coordinate. -/
theorem nestedSpecialization_realizeFormalCoordinates
    (c : ArtinIndex n → GeneralIdeal.Coeff R n) :
    nestedSpecialization R n (realizeFormalCoordinates R n c) =
      realizeCoordinates R n c := by
  classical
  rw [realizeFormalCoordinates, map_sum, realizeCoordinates,
    Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [nestedSpecialization_monomial,
    ArtinModule.symmetricArtinBasis_apply_eq_monomial]
  simp [coefficientSpecialization, Algebra.smul_def,
    MvPolynomial.monomial_eq, mul_assoc, mul_left_comm, mul_comm]
  left
  exact (Subalgebra.algebraMap_apply
    (MvPolynomial.symmetricSubalgebra (Fin n) R)
    (coefficientEquiv R n (c a))).symm

/-- The nested specialization is injective on staircase-supported
polynomials. -/
theorem nestedSpecialization_injective_on_standard
    {p q : GeneralIdeal.Ambient R n}
    (hp : IsNestedStandard R n p) (hq : IsNestedStandard R n q)
    (hmap : nestedSpecialization R n p = nestedSpecialization R n q) :
    p = q := by
  have hpcoords :
      realizeCoordinates R n (formalCoordinates R n p) =
        nestedSpecialization R n p := by
    rw [← nestedSpecialization_realizeFormalCoordinates,
      realize_formalCoordinates_of_nestedStandard R n p hp]
  have hqcoords :
      realizeCoordinates R n (formalCoordinates R n q) =
        nestedSpecialization R n q := by
    rw [← nestedSpecialization_realizeFormalCoordinates,
      realize_formalCoordinates_of_nestedStandard R n q hq]
  have hcoords : formalCoordinates R n p = formalCoordinates R n q := by
    have h :
        (fun a => coefficientEquiv R n (formalCoordinates R n p a)) =
          (fun a => coefficientEquiv R n (formalCoordinates R n q a)) := by
      apply (ArtinModule.symmetricArtinBasis R n).equivFun.symm.injective
      simpa [realizeCoordinates] using
        (hpcoords.trans (hmap.trans hqcoords.symm))
    funext a
    apply (coefficientEquiv R n).injective
    exact congrFun h a
  rw [← realize_formalCoordinates_of_nestedStandard R n p hp,
    ← realize_formalCoordinates_of_nestedStandard R n q hq, hcoords]

/-- Consequently the combined specialization is injective on standard
polynomials. -/
theorem combinedSpecialization_injective_on_standard
    {p q : Combined R n} (hp : IsStandard R n p) (hq : IsStandard R n q)
    (hmap : combinedSpecialization R n p =
      combinedSpecialization R n q) : p = q := by
  apply (MvPolynomial.sumRingEquiv R (Fin n) (Fin n)).injective
  apply nestedSpecialization_injective_on_standard R n
    (isNestedStandard_unflatten_of_isStandard R n hp)
    (isNestedStandard_unflatten_of_isStandard R n hq)
  simpa [combinedSpecialization] using hmap

theorem nestedSpecialization_esymm (d : ℕ) :
    nestedSpecialization R n
        (MvPolynomial.esymm (Fin n) (GeneralIdeal.Coeff R n) d) =
      MvPolynomial.esymm (Fin n) R d := by
  simp [nestedSpecialization, MvPolynomial.esymm]

/-- Every formal Vieta relation vanishes under specialization. -/
theorem nestedSpecialization_vietaRelation (i : Fin n) :
    nestedSpecialization R n (GeneralIdeal.vietaRelation R n i) = 0 := by
  rw [GeneralIdeal.vietaRelation, map_sub, nestedSpecialization_esymm]
  simp [GeneralIdeal.e]

/-- Hence each literal nested displayed relation vanishes. -/
theorem nestedSpecialization_printedDisplayedJ (k : Fin n) :
    nestedSpecialization R n (GeneralIdeal.printedDisplayedJ R n k) = 0 := by
  rw [GeneralIdeal.printedDisplayedJ_eq_displayedJ]
  simp [GeneralIdeal.displayedJ, nestedSpecialization_vietaRelation]

/-- The same vanishing statement in the combined ring. -/
theorem combinedSpecialization_printedDisplayedJ (k : Fin n) :
    combinedSpecialization R n (printedDisplayedJ R n k) = 0 := by
  rw [← combined_printedDisplayedJ_eq_unconditional]
  simpa [combinedSpecialization] using
    nestedSpecialization_printedDisplayedJ R n k

/-- The ideal generated by the literal combined-variable displayed family. -/
def combinedDisplayedIdeal : Ideal (Combined R n) :=
  Ideal.span (Set.range (printedDisplayedJ R n))

theorem printedDisplayedJ_mem_combinedDisplayedIdeal (k : Fin n) :
    printedDisplayedJ R n k ∈ combinedDisplayedIdeal R n :=
  Ideal.subset_span (Set.mem_range_self k)

/-- The displayed ideal is contained in the specialization kernel. -/
theorem combinedDisplayedIdeal_le_specialization_ker :
    combinedDisplayedIdeal R n ≤ RingHom.ker (combinedSpecialization R n) := by
  apply Ideal.span_le.2
  rintro _ ⟨k, rfl⟩
  exact combinedSpecialization_printedDisplayedJ R n k

theorem linearCombination_printedDisplayedJ_mem
    (g : Fin n →₀ Combined R n) :
    Finsupp.linearCombination (Combined R n)
      (printedDisplayedJ R n) g ∈ combinedDisplayedIdeal R n := by
  classical
  rw [Finsupp.linearCombination_apply]
  change (∑ k ∈ g.support, g k • printedDisplayedJ R n k) ∈
    combinedDisplayedIdeal R n
  apply Ideal.sum_mem
  intro k _
  change g k * printedDisplayedJ R n k ∈ combinedDisplayedIdeal R n
  exact Ideal.mul_mem_left _ _
    (printedDisplayedJ_mem_combinedDisplayedIdeal R n k)

/-- Two standard representatives of one displayed-ideal class are equal. -/
theorem standard_remainder_unique (p r s : Combined R n)
    (hr : IsStandard R n r) (hs : IsStandard R n s)
    (hpr : p - r ∈ combinedDisplayedIdeal R n)
    (hps : p - s ∈ combinedDisplayedIdeal R n) : r = s := by
  have hrs : r - s ∈ combinedDisplayedIdeal R n := by
    have h := Ideal.sub_mem (combinedDisplayedIdeal R n) hps hpr
    convert h using 1 <;> ring
  have hzero : combinedSpecialization R n (r - s) = 0 :=
    RingHom.mem_ker.mp
      (combinedDisplayedIdeal_le_specialization_ker R n hrs)
  apply combinedSpecialization_injective_on_standard R n hr hs
  rw [← sub_eq_zero, ← map_sub]
  exact hzero

/-- Every polynomial has a unique standard remainder modulo the displayed
ideal.  Existence is Mathlib division; uniqueness is the Artin-basis
specialization argument above. -/
theorem exists_unique_standard_remainder
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (p : Combined R n) :
    ∃ (g : Fin n →₀ Combined R n) (r : Combined R n),
      p = Finsupp.linearCombination (Combined R n)
          (printedDisplayedJ R n) g + r ∧
      IsStandard R n r ∧
      (∀ k, m.degree (printedDisplayedJ R n k * g k) ≼[m]
        m.degree p) ∧
      ∀ s : Combined R n, IsStandard R n s →
        p - s ∈ combinedDisplayedIdeal R n → s = r := by
  obtain ⟨g, r, hdecomp, hdegree, hstandard⟩ :=
    exists_standard_remainder R n hm p
  have hr : IsStandard R n r := fun a ha k => hstandard a ha k
  have hpr : p - r ∈ combinedDisplayedIdeal R n := by
    rw [hdecomp]
    simpa using linearCombination_printedDisplayedJ_mem R n g
  refine ⟨g, r, hdecomp, hr, hdegree, ?_⟩
  intro s hs hps
  exact standard_remainder_unique R n p s r hs hr hps hpr

/-- For any standard representative `r` congruent to `p`, membership of
`p` in the displayed ideal is equivalent to `r = 0`. -/
theorem standard_remainder_eq_zero_iff_mem
    (p r : Combined R n) (hr : IsStandard R n r)
    (hpr : p - r ∈ combinedDisplayedIdeal R n) :
    r = 0 ↔ p ∈ combinedDisplayedIdeal R n := by
  constructor
  · intro hr0
    subst r
    simpa using hpr
  · intro hp
    have hrmem : r ∈ combinedDisplayedIdeal R n := by
      have h := Ideal.sub_mem (combinedDisplayedIdeal R n) hp hpr
      convert h using 1 <;> ring
    have hrzero : combinedSpecialization R n r = 0 :=
      RingHom.mem_ker.mp
        (combinedDisplayedIdeal_le_specialization_ker R n hrmem)
    apply combinedSpecialization_injective_on_standard R n hr
      (isStandard_zero R n)
    simpa using hrzero

/-- The division remainder is zero exactly for members of the displayed
ideal. -/
theorem exists_standard_remainder_with_membership_criterion
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) (p : Combined R n) :
    ∃ (g : Fin n →₀ Combined R n) (r : Combined R n),
      p = Finsupp.linearCombination (Combined R n)
          (printedDisplayedJ R n) g + r ∧
      IsStandard R n r ∧
      (p ∈ combinedDisplayedIdeal R n ↔ r = 0) := by
  obtain ⟨g, r, hdecomp, hr, _, _⟩ :=
    exists_unique_standard_remainder R n hm p
  have hpr : p - r ∈ combinedDisplayedIdeal R n := by
    rw [hdecomp]
    simpa using linearCombination_printedDisplayedJ_mem R n g
  exact ⟨g, r, hdecomp, hr,
    (standard_remainder_eq_zero_iff_mem R n p r hr hpr).symm⟩

/-- The combined displayed ideal is exactly the kernel of elementary-
symmetric specialization. -/
theorem combinedSpecialization_ker_eq_combinedDisplayedIdeal
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) :
    RingHom.ker (combinedSpecialization R n) =
      combinedDisplayedIdeal R n := by
  apply le_antisymm
  · intro p hp
    obtain ⟨g, r, hdecomp, hr, _, _⟩ :=
      exists_unique_standard_remainder R n hm p
    have hgmem := linearCombination_printedDisplayedJ_mem R n g
    have hpg : combinedSpecialization R n
        (Finsupp.linearCombination (Combined R n)
          (printedDisplayedJ R n) g) = 0 :=
      RingHom.mem_ker.mp
        (combinedDisplayedIdeal_le_specialization_ker R n hgmem)
    have hpzero : combinedSpecialization R n p = 0 :=
      RingHom.mem_ker.mp hp
    have hrzero : combinedSpecialization R n r = 0 := by
      have h := congrArg (combinedSpecialization R n) hdecomp
      rw [map_add, hpzero, hpg, zero_add] at h
      exact h.symm
    have hr0 : r = 0 :=
      combinedSpecialization_injective_on_standard R n hr
        (isStandard_zero R n) (by simpa using hrzero)
    rw [hr0, add_zero] at hdecomp
    rw [hdecomp]
    exact hgmem
  · exact combinedDisplayedIdeal_le_specialization_ker R n

/-- Defining Gröbner property: every nonzero member of the displayed ideal
has leading exponent divisible by a displayed leading exponent. -/
theorem leadingExponent_divides_degree_of_mem
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) {p : Combined R n}
    (hp : p ∈ combinedDisplayedIdeal R n) (hp0 : p ≠ 0) :
    ∃ k : Fin n, leadingExponent n k ≤ m.degree p := by
  classical
  obtain ⟨g, r, hdecomp, hr, hdegree, _⟩ :=
    exists_unique_standard_remainder R n hm p
  have hpr : p - r ∈ combinedDisplayedIdeal R n := by
    rw [hdecomp]
    simpa using linearCombination_printedDisplayedJ_mem R n g
  have hr0 : r = 0 :=
    (standard_remainder_eq_zero_iff_mem R n p r hr hpr).mpr hp
  have hlead : m.degree p ∈ p.support := m.degree_mem_support hp0
  have hdecomp0 :
      p = Finsupp.linearCombination (Combined R n)
        (printedDisplayedJ R n) g := by
    simpa [hr0] using hdecomp
  have hlead' :
      m.degree p ∈
        (Finsupp.linearCombination (Combined R n)
          (printedDisplayedJ R n) g).support := by
    rw [← hdecomp0]
    exact hlead
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hlead'
  have hsum := MvPolynomial.support_sum hlead'
  rcases Finset.mem_biUnion.mp hsum with ⟨k, hk, hterm⟩
  have hterm' :
      m.degree p ∈
        (printedDisplayedJ R n k * g k).support := by
    simpa [smul_eq_mul, mul_comm] using hterm
  have hle :
      m.degree p ≼[m]
        m.degree (printedDisplayedJ R n k * g k) :=
    m.le_degree hterm'
  have heq :
      m.degree (printedDisplayedJ R n k * g k) = m.degree p :=
    m.toSyn.injective (le_antisymm (hdegree k) hle)
  have hproduct : printedDisplayedJ R n k * g k ≠ 0 := by
    intro hzero
    rw [hzero] at hterm'
    simpa using hterm'
  have hg : g k ≠ 0 := by
    intro hg0
    apply hproduct
    simp [hg0]
  have hb : printedDisplayedJ R n k ≠ 0 := by
    apply m.leadingCoeff_ne_zero_iff.mp
    rw [leadingCoeff_printedDisplayedJ R n hm]
    exact one_ne_zero
  have hmul := m.degree_mul hb hg
  rw [degree_printedDisplayedJ R n hm] at hmul
  refine ⟨k, ?_⟩
  rw [← heq, hmul]
  exact le_add_right le_rfl

/-- A literal reduced-Gröbner certificate for the general displayed family.

`initialDivisibility` is the defining initial-ideal property; it is not a
renaming of the division-existence theorem.  The strict S-pair
representations are retained as the usual Buchberger witnesses, while
`uniqueDivision` and `membershipRemainder` record the two canonical-normal-
form consequences. -/
structure DisplayedReducedGroebnerCertificate
    (m : MonomialOrder (Variable n)) : Prop where
  monicLeading : ∀ k : Fin n,
    m.leadingCoeff (printedDisplayedJ R n k) = 1
  leading : ∀ k : Fin n,
    m.degree (printedDisplayedJ R n k) = leadingExponent n k
  leadingMinimal : ∀ {i j : Fin n}, i ≠ j →
    ¬ leadingExponent n i ≤ leadingExponent n j
  reducedTails : ∀ k : Fin n, ∀ a ∈ (printedTail R n k).support,
    ∀ j : Fin n, ¬ leadingExponent n j ≤ a
  pairStandard : ∀ {i j : Fin n}, i ≠ j →
    PairSPolynomialStandardRepresentation R n m i j
  initialDivisibility : ∀ {p : Combined R n},
    p ∈ combinedDisplayedIdeal R n → p ≠ 0 →
      ∃ k : Fin n, leadingExponent n k ≤ m.degree p
  uniqueDivision : ∀ p : Combined R n,
    ∃ (g : Fin n →₀ Combined R n) (r : Combined R n),
      p = Finsupp.linearCombination (Combined R n)
          (printedDisplayedJ R n) g + r ∧
      IsStandard R n r ∧
      (∀ k, m.degree (printedDisplayedJ R n k * g k) ≼[m]
        m.degree p) ∧
      ∀ s : Combined R n, IsStandard R n s →
        p - s ∈ combinedDisplayedIdeal R n → s = r
  membershipRemainder : ∀ p : Combined R n,
    ∃ (g : Fin n →₀ Combined R n) (r : Combined R n),
      p = Finsupp.linearCombination (Combined R n)
          (printedDisplayedJ R n) g + r ∧
      IsStandard R n r ∧
      (p ∈ combinedDisplayedIdeal R n ↔ r = 0)
  specializationKernel :
    RingHom.ker (combinedSpecialization R n) = combinedDisplayedIdeal R n

/-- The printed family is a reduced Gröbner basis for every paper order,
over every coefficient domain. -/
theorem displayedReducedGroebnerCertificate
    {m : MonomialOrder (Variable n)}
    (hm : PaperOrderHypotheses n m) :
    DisplayedReducedGroebnerCertificate R n m where
  monicLeading := leadingCoeff_printedDisplayedJ R n hm
  leading := degree_printedDisplayedJ R n hm
  leadingMinimal := leadingExponent_not_divides_of_ne n
  reducedTails := fun k a ha j =>
    printedDisplayedJ_reduced_tails R n k ha j
  pairStandard := fun hij =>
    pairSPolynomial_standardRepresentation R n hm hij
  initialDivisibility := fun hp hp0 =>
    leadingExponent_divides_degree_of_mem R n hm hp hp0
  uniqueDivision := exists_unique_standard_remainder R n hm
  membershipRemainder :=
    exists_standard_remainder_with_membership_criterion R n hm
  specializationKernel :=
    combinedSpecialization_ker_eq_combinedDisplayedIdeal R n hm

end DomainEndpoint

/-
The core arbitrary-order theorems above are `degree_printedDisplayedJ` and
`printedDisplayedJ_reduced_tails`; they do not depend on
`PrefixCoefficientBridge`.

Mathlib currently exposes multivariate division and S-polynomials but no
named `IsGroebnerBasis` predicate.  `DisplayedReducedGroebnerCertificate`
therefore records the mathematical defining property explicitly: leading
monomial divisibility for every nonzero ideal member.  Its proof over a
domain uses the already formalized arbitrary-degree Artin module basis to
prove uniqueness of staircase representatives, and then Mathlib division to
deduce initial divisibility.  The strict pairwise S-polynomial
representations remain separate fields of the certificate; no nonexistent
library Buchberger theorem is assumed.
-/

end

end LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerGeneralOrder
