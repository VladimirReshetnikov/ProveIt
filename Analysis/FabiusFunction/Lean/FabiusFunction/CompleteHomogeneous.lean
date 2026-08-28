import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Ring

/-!
# Evaluated complete homogeneous symmetric polynomials

Mathlib's `MvPolynomial.hsymm` is the universal complete homogeneous
symmetric polynomial.  This module supplies its finite-family evaluation API:
an explicit multiset sum, the recurrence obtained by adjoining one variable,
and a polynomial in one distinguished variable.

The evaluation and quotient recurrences are developed over an arbitrary
commutative semiring; the linear-factor identity uses a commutative ring only
because it contains subtraction.  No division, characteristic-zero
hypothesis, topology, or ordering is involved.  The resulting polynomial is
the natural quotient in all higher Lagrange and Richardson residual moments.

## Main results

* `completeHomogeneousEval_eq_sum_sym` is the explicit multiset formula.
* `completeHomogeneousEval_eq_eval_hsymm` identifies Mathlib's universal
  symmetric polynomial with this evaluation API.
* `completeHomogeneousEval_smul` records homogeneity under a common scale.
* `completeHomogeneousEval_option_succ` adjoins one distinguished variable.
* `completeHomogeneousEval_option_zero` removes an adjoined zero variable.
* `completeHomogeneousQuotient` packages `h_n(X, a_1, ..., a_d)` as a
  univariate polynomial.
* `eval_completeHomogeneousQuotient` evaluates that polynomial as the
  complete homogeneous function of the target together with the family.
-/

set_option autoImplicit false

open scoped BigOperators Polynomial

namespace Fabius

open Finset Multiset Sym

noncomputable section

/-- Evaluation of the `n`th complete homogeneous symmetric polynomial at a
finite family `a`.  The index type supplies the variables; repetitions in a
degree-`n` monomial are encoded by `Sym ι n`. -/
def completeHomogeneousEval
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) : R := by
  classical
  exact ∑ m : Sym ι n, (m.1.map a).prod

/-- Explicit multiset formula for the evaluated complete homogeneous
symmetric polynomial. -/
theorem completeHomogeneousEval_eq_sum_sym
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    completeHomogeneousEval a n =
      (by
        classical
        exact ∑ m : Sym ι n, (m.1.map a).prod) := by
  rfl

/-- `completeHomogeneousEval` is precisely the evaluation of Mathlib's
universal `MvPolynomial.hsymm`. -/
theorem completeHomogeneousEval_eq_eval_hsymm
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    completeHomogeneousEval a n =
      (by
        classical
        exact MvPolynomial.eval a (MvPolynomial.hsymm ι R n)) := by
  classical
  symm
  simp [completeHomogeneousEval, MvPolynomial.hsymm,
    ← Multiset.prod_hom']

/-- The complete homogeneous polynomial of degree zero is one. -/
@[simp]
theorem completeHomogeneousEval_zero
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) : completeHomogeneousEval a 0 = 1 := by
  classical
  simp [completeHomogeneousEval, Sym.eq_nil_of_card_zero]

/-- In degree one, the complete homogeneous polynomial is the sum of its
variables. -/
@[simp]
theorem completeHomogeneousEval_one
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) : completeHomogeneousEval a 1 = ∑ i, a i := by
  classical
  rw [completeHomogeneousEval_eq_eval_hsymm]
  simp

/-- A positive-degree complete homogeneous polynomial in no variables
vanishes. -/
@[simp]
theorem completeHomogeneousEval_isEmpty_succ
    {R ι : Type*} [CommSemiring R] [Fintype ι] [IsEmpty ι]
    (a : ι → R) (n : ℕ) : completeHomogeneousEval a (n + 1) = 0 := by
  classical
  simp [completeHomogeneousEval]

/-- Reindexing a finite family by an equivalence does not change its complete
homogeneous evaluation. -/
theorem completeHomogeneousEval_comp_equiv
    {R ι κ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : κ → R) (n : ℕ) :
    completeHomogeneousEval (a ∘ e) n =
      completeHomogeneousEval a n := by
  classical
  unfold completeHomogeneousEval
  apply Fintype.sum_equiv (Sym.equivCongr e)
  intro m
  simp [Multiset.map_map]

/-- Complete homogeneous evaluation commutes with homomorphisms of
commutative semirings. -/
theorem map_completeHomogeneousEval
    {R S ι : Type*} [CommSemiring R] [CommSemiring S] [Fintype ι]
    (f : R →+* S) (a : ι → R) (n : ℕ) :
    f (completeHomogeneousEval a n) =
      completeHomogeneousEval (fun i ↦ f (a i)) n := by
  classical
  simp [completeHomogeneousEval, map_sum, ← Multiset.prod_hom']

/-- Scaling every variable by `c` scales the degree-`n` complete homogeneous
evaluation by `c ^ n`.

This is valid over every commutative semiring; no cancellation or
nonzeroness assumption on `c` is needed. -/
theorem completeHomogeneousEval_smul
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (c : R) (a : ι → R) (n : ℕ) :
    completeHomogeneousEval (fun i ↦ c * a i) n =
      c ^ n * completeHomogeneousEval a n := by
  classical
  unfold completeHomogeneousEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  have hp (s : Multiset ι) :
      (s.map (fun i ↦ c * a i)).prod =
        c ^ s.card * (s.map a).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons i s ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons,
          Multiset.card_cons, ih, pow_succ]
        ac_rfl
  simpa only [m.2] using hp m.1

private theorem sum_sym_option_succ
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] [DecidableEq (Option ι)]
    (a : Option ι → R) (n : ℕ) :
    (∑ m : Sym (Option ι) (n + 1), (m.1.map a).prod) =
      a none * ∑ m : Sym (Option ι) n, (m.1.map a).prod +
        ∑ m : Sym ι (n + 1), (m.1.map (a ∘ some)).prod := by
  let e := symOptionSuccEquiv (α := ι) (n := n)
  let g : Sym (Option ι) n ⊕ Sym ι (n + 1) → R
    | Sum.inl m => a none * (m.1.map a).prod
    | Sum.inr m => (m.1.map (a ∘ some)).prod
  have htransport :
      (∑ y, g y) =
        ∑ m : Sym (Option ι) (n + 1), (m.1.map a).prod := by
    apply Fintype.sum_equiv e.symm
    intro y
    rcases y with m | m
    · change a none * (m.1.map a).prod =
        ((none ::ₘ m.1).map a).prod
      rw [Multiset.map_cons, Multiset.prod_cons]
    · change (m.1.map (a ∘ some)).prod =
        ((m.1.map some).map a).prod
      rw [Multiset.map_map]
  refine htransport.symm.trans ?_
  simpa only [g, Finset.mul_sum] using Fintype.sum_sum_type g

/-- Adjoining one distinguished variable gives the fundamental recurrence

`h_(n+1)(x, a) = x * h_n(x, a) + h_(n+1)(a)`.

The proof is the canonical decomposition of a multiset of size `n + 1`
according to whether it contains the distinguished `none` variable. -/
theorem completeHomogeneousEval_option_succ
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : Option ι → R) (n : ℕ) :
    completeHomogeneousEval a (n + 1) =
      a none * completeHomogeneousEval a n +
        completeHomogeneousEval (a ∘ some) (n + 1) := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : DecidableEq (Option ι) := Classical.decEq (Option ι)
  simpa only [completeHomogeneousEval] using sum_sym_option_succ a n

/-- Adjoining a zero variable does not change a complete homogeneous
evaluation. -/
@[simp]
theorem completeHomogeneousEval_option_zero
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    completeHomogeneousEval (Option.elim' 0 a) n =
      completeHomogeneousEval a n := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [Function.comp_def] using
        completeHomogeneousEval_option_succ
          (Option.elim' (0 : R) a) n

/-- Splitting the first variable from a nonempty `Fin` family gives the
head--tail recurrence for complete homogeneous evaluations. -/
theorem completeHomogeneousEval_fin_succ
    {R : Type*} [CommSemiring R] {r : ℕ}
    (a : Fin (r + 1) → R) (n : ℕ) :
    completeHomogeneousEval a (n + 1) =
      a 0 * completeHomogeneousEval a n +
        completeHomogeneousEval (fun j : Fin r ↦ a j.succ) (n + 1) := by
  let b : Option (Fin r) → R :=
    Option.elim' (a 0) (fun j ↦ a j.succ)
  have hba : b ∘ finSuccEquiv r = a := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [b]
    · simp [b]
  have hreindex (d : ℕ) :
      completeHomogeneousEval a d = completeHomogeneousEval b d := by
    rw [← hba]
    exact completeHomogeneousEval_comp_equiv (finSuccEquiv r) b d
  calc
    completeHomogeneousEval a (n + 1) =
        completeHomogeneousEval b (n + 1) := hreindex (n + 1)
    _ = b none * completeHomogeneousEval b n +
        completeHomogeneousEval (b ∘ some) (n + 1) :=
      completeHomogeneousEval_option_succ b n
    _ = a 0 * completeHomogeneousEval a n +
        completeHomogeneousEval (fun j : Fin r ↦ a j.succ) (n + 1) := by
      rw [hreindex n]
      rfl

/-- Complete homogeneous evaluation on a `Finset`, with the variables
indexed by its subtype. -/
def completeHomogeneousEvalOn
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (n : ℕ) : R :=
  completeHomogeneousEval (fun i : s ↦ a i) n

/-- Evaluation on the natural-number range `0, ..., n - 1` is the same as
evaluation on the canonically equivalent type `Fin n`. -/
theorem completeHomogeneousEvalOn_range
    {R : Type*} [CommSemiring R]
    (a : ℕ → R) (n d : ℕ) :
    completeHomogeneousEvalOn (Finset.range n) a d =
      completeHomogeneousEval (fun i : Fin n ↦ a i) d := by
  let e : (Finset.range n : Finset ℕ) ≃ Fin n :=
    { toFun := fun i ↦ ⟨i.1, Finset.mem_range.mp i.2⟩
      invFun := fun i ↦ ⟨i.1, Finset.mem_range.mpr i.2⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  change completeHomogeneousEval (fun i : Finset.range n ↦ a i) d =
    completeHomogeneousEval (fun i : Fin n ↦ a i) d
  have hfun : (fun i : Finset.range n ↦ a i) =
      (fun i : Fin n ↦ a i) ∘ e := by
    rfl
  rw [hfun]
  exact completeHomogeneousEval_comp_equiv e (fun i : Fin n ↦ a i) d

/-- Complete homogeneous evaluation in one distinguished target variable
together with the variables indexed by `s`. -/
def completeHomogeneousEvalAt
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (x : R) (n : ℕ) : R :=
  completeHomogeneousEval (Option.elim' x (fun i : s ↦ a i)) n

/-- At target zero, the distinguished variable drops out of the complete
homogeneous evaluation. -/
@[simp]
theorem completeHomogeneousEvalAt_zero
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (n : ℕ) :
    completeHomogeneousEvalAt s a 0 n =
      completeHomogeneousEvalOn s a n := by
  simpa only [completeHomogeneousEvalAt, completeHomogeneousEvalOn] using
    completeHomogeneousEval_option_zero (R := R)
      (fun i : s ↦ a i) n

private theorem completeHomogeneousEvalOn_insert_eq_option
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (a : ι → R) (n : ℕ) :
    completeHomogeneousEvalOn (insert i s) a n =
      completeHomogeneousEval (Option.elim' (a i) (fun j : s ↦ a j)) n := by
  let e := Finset.subtypeInsertEquivOption hi
  calc
    completeHomogeneousEvalOn (insert i s) a n =
        completeHomogeneousEval
          ((fun j : (insert i s : Finset ι) ↦ a j) ∘ e.symm) n :=
      (completeHomogeneousEval_comp_equiv e.symm
        (fun j : (insert i s : Finset ι) ↦ a j) n).symm
    _ = completeHomogeneousEval
        (Option.elim' (a i) (fun j : s ↦ a j)) n := by
      congr 1
      funext j
      cases j with
      | none => rfl
      | some j => rfl

/-- Adjoining one element to a `Finset` gives the complete homogeneous
recurrence, with no distinctness requirement on the values. -/
theorem completeHomogeneousEvalOn_insert_succ
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (a : ι → R) (n : ℕ) :
    completeHomogeneousEvalOn (insert i s) a (n + 1) =
      a i * completeHomogeneousEvalOn (insert i s) a n +
        completeHomogeneousEvalOn s a (n + 1) := by
  let b : Option s → R := Option.elim' (a i) (fun j : s ↦ a j)
  have hbnone : b none = a i := rfl
  have hbsome : b ∘ some =
        (fun j : s ↦ a j) := by
    funext j
    rfl
  calc
    completeHomogeneousEvalOn (insert i s) a (n + 1) =
        completeHomogeneousEval b (n + 1) :=
      completeHomogeneousEvalOn_insert_eq_option hi a (n + 1)
    _ = b none * completeHomogeneousEval b n +
        completeHomogeneousEval (b ∘ some) (n + 1) :=
      completeHomogeneousEval_option_succ b n
    _ = a i * completeHomogeneousEvalOn (insert i s) a n +
        completeHomogeneousEvalOn s a (n + 1) := by
      rw [hbnone, hbsome,
        ← completeHomogeneousEvalOn_insert_eq_option hi a n]
      rfl

/-- The target-plus-family complete homogeneous functions inherit the
one-variable adjoining recurrence. -/
theorem completeHomogeneousEvalAt_succ
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (x : R) (n : ℕ) :
    completeHomogeneousEvalAt s a x (n + 1) =
      x * completeHomogeneousEvalAt s a x n +
        completeHomogeneousEvalOn s a (n + 1) := by
  let b : Option s → R := Option.elim' x (fun i : s ↦ a i)
  have hbnone : b none = x := rfl
  have hbsome : b ∘ some =
        (fun i : s ↦ a i) := by
    funext i
    rfl
  change completeHomogeneousEval b (n + 1) =
    x * completeHomogeneousEval b n +
      completeHomogeneousEval (fun i : s ↦ a i) (n + 1)
  rw [completeHomogeneousEval_option_succ, hbnone, hbsome]

/-- The univariate polynomial `h_n(X, a_1, ..., a_d)`, characterized by

`Q_0 = 1`,  `Q_(n+1) = X * Q_n + C(h_(n+1)(a_1, ..., a_d))`.

Equivalently, `Q_n = sum_{k=0}^n C(h_k(a)) X^(n-k)`.  It is defined over any
commutative semiring and has no distinctness requirement on the family. -/
def completeHomogeneousQuotient
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) : ℕ → R[X]
  | 0 => 1
  | n + 1 => Polynomial.X * completeHomogeneousQuotient s a n +
      Polynomial.C (completeHomogeneousEvalOn s a (n + 1))

/-- The quotient polynomial starts at one. -/
@[simp]
theorem completeHomogeneousQuotient_zero
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) :
    completeHomogeneousQuotient s a 0 = 1 := by
  rw [completeHomogeneousQuotient]

/-- The quotient polynomials obey the same adjoining-variable recurrence as
the complete homogeneous functions. -/
theorem completeHomogeneousQuotient_succ
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (n : ℕ) :
    completeHomogeneousQuotient s a (n + 1) =
      Polynomial.X * completeHomogeneousQuotient s a n +
        Polynomial.C (completeHomogeneousEvalOn s a (n + 1)) := by
  rw [completeHomogeneousQuotient]

/-- With no family variables, the distinguished-variable polynomial is the
corresponding monomial. -/
@[simp]
theorem completeHomogeneousQuotient_empty
    {R ι : Type*} [CommSemiring R]
    (a : ι → R) (n : ℕ) :
    completeHomogeneousQuotient (∅ : Finset ι) a n =
      Polynomial.X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [completeHomogeneousQuotient_succ, ih]
      simp [completeHomogeneousEvalOn, pow_succ, mul_comm]

/-- Splitting off one family member factors the complete homogeneous
polynomial through the corresponding linear factor. -/
theorem completeHomogeneousQuotient_insert
    {R ι : Type*} [CommRing R] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (a : ι → R) (n : ℕ) :
    completeHomogeneousQuotient s a (n + 1) =
      (Polynomial.X - Polynomial.C (a i)) *
          completeHomogeneousQuotient (insert i s) a n +
        Polynomial.C
          (completeHomogeneousEvalOn (insert i s) a (n + 1)) := by
  induction n with
  | zero =>
      rw [completeHomogeneousQuotient_succ s a 0,
        completeHomogeneousQuotient_zero s a,
        completeHomogeneousQuotient_zero (insert i s) a,
        completeHomogeneousEvalOn_insert_succ hi a 0]
      simp only [completeHomogeneousEvalOn,
        completeHomogeneousEval_zero, mul_one,
        Polynomial.C_add]
      ring
  | succ n ih =>
      rw [completeHomogeneousQuotient_succ s a (n + 1), ih,
        completeHomogeneousQuotient_succ (insert i s) a n,
        completeHomogeneousEvalOn_insert_succ hi a (n + 1)]
      simp only [Polynomial.C_add, Polynomial.C_mul]
      ring

/-- Evaluating `completeHomogeneousQuotient` at `x` gives the complete
homogeneous function in `x` together with all variables indexed by `s`. -/
theorem eval_completeHomogeneousQuotient
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (x : R) (n : ℕ) :
    (completeHomogeneousQuotient s a n).eval x =
      completeHomogeneousEvalAt s a x n := by
  induction n with
  | zero =>
      rw [completeHomogeneousQuotient_zero, Polynomial.eval_one,
        completeHomogeneousEvalAt, completeHomogeneousEval_zero]
  | succ n ih =>
      calc
        (completeHomogeneousQuotient s a (n + 1)).eval x =
            x * (completeHomogeneousQuotient s a n).eval x +
              completeHomogeneousEvalOn s a (n + 1) := by
          rw [completeHomogeneousQuotient_succ,
            Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, Polynomial.eval_C]
        _ = x * completeHomogeneousEvalAt s a x n +
              completeHomogeneousEvalOn s a (n + 1) := by
          rw [ih]
        _ = completeHomogeneousEvalAt s a x (n + 1) :=
          (completeHomogeneousEvalAt_succ s a x n).symm

end

end Fabius
