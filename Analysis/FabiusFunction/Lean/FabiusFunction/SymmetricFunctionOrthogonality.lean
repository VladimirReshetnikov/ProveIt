import FabiusFunction.CompleteHomogeneous

/-!
# Elementary and complete symmetric-function orthogonality

This module supplies the evaluated elementary symmetric functions paired with
`completeHomogeneousEval`.  Their adjoining-variable recurrences give the
division-free orthogonality identity

`sum_{k=0}^n (-1)^k e_k(a) h_(n-k)(a) = [n = 0]`

over every commutative ring.  The statement is total in the degree and in the
finite index family, including degree zero and the empty family.

## Main results

* `elementarySymmetricEval` evaluates Mathlib's `Multiset.esymm` on a finite
  family.
* `elementarySymmetricEval_eq_eval_esymm` identifies this evaluator with
  Mathlib's universal `MvPolynomial.esymm`.
* `elementarySymmetricEval_comp_equiv` makes reindexing invariance explicit.
* `elementarySymmetricEval_option_succ` and
  `elementarySymmetricEval_fin_succ` adjoin one distinguished variable.
* `sum_elementarySymmetricEval_mul_completeHomogeneousEval` is the total
  elementary--complete orthogonality identity.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Multiset

noncomputable section

/-- Evaluation of the `n`th elementary symmetric polynomial at a finite
family `a`. -/
def elementarySymmetricEval
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) : R := by
  classical
  exact (Finset.univ.val.map a).esymm n

/-- `elementarySymmetricEval` is precisely the evaluation of Mathlib's
universal `MvPolynomial.esymm`. -/
theorem elementarySymmetricEval_eq_eval_esymm
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    elementarySymmetricEval a n =
      (by
        classical
        exact MvPolynomial.eval a (MvPolynomial.esymm ι R n)) := by
  classical
  change (Finset.univ.val.map a).esymm n =
    MvPolynomial.eval a (MvPolynomial.esymm ι R n)
  rw [← MvPolynomial.aeval_eq_eval]
  exact (MvPolynomial.aeval_esymm_eq_multiset_esymm ι R n a).symm

/-- The elementary symmetric polynomial of degree zero is one. -/
@[simp]
theorem elementarySymmetricEval_zero
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) : elementarySymmetricEval a 0 = 1 := by
  classical
  simp [elementarySymmetricEval, Multiset.esymm]

/-- Reindexing a finite family by an equivalence does not change its
elementary symmetric evaluation. -/
theorem elementarySymmetricEval_comp_equiv
    {R ι κ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : κ → R) (n : ℕ) :
    elementarySymmetricEval (a ∘ e) n =
      elementarySymmetricEval a n := by
  classical
  unfold elementarySymmetricEval
  congr 1
  rw [← Multiset.map_map]
  congr 1
  ext x
  simp

private theorem esymm_cons
    {R : Type*} [CommSemiring R] (x : R) (s : Multiset R) (n : ℕ) :
    (x ::ₘ s).esymm (n + 1) =
      x * s.esymm n + s.esymm (n + 1) := by
  simp [Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.sum_map_mul_left, add_comm]

/-- Adjoining a distinguished variable gives

`e_(n+1)(x, a) = x * e_n(a) + e_(n+1)(a)`.
-/
theorem elementarySymmetricEval_option_succ
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : Option ι → R) (n : ℕ) :
    elementarySymmetricEval a (n + 1) =
      a none * elementarySymmetricEval (a ∘ some) n +
        elementarySymmetricEval (a ∘ some) (n + 1) := by
  classical
  simp [elementarySymmetricEval, univ_option, Finset.insertNone,
    esymm_cons]

/-- Splitting the first variable from a nonempty `Fin` family gives the
head--tail recurrence for elementary symmetric evaluations. -/
theorem elementarySymmetricEval_fin_succ
    {R : Type*} [CommSemiring R] {r : ℕ}
    (a : Fin (r + 1) → R) (n : ℕ) :
    elementarySymmetricEval a (n + 1) =
      a 0 * elementarySymmetricEval (fun j : Fin r ↦ a j.succ) n +
        elementarySymmetricEval (fun j : Fin r ↦ a j.succ) (n + 1) := by
  let b : Option (Fin r) → R :=
    Option.elim' (a 0) (fun j ↦ a j.succ)
  have hba : b ∘ finSuccEquiv r = a := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [b]
    · simp [b]
  have hreindex (d : ℕ) :
      elementarySymmetricEval a d = elementarySymmetricEval b d := by
    rw [← hba]
    exact elementarySymmetricEval_comp_equiv (finSuccEquiv r) b d
  calc
    elementarySymmetricEval a (n + 1) =
        elementarySymmetricEval b (n + 1) := hreindex (n + 1)
    _ = b none * elementarySymmetricEval (b ∘ some) n +
        elementarySymmetricEval (b ∘ some) (n + 1) :=
      elementarySymmetricEval_option_succ b n
    _ = a 0 * elementarySymmetricEval (fun j : Fin r ↦ a j.succ) n +
        elementarySymmetricEval (fun j : Fin r ↦ a j.succ) (n + 1) := by
      rfl

private def elementaryCompleteConvolution
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : ι → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : R) ^ k * elementarySymmetricEval a k *
      completeHomogeneousEval a (n - k)

private theorem elementaryCompleteConvolution_comp_equiv
    {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : κ → R) (n : ℕ) :
    elementaryCompleteConvolution (a ∘ e) n =
      elementaryCompleteConvolution a n := by
  unfold elementaryCompleteConvolution
  apply Finset.sum_congr rfl
  intro k _hk
  rw [elementarySymmetricEval_comp_equiv,
    completeHomogeneousEval_comp_equiv]

private theorem elementaryCompleteConvolution_option
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : Option ι → R) (n : ℕ) :
    elementaryCompleteConvolution a n =
      elementaryCompleteConvolution (a ∘ some) n := by
  let b : ι → R := a ∘ some
  let x : R := a none
  cases n with
  | zero => simp [elementaryCompleteConvolution]
  | succ n =>
      let A : ℕ → ℕ → R := fun d k ↦
        (-1 : R) ^ k * elementarySymmetricEval a k *
          completeHomogeneousEval a (d - k)
      let B : ℕ → ℕ → R := fun d k ↦
        (-1 : R) ^ k * elementarySymmetricEval b k *
          completeHomogeneousEval a (d - k)
      let C : ℕ → ℕ → R := fun d k ↦
        (-1 : R) ^ k * elementarySymmetricEval b k *
          completeHomogeneousEval b (d - k)
      have hEA (k : ℕ) :
          elementarySymmetricEval a (k + 1) =
            x * elementarySymmetricEval b k +
              elementarySymmetricEval b (k + 1) := by
        simpa only [b, x] using elementarySymmetricEval_option_succ a k
      have hHA (k : ℕ) :
          completeHomogeneousEval a (k + 1) =
            x * completeHomogeneousEval a k +
              completeHomogeneousEval b (k + 1) := by
        simpa only [b, x] using completeHomogeneousEval_option_succ a k
      have hAhead (d : ℕ) : A d 0 = B d 0 := by
        simp [A, B]
      have hAtail (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
          A (n + 1) (k + 1) =
            B (n + 1) (k + 1) - x * B n k := by
        have hk' : k ≤ n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        simp only [A, B]
        rw [hEA, pow_succ]
        have hsub : n + 1 - (k + 1) = n - k := by omega
        rw [hsub]
        ring
      have hfirst : elementaryCompleteConvolution a (n + 1) =
          (∑ k ∈ Finset.range (n + 2), B (n + 1) k) -
            x * ∑ k ∈ Finset.range (n + 1), B n k := by
        change (∑ k ∈ Finset.range (n + 2), A (n + 1) k) = _
        calc
          (∑ k ∈ Finset.range (n + 2), A (n + 1) k) =
              (∑ k ∈ Finset.range (n + 1), A (n + 1) (k + 1)) +
                A (n + 1) 0 :=
            Finset.sum_range_succ' (A (n + 1)) (n + 1)
          _ = (∑ k ∈ Finset.range (n + 1),
                (B (n + 1) (k + 1) - x * B n k)) +
                B (n + 1) 0 := by
              rw [hAhead]
              apply congrArg (fun z ↦ z + B (n + 1) 0)
              apply Finset.sum_congr rfl
              exact hAtail
          _ = ((∑ k ∈ Finset.range (n + 1),
                  B (n + 1) (k + 1)) + B (n + 1) 0) -
              x * ∑ k ∈ Finset.range (n + 1), B n k := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
            ring
          _ = (∑ k ∈ Finset.range (n + 2), B (n + 1) k) -
              x * ∑ k ∈ Finset.range (n + 1), B n k := by
            rw [Finset.sum_range_succ' (B (n + 1)) (n + 1)]
      have hBlast : B (n + 1) (n + 1) = C (n + 1) (n + 1) := by
        simp [B, C]
      have hBinit (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
          B (n + 1) k = C (n + 1) k + x * B n k := by
        have hk' : k ≤ n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hsub : n + 1 - k = (n - k) + 1 := by omega
        simp only [B, C]
        rw [hsub, hHA]
        ring
      have hsecond :
          (∑ k ∈ Finset.range (n + 2), B (n + 1) k) =
            (∑ k ∈ Finset.range (n + 2), C (n + 1) k) +
              x * ∑ k ∈ Finset.range (n + 1), B n k := by
        calc
          (∑ k ∈ Finset.range (n + 2), B (n + 1) k) =
              (∑ k ∈ Finset.range (n + 1), B (n + 1) k) +
                B (n + 1) (n + 1) :=
            Finset.sum_range_succ (B (n + 1)) (n + 1)
          _ = (∑ k ∈ Finset.range (n + 1),
                (C (n + 1) k + x * B n k)) +
                C (n + 1) (n + 1) := by
              rw [hBlast]
              apply congrArg (fun z ↦ z + C (n + 1) (n + 1))
              apply Finset.sum_congr rfl
              exact hBinit
          _ = ((∑ k ∈ Finset.range (n + 1), C (n + 1) k) +
                  C (n + 1) (n + 1)) +
              x * ∑ k ∈ Finset.range (n + 1), B n k := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            ring
          _ = (∑ k ∈ Finset.range (n + 2), C (n + 1) k) +
              x * ∑ k ∈ Finset.range (n + 1), B n k := by
            rw [Finset.sum_range_succ (C (n + 1)) (n + 1)]
      rw [hfirst, hsecond]
      change
        ((∑ k ∈ Finset.range (n + 2), C (n + 1) k) +
            x * ∑ k ∈ Finset.range (n + 1), B n k) -
          x * ∑ k ∈ Finset.range (n + 1), B n k =
        ∑ k ∈ Finset.range (n + 2), C (n + 1) k
      ring

private theorem elementaryCompleteConvolution_eq_delta
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    elementaryCompleteConvolution a n =
      if n = 0 then 1 else 0 := by
  let P : (ι : Type _) → [Fintype ι] → Prop := fun ι _ ↦
    ∀ (a : ι → R) (n : ℕ),
      elementaryCompleteConvolution a n = if n = 0 then 1 else 0
  apply Fintype.induction_empty_option (P := P)
  · intro α β instβ e hα a n
    letI : Fintype α := @Fintype.ofEquiv α β instβ e.symm
    rw [← elementaryCompleteConvolution_comp_equiv e a n]
    exact hα (a ∘ e) n
  · intro a n
    cases n with
    | zero => simp [elementaryCompleteConvolution]
    | succ n =>
        rw [if_neg (Nat.succ_ne_zero n)]
        unfold elementaryCompleteConvolution
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hk0 : k = 0
        · subst k
          simp
        · have he : elementarySymmetricEval a k = 0 := by
            obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
            simp [elementarySymmetricEval, Multiset.esymm]
          rw [he]
          ring
  · intro α inst hα a n
    rw [elementaryCompleteConvolution_option]
    exact hα (a ∘ some) n

/-- **Elementary--complete symmetric-function orthogonality.**  For every
finite family over a commutative ring,

`sum_(k=0)^n (-1)^k e_k(a) h_(n-k)(a) = [n = 0]`.

The statement includes degree zero and the empty family and uses no division,
characteristic, domain, or nonvanishing hypothesis. -/
theorem sum_elementarySymmetricEval_mul_completeHomogeneousEval
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ k * elementarySymmetricEval a k *
        completeHomogeneousEval a (n - k)) =
      if n = 0 then 1 else 0 := by
  exact elementaryCompleteConvolution_eq_delta a n

end

end Fabius
