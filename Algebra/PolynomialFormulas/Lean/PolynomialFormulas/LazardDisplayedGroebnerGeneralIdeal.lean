import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The general displayed family: ideal-theoretic core

This file isolates the order-free first half of Lazard's Lemma 1.  For an
arbitrary number `n` of roots and an arbitrary commutative coefficient ring,
it defines both the paper's printed complete-homogeneous triangular family
and its uniform Vieta-combination form, proves that the two agree by the
elementary/complete-homogeneous cancellation, and proves that they generate
the same ideal as the formal Vieta relations.

We index the family by its triangular degree.  If `k : Fin n`, then
`printedDisplayedJ k` (and the equal term `displayedJ k`) is the member of
root degree `k+1`; it uses the first `n-k` root variables.  Thus `k = 0`
gives `sigma₁-e₁`, while `k = n-1` gives the degree-`n` relation in
`x₀`.

The formula used here is the uniform change-of-generators identity

`J_k = sum_(j=0)^k (-1)^j h_(k-j)(x₀,...,x_(n-k-1)) (sigma_(j+1)-e_(j+1))`.

The paper's printed alternating-`e` display is defined separately below and
proved equal to this change-of-generators expression by the standard
elementary/complete-homogeneous cancellation.  The order-parametric
reduced-Groebner conclusion deliberately remains separate: the theorems below
need neither a monomial order nor division.
-/

namespace LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerGeneralIdeal

open scoped BigOperators
open Finset MvPolynomial

set_option autoImplicit false

noncomputable section

variable (R : Type*) [CommRing R]
variable (n : ℕ)

/-- The formal elementary-symmetric coefficient ring. -/
abbrev Coeff := MvPolynomial (Fin n) R

/-- Root polynomials whose coefficients are polynomials in the formal
elementary-symmetric variables. -/
abbrev Ambient := MvPolynomial (Fin n) (Coeff R n)

/-- The `i`th root variable. -/
def x (i : Fin n) : Ambient R n := X i

/-- The paper's formal coefficient `e_(i+1)`. -/
def e (i : Fin n) : Ambient R n := C (X i : Coeff R n)

/-- The formal Vieta relation `sigma_(i+1)-e_(i+1)`. -/
def vietaRelation (i : Fin n) : Ambient R n :=
  esymm (Fin n) (Coeff R n) (i.1 + 1) - e R n i

/-- Embed the first `n-k` root-variable indices in all `n` indices. -/
def prefixEmbedding (k : Fin n) : Fin (n - k.1) → Fin n :=
  Fin.castLE (Nat.sub_le n k.1)

/-- The geometric power series `1+aX+a^2X^2+...`. -/
def geometricSeries (a : Ambient R n) : PowerSeries (Ambient R n) :=
  PowerSeries.rescale a (PowerSeries.mk 1)

@[simp]
theorem geometricSeries_coeff (a : Ambient R n) (r : ℕ) :
    PowerSeries.coeff r (geometricSeries R n a) = a ^ r := by
  simp [geometricSeries]

/-- The complete-homogeneous generating series in precisely the first
`n-k` root variables. -/
def prefixCompleteSeries (k : Fin n) : PowerSeries (Ambient R n) :=
  ∏ j : Fin (n - k.1), geometricSeries R n (x R n (prefixEmbedding n k j))

/-- The complete homogeneous polynomial of degree `r` in precisely the
first `n-k` root variables, defined by its standard product-of-geometric-
series recursion.  This avoids every finite quintic expansion of the
paper's `C_r^(i)`. -/
def prefixHsymm (k : Fin n) (r : ℕ) : Ambient R n :=
  PowerSeries.coeff r (prefixCompleteSeries R n k)

@[simp]
theorem prefixHsymm_zero (k : Fin n) :
    prefixHsymm R n k 0 = 1 := by
  rw [prefixHsymm, prefixCompleteSeries,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
  apply Finset.prod_eq_one
  intro j hj
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    geometricSeries_coeff]
  simp

/-- The formal coefficient `e_r`, extended by `e_0 = 1` and by zero above
degree `n`.  The printed family only evaluates it in the range `0..n`. -/
def formalE (r : ℕ) : Ambient R n :=
  if hr : r = 0 then 1
  else if hrn : r ≤ n then e R n ⟨r - 1, by omega⟩
  else 0

@[simp]
theorem formalE_zero : formalE R n 0 = 1 := by
  simp [formalE]

@[simp]
theorem formalE_succ (r : ℕ) (hr : r < n) :
    formalE R n (r + 1) = e R n ⟨r, hr⟩ := by
  simp [formalE, Nat.succ_le_iff.mpr hr]

/-! ## Elementary/complete-homogeneous cancellation -/

/-- The linear factor `1-aX`, first as a polynomial. -/
def linearPolynomial (a : Ambient R n) : Polynomial (Ambient R n) :=
  1 - Polynomial.C a * Polynomial.X

/-- The same factor as a power series. -/
def linearSeries (a : Ambient R n) : PowerSeries (Ambient R n) :=
  (linearPolynomial R n a : PowerSeries (Ambient R n))

/-- A geometric series cancels its linear factor. -/
theorem geometricSeries_mul_linearSeries (a : Ambient R n) :
    geometricSeries R n a * linearSeries R n a = 1 := by
  have h := congrArg (fun f : PowerSeries (Ambient R n) =>
      PowerSeries.rescale a f)
    (PowerSeries.mk_one_mul_one_sub_eq_one (Ambient R n))
  simpa [geometricSeries, linearSeries, linearPolynomial,
    map_mul, map_sub, PowerSeries.rescale_X] using h

/-- The final `k` root variables, complementary to `prefixEmbedding`. -/
def suffixEmbedding (k : Fin n) : Fin k.1 → Fin n := fun j =>
  ⟨n - k.1 + j.1, by omega⟩

/-- Product of the first `n-k` linear factors. -/
def prefixLinearSeries (k : Fin n) : PowerSeries (Ambient R n) :=
  ∏ j : Fin (n - k.1),
    linearSeries R n (x R n (prefixEmbedding n k j))

/-- Product of the complementary final `k` linear factors. -/
def suffixLinearSeries (k : Fin n) : PowerSeries (Ambient R n) :=
  ∏ j : Fin k.1,
    linearSeries R n (x R n (suffixEmbedding n k j))

/-- Product of all `n` linear factors. -/
def fullLinearSeries : PowerSeries (Ambient R n) :=
  ∏ i : Fin n, linearSeries R n (x R n i)

/-- Splitting `Fin n` after the first `n-k` indices. -/
def splitIndexEquiv (k : Fin n) :
    Fin (n - k.1) ⊕ Fin k.1 ≃ Fin n :=
  finSumFinEquiv.trans
    (finCongr (Nat.sub_add_cancel (Nat.le_of_lt k.2)))

@[simp]
theorem splitIndexEquiv_inl (k : Fin n) (j : Fin (n - k.1)) :
    splitIndexEquiv n k (Sum.inl j) = prefixEmbedding n k j := by
  apply Fin.ext
  rfl

@[simp]
theorem splitIndexEquiv_inr (k : Fin n) (j : Fin k.1) :
    splitIndexEquiv n k (Sum.inr j) = suffixEmbedding n k j := by
  apply Fin.ext
  rfl

theorem fullLinearSeries_split (k : Fin n) :
    fullLinearSeries R n =
      prefixLinearSeries R n k * suffixLinearSeries R n k := by
  classical
  have hprod := Fintype.prod_equiv (splitIndexEquiv n k)
    (fun z : Fin (n - k.1) ⊕ Fin k.1 =>
      linearSeries R n (x R n (splitIndexEquiv n k z)))
    (fun i : Fin n => linearSeries R n (x R n i))
    (fun _ => rfl)
  rw [Fintype.prod_sum_type] at hprod
  simpa [fullLinearSeries, prefixLinearSeries, suffixLinearSeries] using
    hprod.symm

theorem prefixCompleteSeries_mul_prefixLinearSeries (k : Fin n) :
    prefixCompleteSeries R n k * prefixLinearSeries R n k = 1 := by
  classical
  rw [prefixCompleteSeries, prefixLinearSeries,
    ← Finset.prod_mul_distrib]
  simp [geometricSeries_mul_linearSeries]

theorem fullLinearSeries_mul_prefixCompleteSeries (k : Fin n) :
    fullLinearSeries R n * prefixCompleteSeries R n k =
      suffixLinearSeries R n k := by
  rw [fullLinearSeries_split]
  calc
    (prefixLinearSeries R n k * suffixLinearSeries R n k) *
        prefixCompleteSeries R n k =
      suffixLinearSeries R n k *
        (prefixCompleteSeries R n k * prefixLinearSeries R n k) := by
          ring
    _ = suffixLinearSeries R n k := by
      rw [prefixCompleteSeries_mul_prefixLinearSeries, mul_one]

/-- Elementary symmetric recursion for a multiset after adjoining one
element. -/
lemma multiset_esymm_cons_succ {A : Type*} [CommRing A]
    (a : A) (s : Multiset A) (r : ℕ) :
    (a ::ₘ s).esymm (r + 1) =
      s.esymm (r + 1) + a * s.esymm r := by
  simp [Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.sum_add, Multiset.sum_map_mul_left]

/-- Coefficients of a product of `1-aX` are the signed elementary
symmetric functions. -/
lemma coeff_prod_linearPolynomial {A : Type*} [CommRing A]
    (s : Multiset A) (r : ℕ) :
    (((s.map fun a =>
      (1 - Polynomial.C a * Polynomial.X : Polynomial A)).prod).coeff r) =
      (-1 : A) ^ r * s.esymm r := by
  induction s using Multiset.induction_on generalizing r with
  | empty =>
      cases r with
      | zero => simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      | succ r =>
          rw [Multiset.map_zero, Multiset.prod_zero,
            Polynomial.coeff_one, if_neg (Nat.succ_ne_zero r)]
          simp [Multiset.esymm]
  | @cons a s ih =>
      cases r with
      | zero =>
          simpa [Multiset.esymm, Multiset.powersetCard_zero_left] using ih 0
      | succ r =>
          rw [Multiset.map_cons, Multiset.prod_cons]
          have hfactor :
              (1 - Polynomial.C a * Polynomial.X) *
                  (s.map fun b =>
                    (1 - Polynomial.C b * Polynomial.X : Polynomial A)).prod =
                (s.map fun b =>
                    (1 - Polynomial.C b * Polynomial.X : Polynomial A)).prod -
                  Polynomial.C a *
                    (Polynomial.X *
                      (s.map fun b =>
                        (1 - Polynomial.C b * Polynomial.X : Polynomial A)).prod) := by
            ring
          rw [hfactor, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_mul, ih, ih,
            multiset_esymm_cons_succ, pow_succ]
          ring

/-- The coefficient of the full linear-factor series is the signed
elementary symmetric polynomial in all roots. -/
theorem fullLinearSeries_coeff (r : ℕ) :
    PowerSeries.coeff r (fullLinearSeries R n) =
      (-1 : Ambient R n) ^ r *
        esymm (Fin n) (Coeff R n) r := by
  classical
  have h := coeff_prod_linearPolynomial
    ((Finset.univ : Finset (Fin n)).val.map (x R n)) r
  rw [MvPolynomial.esymm_eq_multiset_esymm]
  rw [fullLinearSeries]
  simp_rw [linearSeries]
  have hmap :
      (∏ i : Fin n,
          (linearPolynomial R n (x R n i) : PowerSeries (Ambient R n))) =
        (((∏ i : Fin n, linearPolynomial R n (x R n i)) :
          Polynomial (Ambient R n)) : PowerSeries (Ambient R n)) := by
    change (∏ i, Polynomial.coeToPowerSeries.ringHom
        (linearPolynomial R n (x R n i))) =
      Polynomial.coeToPowerSeries.ringHom
        (∏ i, linearPolynomial R n (x R n i))
    rw [map_prod]
  rw [hmap, Polynomial.coeff_coe]
  simpa [fullLinearSeries, linearSeries, linearPolynomial,
    Finset.prod_eq_multiset_prod, Multiset.map_map,
    Function.comp_def, x] using h

/-- The suffix product has degree at most `k`, so its coefficient of degree
`k+1` vanishes. -/
theorem suffixLinearSeries_coeff_succ_eq_zero (k : Fin n) :
    PowerSeries.coeff (k.1 + 1) (suffixLinearSeries R n k) = 0 := by
  classical
  let p : Polynomial (Ambient R n) :=
    ∏ j : Fin k.1,
      linearPolynomial R n (x R n (suffixEmbedding n k j))
  have hpdeg : p.natDegree ≤ k.1 := by
    calc
      p.natDegree ≤
          ∑ j : Fin k.1,
            (linearPolynomial R n
              (x R n (suffixEmbedding n k j))).natDegree := by
          simpa using Polynomial.natDegree_prod_le
            (Finset.univ : Finset (Fin k.1))
            (fun j => linearPolynomial R n
              (x R n (suffixEmbedding n k j)))
      _ ≤ ∑ _j : Fin k.1, 1 := by
          apply Finset.sum_le_sum
          intro j _
          exact (Polynomial.natDegree_sub_le _ _).trans
            (max_le (by simp)
              ((Polynomial.natDegree_C_mul_le _ _).trans
                Polynomial.natDegree_X_le))
      _ = k.1 := by simp
  have hpcoeff : p.coeff (k.1 + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hpdeg (Nat.lt_succ_self k.1))
  have hsuffix : suffixLinearSeries R n k =
      (p : PowerSeries (Ambient R n)) := by
    rw [suffixLinearSeries]
    simp_rw [linearSeries]
    dsimp [p]
    change (∏ j : Fin k.1,
        (linearPolynomial R n (x R n (suffixEmbedding n k j)) :
          PowerSeries (Ambient R n))) =
      (((∏ j : Fin k.1,
        linearPolynomial R n (x R n (suffixEmbedding n k j))) :
          Polynomial (Ambient R n)) : PowerSeries (Ambient R n))
    change (∏ j, Polynomial.coeToPowerSeries.ringHom
        (linearPolynomial R n (x R n (suffixEmbedding n k j)))) =
      Polynomial.coeToPowerSeries.ringHom
        (∏ j, linearPolynomial R n (x R n (suffixEmbedding n k j)))
    rw [map_prod]
  rw [hsuffix, Polynomial.coeff_coe]
  exact hpcoeff

/-- The elementary/complete-homogeneous cancellation in exactly the degree
needed by the `k`th printed displayed relation. -/
theorem esymm_prefixHsymm_cancellation (k : Fin n) :
    ∑ j ∈ Finset.range (k.1 + 2),
        ((-1 : Ambient R n) ^ j *
          esymm (Fin n) (Coeff R n) j) *
            prefixHsymm R n k (k.1 + 1 - j) = 0 := by
  have hcoeff := congrArg (PowerSeries.coeff (k.1 + 1))
    (fullLinearSeries_mul_prefixCompleteSeries R n k)
  rw [PowerSeries.coeff_mul,
    suffixLinearSeries_coeff_succ_eq_zero] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simpa [fullLinearSeries_coeff, prefixHsymm, mul_assoc] using hcoeff

/-- The same cancellation indexed by `Fin`, for splitting off its zeroth
term together with the printed displayed relation. -/
theorem esymm_prefixHsymm_cancellation_fin (k : Fin n) :
    ∑ j : Fin (k.1 + 2),
      ((-1 : Ambient R n) ^ j.1 *
        esymm (Fin n) (Coeff R n) j.1) *
          prefixHsymm R n k (k.1 + 1 - j.1) = 0 := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ j ∈ Finset.range (k.1 + 2),
        ((-1 : Ambient R n) ^ j *
          esymm (Fin n) (Coeff R n) j) *
            prefixHsymm R n k (k.1 + 1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    _ = 0 := esymm_prefixHsymm_cancellation R n k

/-- Embed a triangular summation index `j <= k` as the Vieta-relation index
of degree `j+1`. -/
def degreeIndex (k : Fin n) (j : Fin (k.1 + 1)) : Fin n :=
  Fin.castLE (Nat.succ_le_iff.mpr k.2) j

@[simp]
theorem degreeIndex_val (k : Fin n) (j : Fin (k.1 + 1)) :
    (degreeIndex n k j).1 = j.1 :=
  rfl

@[simp]
theorem degreeIndex_last (k : Fin n) :
    degreeIndex n k (Fin.last k.1) = k := by
  apply Fin.ext
  rfl

@[simp]
theorem formalE_degreeIndex (k : Fin n) (j : Fin (k.1 + 1)) :
    formalE R n (j.1 + 1) = e R n (degreeIndex n k j) := by
  rw [formalE_succ R n j.1]
  rfl

/-- Lazard's displayed triangular family, written in its uniform
complete-homogeneous Vieta-combination form. -/
def displayedJ (k : Fin n) : Ambient R n :=
  ∑ j : Fin (k.1 + 1),
    ((-1 : Ambient R n) ^ j.1 * prefixHsymm R n k (k.1 - j.1)) *
      vietaRelation R n (degreeIndex n k j)

/-- Lazard's displayed triangular polynomial in the literal printed form

`sum_(r=0)^(k+1) (-1)^r e_r h_(k+1-r)(x₀,...,x_(n-k-1))`,

where `e_0 = 1`.  The upper bound `k+1 ≤ n` means that the zero extension
in `formalE` is not used here. -/
def printedDisplayedJ (k : Fin n) : Ambient R n :=
  ∑ r : Fin (k.1 + 2),
    ((-1 : Ambient R n) ^ r.1 * formalE R n r.1) *
      prefixHsymm R n k (k.1 + 1 - r.1)

/-- The literal printed alternating-`e` polynomial is exactly the uniform
Vieta-combination polynomial. -/
theorem printedDisplayedJ_eq_displayedJ (k : Fin n) :
    printedDisplayedJ R n k = displayedJ R n k := by
  classical
  let sigmaTail : Fin (k.1 + 1) → Ambient R n := fun j =>
    ((-1 : Ambient R n) ^ (j.1 + 1) *
      esymm (Fin n) (Coeff R n) (j.1 + 1)) *
        prefixHsymm R n k (k.1 - j.1)
  let eTail : Fin (k.1 + 1) → Ambient R n := fun j =>
    ((-1 : Ambient R n) ^ (j.1 + 1) *
      e R n (degreeIndex n k j)) *
        prefixHsymm R n k (k.1 - j.1)
  let relationTerm : Fin (k.1 + 1) → Ambient R n := fun j =>
    ((-1 : Ambient R n) ^ j.1 *
      prefixHsymm R n k (k.1 - j.1)) *
        vietaRelation R n (degreeIndex n k j)
  have hcancel :
      prefixHsymm R n k (k.1 + 1) + ∑ j, sigmaTail j = 0 := by
    simpa [Fin.sum_univ_succ, sigmaTail, MvPolynomial.esymm_zero] using
      esymm_prefixHsymm_cancellation_fin R n k
  have hprinted :
      printedDisplayedJ R n k =
        prefixHsymm R n k (k.1 + 1) + ∑ j, eTail j := by
    simp [printedDisplayedJ, Fin.sum_univ_succ, eTail,
      formalE_degreeIndex]
  have hterm (j : Fin (k.1 + 1)) :
      sigmaTail j + relationTerm j = eTail j := by
    dsimp [sigmaTail, relationTerm, eTail, vietaRelation]
    rw [pow_succ]
    ring
  have hsum :
      (∑ j, sigmaTail j) + ∑ j, relationTerm j = ∑ j, eTail j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hterm j
  calc
    printedDisplayedJ R n k =
        prefixHsymm R n k (k.1 + 1) + ∑ j, eTail j := hprinted
    _ = prefixHsymm R n k (k.1 + 1) +
          ((∑ j, sigmaTail j) + ∑ j, relationTerm j) := by
        rw [hsum]
    _ = (prefixHsymm R n k (k.1 + 1) + ∑ j, sigmaTail j) +
          ∑ j, relationTerm j := by
        rw [add_assoc]
    _ = ∑ j, relationTerm j := by
        rw [hcancel, zero_add]
    _ = displayedJ R n k := by
        rfl

/-- Lazard's formal Vieta ideal. -/
def vietaIdeal : Ideal (Ambient R n) :=
  Ideal.span (Set.range (vietaRelation R n))

/-- The ideal generated by the general displayed family. -/
def displayedIdeal : Ideal (Ambient R n) :=
  Ideal.span (Set.range (displayedJ R n))

/-- The ideal generated by the literal printed alternating-`e` family. -/
def printedDisplayedIdeal : Ideal (Ambient R n) :=
  Ideal.span (Set.range (printedDisplayedJ R n))

theorem printedDisplayedIdeal_eq_displayedIdeal :
    printedDisplayedIdeal R n = displayedIdeal R n := by
  rw [printedDisplayedIdeal, displayedIdeal]
  apply congrArg Ideal.span
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (printedDisplayedJ_eq_displayedJ R n k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, printedDisplayedJ_eq_displayedJ R n k⟩

theorem vietaRelation_mem_vietaIdeal (i : Fin n) :
    vietaRelation R n i ∈ vietaIdeal R n :=
  Ideal.subset_span (Set.mem_range_self i)

theorem displayedJ_mem_displayedIdeal (i : Fin n) :
    displayedJ R n i ∈ displayedIdeal R n :=
  Ideal.subset_span (Set.mem_range_self i)

/-- Every displayed relation is, definitionally, a
complete-homogeneous linear combination of the Vieta relations. -/
theorem displayedJ_mem_vietaIdeal (k : Fin n) :
    displayedJ R n k ∈ vietaIdeal R n := by
  classical
  rw [displayedJ]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _
    (vietaRelation_mem_vietaIdeal R n (degreeIndex n k j))

theorem displayedIdeal_le_vietaIdeal :
    displayedIdeal R n ≤ vietaIdeal R n := by
  apply Ideal.span_le.2
  rintro _ ⟨k, rfl⟩
  exact displayedJ_mem_vietaIdeal R n k

/-- Triangular inversion: the Vieta relation of degree `k+1` belongs to the
ideal generated by the first `k+1` displayed relations.  The proof uses only
that `h_0=1`; no coefficient expansion or monomial order occurs. -/
theorem vietaRelation_mem_displayedIdeal (i : Fin n) :
    vietaRelation R n i ∈ displayedIdeal R n := by
  classical
  have hmem : ∀ k : ℕ, ∀ hk : k < n,
      vietaRelation R n ⟨k, hk⟩ ∈ displayedIdeal R n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let ki : Fin n := ⟨k, hk⟩
        let term : Fin (k + 1) → Ambient R n := fun j =>
          ((-1 : Ambient R n) ^ j.1 *
              prefixHsymm R n ki (k - j.1)) *
            vietaRelation R n (degreeIndex n ki j)
        have hJ : (∑ j : Fin (k + 1), term j) ∈ displayedIdeal R n := by
          simpa [term, ki, displayedJ] using
            displayedJ_mem_displayedIdeal R n ki
        rw [Fin.sum_univ_castSucc] at hJ
        have hrest : (∑ j : Fin k, term j.castSucc) ∈
            displayedIdeal R n := by
          apply Ideal.sum_mem
          intro j _
          apply Ideal.mul_mem_left
          have hjk : (degreeIndex n ki j.castSucc).1 < k := by
            simpa [degreeIndex, ki] using j.2
          exact ih (degreeIndex n ki j.castSucc).1 hjk
            (degreeIndex n ki j.castSucc).2
        have hlast : term (Fin.last k) ∈ displayedIdeal R n := by
          have := Ideal.sub_mem (displayedIdeal R n) hJ hrest
          simpa using this
        have hsigned :
            ((-1 : Ambient R n) ^ k) * vietaRelation R n ki ∈
              displayedIdeal R n := by
          have hdi : degreeIndex n ki (Fin.last k) = ki := by
            simpa [ki] using degreeIndex_last n ki
          simpa [term, prefixHsymm_zero, hdi] using hlast
        have hunsigned := Ideal.mul_mem_left (displayedIdeal R n)
          ((-1 : Ambient R n) ^ k) hsigned
        have hsign :
            ((-1 : Ambient R n) ^ k) * ((-1 : Ambient R n) ^ k) = 1 := by
          have hbase : (-1 : Ambient R n) * (-1 : Ambient R n) = 1 := by
            ring
          rw [← mul_pow, hbase, one_pow]
        rw [← mul_assoc, hsign, one_mul] at hunsigned
        simpa [ki] using hunsigned
  exact hmem i.1 i.2

theorem vietaIdeal_le_displayedIdeal :
    vietaIdeal R n ≤ displayedIdeal R n := by
  apply Ideal.span_le.2
  rintro _ ⟨i, rfl⟩
  exact vietaRelation_mem_displayedIdeal R n i

/-- Order-free, arbitrary-degree ideal equality underlying Lazard's
Lemma 1. -/
theorem displayedIdeal_eq_vietaIdeal :
    displayedIdeal R n = vietaIdeal R n := by
  apply le_antisymm
  · exact displayedIdeal_le_vietaIdeal R n
  · exact vietaIdeal_le_displayedIdeal R n

/-- Order-free, arbitrary-degree ideal equality for the literal printed
family underlying Lazard's Lemma 1. -/
theorem printedDisplayedIdeal_eq_vietaIdeal :
    printedDisplayedIdeal R n = vietaIdeal R n := by
  rw [printedDisplayedIdeal_eq_displayedIdeal,
    displayedIdeal_eq_vietaIdeal]

end

end LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerGeneralIdeal
