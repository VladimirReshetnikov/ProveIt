import GowersSzemeredi.Sections17_18
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Polynomial phase decomposition in Section 17

This module proves Lemma 17.1.  The algebraic core is the polarization
identity expressing a square-free monomial as a mixed finite difference of
a one-variable power.  We prove that identity over an arbitrary commutative
ring by tracking the top coefficient of a polynomial under successive
backward differences.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset Polynomial

namespace LeanProofs.GowersSzemeredi

section PolynomialDifferences

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- Backward finite difference of a polynomial with increment `h`. -/
private def backwardDiffPoly (h : R) (P : R[X]) : R[X] :=
  P - P.comp (X - C h)

private lemma hasseDeriv_eq_C_of_natDegree_le (P : R[X]) (n : Nat)
    (hP : P.natDegree ≤ n) :
    P.hasseDeriv n = C (P.coeff n) := by
  ext j
  cases j with
  | zero => simp [Polynomial.hasseDeriv_coeff]
  | succ j =>
      rw [Polynomial.hasseDeriv_coeff, coeff_C]
      have hlt : n < (j + 1) + n := by omega
      have hz : P.coeff ((j + 1) + n) = 0 :=
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP) _ hlt
      simp [hz]

private lemma hasseDeriv_pred_eq (P : R[X]) (n : Nat)
    (hP : P.natDegree ≤ n + 1) :
    P.hasseDeriv n =
      C (P.coeff n) + C (((n + 1 : Nat) : R) * P.coeff (n + 1)) * X := by
  ext j
  rcases j with _ | j
  · simp [Polynomial.hasseDeriv_coeff]
  rcases j with _ | j
  · rw [Polynomial.hasseDeriv_coeff]
    norm_num [Nat.choose_succ_self_right, add_comm]
  · rw [Polynomial.hasseDeriv_coeff]
    have hlt : n + 1 < (j + 2) + n := by omega
    have hz : P.coeff ((j + 2) + n) = 0 :=
      (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP) _ hlt
    rw [hz, mul_zero, coeff_add, coeff_C]
    simp [Polynomial.coeff_one]

private lemma backwardDiffPoly_degree_coeff (P : R[X]) (n : Nat)
    (hP : P.natDegree ≤ n + 1) (h : R) :
    (backwardDiffPoly h P).natDegree ≤ n ∧
      (backwardDiffPoly h P).coeff n =
        ((n + 1 : Nat) : R) * h * P.coeff (n + 1) := by
  have hshift : (P.comp (X - C h)).natDegree ≤ n + 1 := by
    rw [show X - C h = X + C (-h) by simp [sub_eq_add_neg]]
    rw [← Polynomial.taylor_apply, Polynomial.natDegree_taylor]
    exact hP
  have hrough : (backwardDiffPoly h P).natDegree ≤ n + 1 := by
    exact (P.natDegree_sub_le_of_le hP hshift).trans (by simp)
  have htop : (backwardDiffPoly h P).coeff (n + 1) = 0 := by
    rw [backwardDiffPoly, coeff_sub]
    have htaylor : (P.comp (X - C h)).coeff (n + 1) = P.coeff (n + 1) := by
      rw [show X - C h = X + C (-h) by simp [sub_eq_add_neg], ← Polynomial.taylor_apply,
        Polynomial.taylor_coeff, hasseDeriv_eq_C_of_natDegree_le P (n + 1) hP,
        eval_C]
    rw [htaylor, sub_self]
  refine ⟨Polynomial.natDegree_le_pred hrough htop, ?_⟩
  rw [backwardDiffPoly, coeff_sub]
  have htaylor : (P.comp (X - C h)).coeff n =
      P.coeff n - ((n + 1 : Nat) : R) * h * P.coeff (n + 1) := by
    rw [show X - C h = X + C (-h) by simp [sub_eq_add_neg], ← Polynomial.taylor_apply,
      Polynomial.taylor_coeff, hasseDeriv_pred_eq P n hP]
    simp [eval_add, eval_mul, eval_C, eval_X]
    ring
  rw [htaylor]
  ring

/-- Alternating polynomial sum over all subsets of `S`. -/
private def powersetDifferencePoly (S : Finset ι) (x : ι → R)
    (P : R[X]) : R[X] :=
  ∑ E ∈ S.powerset,
    C ((-1 : R) ^ E.card) *
      P.comp (X - C (∑ i ∈ E, x i))

private lemma powersetDifferencePoly_insert (a : ι) (S : Finset ι)
    (ha : a ∉ S) (x : ι → R) (P : R[X]) :
    powersetDifferencePoly (insert a S) x P =
      powersetDifferencePoly S x (backwardDiffPoly (x a) P) := by
  classical
  rw [powersetDifferencePoly, Finset.sum_powerset_insert ha,
    powersetDifferencePoly, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have haE : a ∉ E := notMem_mono (mem_powerset.mp hE) ha
  rw [card_insert_of_notMem haE, sum_insert haE]
  simp only [pow_succ, mul_neg, mul_one, C_neg]
  rw [backwardDiffPoly, Polynomial.sub_comp]
  have hcomp :
      (P.comp (X - C (x a))).comp (X - C (∑ i ∈ E, x i)) =
        P.comp (X - C (x a + ∑ i ∈ E, x i)) := by
    rw [Polynomial.comp_assoc]
    congr 1
    simp only [Polynomial.sub_comp, X_comp, C_comp]
    rw [map_add]
    ring
  rw [hcomp]
  ring

private lemma powersetDifferencePoly_eq_C (S : Finset ι) (x : ι → R)
    (P : R[X]) (hP : P.natDegree ≤ S.card) :
    powersetDifferencePoly S x P =
      C (((S.card.factorial : Nat) : R) * (∏ i ∈ S, x i) * P.coeff S.card) := by
  classical
  induction S using Finset.induction_on generalizing P with
  | empty =>
      simpa [powersetDifferencePoly] using
        (Polynomial.eq_C_of_natDegree_le_zero hP)
  | @insert a S ha ih =>
      rw [powersetDifferencePoly_insert a S ha x P]
      have hdiff := backwardDiffPoly_degree_coeff P S.card (by simpa [ha] using hP) (x a)
      rw [ih _ hdiff.1, hdiff.2]
      simp only [card_insert_of_notMem ha, prod_insert ha, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      congr 1
      ring

private lemma powersetDifference_pow (S : Finset ι) (x : ι → R) (s : R) :
    ∑ E ∈ S.powerset,
        (-1 : R) ^ E.card * (s - ∑ i ∈ E, x i) ^ S.card =
      ((S.card.factorial : Nat) : R) * ∏ i ∈ S, x i := by
  have h := congrArg (fun P : R[X] => P.eval s)
    (powersetDifferencePoly_eq_C S x (X ^ S.card)
      (Polynomial.natDegree_X_pow_le S.card))
  simpa only [powersetDifferencePoly, eval_finsetSum, eval_mul, eval_C, eval_comp,
    eval_sub, eval_X, eval_pow, coeff_X_pow_self, mul_one] using h

end PolynomialDifferences

/-! ### Boolean supports and the phase construction -/

/-- Support of a Boolean cube vertex. -/
private def boolSupport {k : Nat} (e : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => e i = true

/-- Boolean cube vertices are the same finite objects as subsets of the
coordinate set. -/
private def boolFinsetEquiv (k : Nat) : (Fin k → Bool) ≃ Finset (Fin k) where
  toFun := boolSupport
  invFun := fun S i => decide (i ∈ S)
  left_inv e := by
    funext i
    simp only [boolSupport, mem_filter, mem_univ, true_and]
    cases e i <;> simp
  right_inv S := by
    ext i
    simp [boolSupport]

@[simp] private lemma boolSupport_equiv_apply {k : Nat} (e : Fin k → Bool) :
    boolFinsetEquiv k e = boolSupport e := rfl

@[simp] private lemma boolSupport_equiv_symm_apply {k : Nat} (S : Finset (Fin k)) :
    boolSupport ((boolFinsetEquiv k).symm S) = S :=
  (boolFinsetEquiv k).apply_symm_apply S

@[simp] private lemma boolFinsetEquiv_symm_support {k : Nat} (e : Fin k → Bool) :
    (boolFinsetEquiv k).symm (boolSupport e) = e :=
  (boolFinsetEquiv k).symm_apply_apply e

private lemma boolSupport_card {k : Nat} (e : Fin k → Bool) :
    (boolSupport e).card = boolWeight e := by
  classical
  unfold boolSupport boolWeight countWhere
  congr 1
  ext i
  simp

private lemma boolSupport_sum {N k : Nat} (e : Fin k → Bool)
    (x : Point N k) :
    (∑ i ∈ boolSupport e, x i) = ∑ i, if e i then x i else 0 := by
  classical
  rw [boolSupport, sum_filter]

private lemma boolSupport_prod {N k : Nat} (e : Fin k → Bool)
    (x : Point N k) :
    (∏ i ∈ boolSupport e, x i) = ∏ i, if e i then x i else 1 := by
  classical
  rw [boolSupport, prod_filter]

private lemma parityTerm_eq_negOnePow {N n : Nat} (z : ZMod N) :
    (if Even n then z else -z) = (-1 : ZMod N) ^ n * z := by
  rw [neg_one_pow_eq_ite]
  split <;> simp_all

/-- Coefficient contributed by the square-free monomial indexed by `U`. -/
private def polarizationCoefficient {N k : Nat}
    (c : (Fin k → Bool) → ZMod N) (U : Finset (Fin k)) : ZMod N :=
  c ((boolFinsetEquiv k).symm U) *
    (((U.card.factorial : Nat) : ZMod N))⁻¹

/-- The one-variable polynomial phase assigned to the cube vertex with
support `E`. -/
private def polarizationPhase {N k : Nat}
    (c : (Fin k → Bool) → ZMod N) (E : Finset (Fin k))
    (t : ZMod N) : ZMod N :=
  ∑ U ∈ (Finset.univ : Finset (Fin k)).powerset,
    if E ⊆ U then polarizationCoefficient c U * t ^ U.card else 0

private lemma polarizationPhase_polynomialOn {N k : Nat} [NeZero N]
    (c : (Fin k → Bool) → ZMod N) (E : Finset (Fin k)) :
    PolynomialOn k Finset.univ (polarizationPhase c E) := by
  classical
  let q : Fin (k + 1) → ZMod N := fun j =>
    ∑ U ∈ (Finset.univ : Finset (Fin k)).powersetCard (j : Nat),
      if E ⊆ U then polarizationCoefficient c U else 0
  refine ⟨q, ?_⟩
  intro t _
  rw [polarizationPhase, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < k + 1 := mem_range.mp hj
  simp only [q, dif_pos hjlt]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro U hU
  have hcard : U.card = j := (mem_powersetCard.mp hU).2
  split_ifs with hEU
  · rw [hcard]
  · simp

private lemma sum_if_subset_powerset {R ι : Type*} [AddCommMonoid R]
    [DecidableEq ι] (F U : Finset ι) (hUF : U ⊆ F) (g : Finset ι → R) :
    (∑ E ∈ F.powerset, if E ⊆ U then g E else 0) =
      ∑ E ∈ U.powerset, g E := by
  classical
  have hfilter : F.powerset.filter (fun E => E ⊆ U) = U.powerset := by
    ext E
    simp only [mem_filter, mem_powerset]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans hUF, h⟩
  rw [← hfilter, Finset.sum_filter]

private lemma polarizationCoefficient_mul_factorial {N k : Nat} [NeZero N]
    [Fact N.Prime]
    (c : (Fin k → Bool) → ZMod N)
    (hkfac : IsUnit ((Nat.factorial k : Nat) : ZMod N))
    (U : Finset (Fin k)) :
    polarizationCoefficient c U *
        ((U.card.factorial : Nat) : ZMod N) =
      c ((boolFinsetEquiv k).symm U) := by
  have hcard : U.card ≤ k := by
    simpa using Finset.card_le_card (Finset.subset_univ U)
  have hunit : IsUnit ((U.card.factorial : Nat) : ZMod N) :=
    hkfac.natCast_factorial_of_le hcard
  rw [polarizationCoefficient, mul_assoc, inv_mul_cancel₀ hunit.ne_zero, mul_one]

private lemma polarization_inner_sum {N k : Nat} [NeZero N] [Fact N.Prime]
    (c : (Fin k → Bool) → ZMod N)
    (hkfac : IsUnit ((Nat.factorial k : Nat) : ZMod N))
    (U : Finset (Fin k)) (s : ZMod N) (x : Point N k) :
    (∑ E ∈ U.powerset,
        (-1 : ZMod N) ^ E.card * polarizationCoefficient c U *
          (s - ∑ i ∈ E, x i) ^ U.card) =
      c ((boolFinsetEquiv k).symm U) * ∏ i ∈ U, x i := by
  calc
    (∑ E ∈ U.powerset,
        (-1 : ZMod N) ^ E.card * polarizationCoefficient c U *
          (s - ∑ i ∈ E, x i) ^ U.card) =
        polarizationCoefficient c U *
          (∑ E ∈ U.powerset,
            (-1 : ZMod N) ^ E.card *
              (s - ∑ i ∈ E, x i) ^ U.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = polarizationCoefficient c U *
        (((U.card.factorial : Nat) : ZMod N) * ∏ i ∈ U, x i) := by
      rw [powersetDifference_pow]
    _ = c ((boolFinsetEquiv k).symm U) * ∏ i ∈ U, x i := by
      rw [← mul_assoc, polarizationCoefficient_mul_factorial c hkfac U]

private lemma signedCubeSum_polarization {N k : Nat} [NeZero N] [Fact N.Prime]
    (c : (Fin k → Bool) → ZMod N)
    (hkfac : IsUnit ((Nat.factorial k : Nat) : ZMod N))
    (s : ZMod N) (x : Point N k) :
    signedCubeSum
        (fun e => polarizationPhase c (boolSupport e)) s x =
      ∑ e : Fin k → Bool, c e * ∏ i, if e i then x i else 1 := by
  classical
  let F : Finset (Fin k) := Finset.univ
  calc
    signedCubeSum (fun e => polarizationPhase c (boolSupport e)) s x =
        ∑ e : Fin k → Bool,
          (-1 : ZMod N) ^ (boolSupport e).card *
            polarizationPhase c (boolSupport e)
              (s - ∑ i ∈ boolSupport e, x i) := by
      unfold signedCubeSum
      apply Finset.sum_congr rfl
      intro e _
      rw [parityTerm_eq_negOnePow, ← boolSupport_card, cubeArgument,
        ← boolSupport_sum]
    _ = ∑ E : Finset (Fin k),
          (-1 : ZMod N) ^ E.card *
            polarizationPhase c E (s - ∑ i ∈ E, x i) := by
      exact (boolFinsetEquiv k).sum_comp (fun E =>
        (-1 : ZMod N) ^ E.card *
          polarizationPhase c E (s - ∑ i ∈ E, x i))
    _ = ∑ E ∈ F.powerset,
          (-1 : ZMod N) ^ E.card *
            polarizationPhase c E (s - ∑ i ∈ E, x i) := by
      simp [F]
    _ = ∑ E ∈ F.powerset, ∑ U ∈ F.powerset,
          if E ⊆ U then
            (-1 : ZMod N) ^ E.card * polarizationCoefficient c U *
              (s - ∑ i ∈ E, x i) ^ U.card
          else 0 := by
      apply Finset.sum_congr rfl
      intro E _
      rw [polarizationPhase, mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      split_ifs <;> ring
    _ = ∑ U ∈ F.powerset, ∑ E ∈ F.powerset,
          if E ⊆ U then
            (-1 : ZMod N) ^ E.card * polarizationCoefficient c U *
              (s - ∑ i ∈ E, x i) ^ U.card
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ U ∈ F.powerset, ∑ E ∈ U.powerset,
          (-1 : ZMod N) ^ E.card * polarizationCoefficient c U *
            (s - ∑ i ∈ E, x i) ^ U.card := by
      apply Finset.sum_congr rfl
      intro U hU
      apply sum_if_subset_powerset F U (mem_powerset.mp hU)
    _ = ∑ U ∈ F.powerset,
          c ((boolFinsetEquiv k).symm U) * ∏ i ∈ U, x i := by
      apply Finset.sum_congr rfl
      intro U _
      exact polarization_inner_sum c hkfac U s x
    _ = ∑ e : Fin k → Bool, c e * ∏ i, if e i then x i else 1 := by
      rw [show F.powerset = Finset.univ by simp [F]]
      calc
        (∑ U : Finset (Fin k),
            c ((boolFinsetEquiv k).symm U) * ∏ i ∈ U, x i) =
            ∑ e : Fin k → Bool,
              c e * ∏ i ∈ boolSupport e, x i := by
          simpa using ((boolFinsetEquiv k).sum_comp (fun U =>
            c ((boolFinsetEquiv k).symm U) * ∏ i ∈ U, x i)).symm
        _ = ∑ e : Fin k → Bool, c e * ∏ i, if e i then x i else 1 := by
          apply Finset.sum_congr rfl
          intro e _
          rw [boolSupport_prod]

/-- **Gowers, Lemma 17.1.** Every multiaffine frequency is the alternating
cube sum of one-variable polynomial phases of degree at most `k`. -/
theorem lemma_17_1_holds : lemma_17_1 := by
  intro N k _ _ _hk hkfac sigma hsigma
  obtain ⟨c, hc⟩ := hsigma
  refine ⟨fun e => polarizationPhase c (boolSupport e), ?_, ?_⟩
  · intro e
    exact polarizationPhase_polynomialOn c (boolSupport e)
  · intro s x
    exact (hc x).trans (signedCubeSum_polarization c hkfac s x).symm

end LeanProofs.GowersSzemeredi
