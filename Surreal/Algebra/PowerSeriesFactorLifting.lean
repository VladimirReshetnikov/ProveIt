import Surreal.Algebra.PolynomialFactorLinearization
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Binary coprime factor lifting in a formal perturbation parameter

This is a formal power-series bridge toward `polynomial:thm:hensel` and
`polynomial:eq:henselrecursion` in
`docs/surcomplex/polynomial-algebra/article.tex`. The coefficients in the
perturbation parameter are polynomials in a separate variable. The bounded
Sylvester inverse recursively produces corrections without changing the
constant factors or their polynomial degree bounds.

The recursion is on natural-number formal coefficients. No convergence in
the fine topology, or cofinality of natural numbers in arbitrary Hahn
supports, is asserted. Arbitrary support-controlled Hahn lifting remains a
separate step.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

private def boundedCorrectionProduct (p q : R[X])
    (h : degreeLT R p.natDegree) (k : degreeLT R q.natDegree) :
    degreeLT R (p.natDegree + q.natDegree) :=
  ⟨(h : R[X]) * (k : R[X]), mem_degreeLT.mpr (by
    by_cases hh : (h : R[X]) = 0
    · rw [hh, zero_mul, degree_zero]
      exact WithBot.bot_lt_coe _
    by_cases hk : (k : R[X]) = 0
    · rw [hk, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hd := (natDegree_lt_iff_degree_lt hh).mpr (mem_degreeLT.mp h.property)
    have kd := (natDegree_lt_iff_degree_lt hk).mpr (mem_degreeLT.mp k.property)
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr
      (natDegree_mul_le.trans_lt (Nat.add_lt_add hd kd))))⟩

/-- The coefficient of the quadratic remainder at the preceding order.
Every index used in this finite sum is strictly smaller than `n`. -/
def factorLiftConvolution (p q : R[X])
    (c : ℕ → degreeLT R p.natDegree × degreeLT R q.natDegree) (n : ℕ) :
    degreeLT R (p.natDegree + q.natDegree) :=
  ∑ i : Fin n, boundedCorrectionProduct p q (c i).1 (c (n - 1 - i)).2

/-- The actual coefficient recursion using the proved inverse of the finite linearization. -/
def factorLiftCoeff (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    ℕ → degreeLT R p.natDegree × degreeLT R q.natDegree :=
  Nat.strongRec fun n prev => factorCorrection p q hp hpq
    (e n - ∑ i : Fin n, boundedCorrectionProduct p q
      (prev i i.isLt).1 (prev (n - 1 - i) (by have := i.isLt; omega)).2)

/-- The recursive equation is exactly the coefficient-level Hensel correction. -/
theorem factorLiftCoeff_eq (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) (n : ℕ) :
    factorLiftCoeff p q hp hpq e n = factorCorrection p q hp hpq
      (e n - factorLiftConvolution p q (factorLiftCoeff p q hp hpq e) n) := by
  unfold factorLiftCoeff
  rw [Nat.strongRec_eq]
  rfl

/-- The prescribed coefficientwise bounded formal error, before multiplying by the parameter. -/
def factorErrorSeries (p q : R[X]) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    PowerSeries R[X] := PowerSeries.mk fun n => (e n : R[X])

/-- The left correction after removing its initial perturbation parameter. -/
def factorLiftLeftSeries (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : PowerSeries R[X] :=
  PowerSeries.mk fun n => ((factorLiftCoeff p q hp hpq e n).1 : R[X])

/-- The right correction after removing its initial perturbation parameter. -/
def factorLiftRightSeries (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : PowerSeries R[X] :=
  PowerSeries.mk fun n => ((factorLiftCoeff p q hp hpq e n).2 : R[X])

private theorem factorLiftConvolution_zero (p q : R[X])
    (c : ℕ → degreeLT R p.natDegree × degreeLT R q.natDegree) :
    factorLiftConvolution p q c 0 = 0 := by simp [factorLiftConvolution]

private theorem factorLiftConvolution_succ (p q : R[X])
    (c : ℕ → degreeLT R p.natDegree × degreeLT R q.natDegree) (n : ℕ) :
    (factorLiftConvolution p q c (n + 1) : R[X]) =
      PowerSeries.coeff n
        (PowerSeries.mk (fun k => ((c k).1 : R[X])) *
          PowerSeries.mk (fun k => ((c k).2 : R[X]))) := by
  simp only [factorLiftConvolution, Submodule.coe_sum, boundedCorrectionProduct,
    PowerSeries.coeff_mul, PowerSeries.coeff_mk, Nat.add_sub_cancel]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact Fin.sum_univ_eq_sum_range
    (fun i => ((c i).1 : R[X]) * ((c (n - i)).2 : R[X])) (n + 1)

/-- The constructed series satisfy the exact linear-plus-quadratic correction equation. -/
theorem factorLift_linearization (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    factorLiftLeftSeries p q hp hpq e * PowerSeries.C q +
      PowerSeries.C p * factorLiftRightSeries p q hp hpq e +
      PowerSeries.X * (factorLiftLeftSeries p q hp hpq e * factorLiftRightSeries p q hp hpq e) =
        factorErrorSeries p q e := by
  apply PowerSeries.ext
  intro n
  have hc := factorCorrection_spec p q hp hpq
    (e n - factorLiftConvolution p q (factorLiftCoeff p q hp hpq e) n)
  rw [← factorLiftCoeff_eq] at hc
  simp only [Submodule.coe_sub] at hc
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
    factorLiftLeftSeries, factorLiftRightSeries, factorErrorSeries, PowerSeries.coeff_mk]
  cases n with
  | zero =>
    rw [factorLiftConvolution_zero, Submodule.coe_zero, sub_zero] at hc
    simpa only [PowerSeries.coeff_zero_X_mul, add_zero] using hc
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, ← factorLiftConvolution_succ]
    exact (eq_sub_iff_add_eq).mp hc

/-- The lifted left factor has exactly the original constant factor. -/
def liftedLeftFactor (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : PowerSeries R[X] :=
  PowerSeries.C p + PowerSeries.X * factorLiftLeftSeries p q hp hpq e

/-- The lifted right factor has exactly the original constant factor. -/
def liftedRightFactor (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : PowerSeries R[X] :=
  PowerSeries.C q + PowerSeries.X * factorLiftRightSeries p q hp hpq e

/-- Exact binary formal factorization of the prescribed perturbation. -/
theorem liftedFactors_mul (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    liftedLeftFactor p q hp hpq e * liftedRightFactor p q hp hpq e =
      PowerSeries.C (p * q) + PowerSeries.X * factorErrorSeries p q e := by
  rw [← factorLift_linearization p q hp hpq e, map_mul]
  unfold liftedLeftFactor liftedRightFactor
  ring

@[simp] theorem constantCoeff_liftedLeftFactor (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    PowerSeries.constantCoeff (liftedLeftFactor p q hp hpq e) = p := by
  simp [liftedLeftFactor]

@[simp] theorem constantCoeff_liftedRightFactor (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    PowerSeries.constantCoeff (liftedRightFactor p q hp hpq e) = q := by
  simp [liftedRightFactor]

theorem degree_coeff_liftedLeftFactor_succ_lt (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) (n : ℕ) :
    (PowerSeries.coeff (n + 1) (liftedLeftFactor p q hp hpq e)).degree < p.natDegree := by
  simpa [liftedLeftFactor, factorLiftLeftSeries] using
    mem_degreeLT.mp (factorLiftCoeff p q hp hpq e n).1.property

theorem degree_coeff_liftedRightFactor_succ_lt (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) (n : ℕ) :
    (PowerSeries.coeff (n + 1) (liftedRightFactor p q hp hpq e)).degree < q.natDegree := by
  simpa [liftedRightFactor, factorLiftRightSeries] using
    mem_degreeLT.mp (factorLiftCoeff p q hp hpq e n).2.property

/-- The coefficient recurrence has only one solution, among all bounded coefficient sequences. -/
theorem factorLiftCoeff_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree))
    (c : ℕ → degreeLT R p.natDegree × degreeLT R q.natDegree)
    (hc : ∀ n, (c n).1 * q + p * (c n).2 +
      (factorLiftConvolution p q c n : R[X]) = e n) (n : ℕ) :
    c n = factorLiftCoeff p q hp hpq e n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hconv : factorLiftConvolution p q c n =
        factorLiftConvolution p q (factorLiftCoeff p q hp hpq e) n := by
      unfold factorLiftConvolution
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i i.isLt, ih (n - 1 - i) (by have := i.isLt; omega)]
    rw [factorLiftCoeff_eq]
    apply factorCorrection_unique
    change (c n).1 * q + p * (c n).2 =
      (e n : R[X]) - (factorLiftConvolution p q (factorLiftCoeff p q hp hpq e) n : R[X])
    rw [← hconv]
    exact (eq_sub_iff_add_eq).mpr (hc n)

/-- Uniqueness of the formal correction series follows coefficientwise from the same inverse. -/
theorem factorLiftSeries_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) (A B : PowerSeries R[X])
    (hA : ∀ n, (PowerSeries.coeff n A).degree < p.natDegree)
    (hB : ∀ n, (PowerSeries.coeff n B).degree < q.natDegree)
    (heq : A * PowerSeries.C q + PowerSeries.C p * B + PowerSeries.X * (A * B) =
      factorErrorSeries p q e) :
    A = factorLiftLeftSeries p q hp hpq e ∧ B = factorLiftRightSeries p q hp hpq e := by
  let c : ℕ → degreeLT R p.natDegree × degreeLT R q.natDegree :=
    fun n => (⟨PowerSeries.coeff n A, mem_degreeLT.mpr (hA n)⟩,
      ⟨PowerSeries.coeff n B, mem_degreeLT.mpr (hB n)⟩)
  have hcA : PowerSeries.mk (fun n => ((c n).1 : R[X])) = A :=
    PowerSeries.ext fun n => by simp [c]
  have hcB : PowerSeries.mk (fun n => ((c n).2 : R[X])) = B :=
    PowerSeries.ext fun n => by simp [c]
  have hc (n : ℕ) : (c n).1 * q + p * (c n).2 +
      (factorLiftConvolution p q c n : R[X]) = e n := by
    have he := congrArg (PowerSeries.coeff n) heq
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
      factorErrorSeries, PowerSeries.coeff_mk] at he
    cases n with
    | zero =>
      simpa only [c, factorLiftConvolution_zero, Submodule.coe_zero,
        PowerSeries.coeff_zero_X_mul] using he
    | succ n =>
      rw [factorLiftConvolution_succ, hcA, hcB]
      simpa only [c, PowerSeries.coeff_succ_X_mul] using he
  have hcoeff := factorLiftCoeff_unique p q hp hpq e c hc
  constructor
  · apply PowerSeries.ext
    intro n
    simpa only [c, factorLiftLeftSeries, PowerSeries.coeff_mk] using
      congrArg (fun hk : degreeLT R p.natDegree × degreeLT R q.natDegree =>
        (hk.1 : R[X])) (hcoeff n)
  · apply PowerSeries.ext
    intro n
    simpa only [c, factorLiftRightSeries, PowerSeries.coeff_mk] using
      congrArg (fun hk : degreeLT R p.natDegree × degreeLT R q.natDegree =>
        (hk.2 : R[X])) (hcoeff n)

/-- Uniqueness among all formal factors with the prescribed constant factors and bounds.
No prior assumption that the candidates arose from the recursion is made. -/
theorem liftedFactors_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) (F G : PowerSeries R[X])
    (hF₀ : PowerSeries.constantCoeff F = p) (hG₀ : PowerSeries.constantCoeff G = q)
    (hF : ∀ n, (PowerSeries.coeff (n + 1) F).degree < p.natDegree)
    (hG : ∀ n, (PowerSeries.coeff (n + 1) G).degree < q.natDegree)
    (hmul : F * G = PowerSeries.C (p * q) + PowerSeries.X * factorErrorSeries p q e) :
    F = liftedLeftFactor p q hp hpq e ∧ G = liftedRightFactor p q hp hpq e := by
  let A := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) F
  let B := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) G
  have hFA : F = PowerSeries.C p + PowerSeries.X * A := by
    simpa only [A, hF₀, add_comm] using PowerSeries.eq_X_mul_shift_add_const F
  have hGB : G = PowerSeries.C q + PowerSeries.X * B := by
    simpa only [B, hG₀, add_comm] using PowerSeries.eq_X_mul_shift_add_const G
  have heq : A * PowerSeries.C q + PowerSeries.C p * B + PowerSeries.X * (A * B) =
      factorErrorSeries p q e := by
    apply PowerSeries.X_mul_cancel
    apply add_left_cancel (a := PowerSeries.C (p * q))
    calc
      PowerSeries.C (p * q) + PowerSeries.X *
          (A * PowerSeries.C q + PowerSeries.C p * B + PowerSeries.X * (A * B)) = F * G := by
            rw [hFA, hGB, map_mul]
            ring
      _ = _ := hmul
  obtain ⟨hA, hB⟩ := factorLiftSeries_unique p q hp hpq e A B
    (fun n => by simpa [A] using hF n) (fun n => by simpa [B] using hG n) heq
  exact ⟨by simpa only [liftedLeftFactor, hA] using hFA,
    by simpa only [liftedRightFactor, hB] using hGB⟩

/-- Existence and uniqueness of bounded binary formal factor lifts, including
degree-zero factors and zero coefficient rings. -/
theorem existsUnique_formal_factor_lift (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    ∃! FG : PowerSeries R[X] × PowerSeries R[X],
      PowerSeries.constantCoeff FG.1 = p ∧ PowerSeries.constantCoeff FG.2 = q ∧
      (∀ n, (PowerSeries.coeff (n + 1) FG.1).degree < p.natDegree) ∧
      (∀ n, (PowerSeries.coeff (n + 1) FG.2).degree < q.natDegree) ∧
      FG.1 * FG.2 = PowerSeries.C (p * q) + PowerSeries.X * factorErrorSeries p q e := by
  refine ⟨⟨liftedLeftFactor p q hp hpq e, liftedRightFactor p q hp hpq e⟩,
    ⟨constantCoeff_liftedLeftFactor p q hp hpq e,
      constantCoeff_liftedRightFactor p q hp hpq e,
      degree_coeff_liftedLeftFactor_succ_lt p q hp hpq e,
      degree_coeff_liftedRightFactor_succ_lt p q hp hpq e,
      liftedFactors_mul p q hp hpq e⟩, ?_⟩
  rintro ⟨F, G⟩ ⟨hF₀, hG₀, hF, hG, hmul⟩
  exact Prod.ext (liftedFactors_unique p q hp hpq e F G hF₀ hG₀ hF hG hmul).1
    (liftedFactors_unique p q hp hpq e F G hF₀ hG₀ hF hG hmul).2

/-- Coprimeness of constant coefficients lifts to coprimeness of the whole formal series.
The lifted Bézout combination has constant coefficient one and is therefore a unit. -/
theorem powerSeries_isCoprime_of_constantCoeff (F G : PowerSeries R[X])
    (h : IsCoprime (PowerSeries.constantCoeff F) (PowerSeries.constantCoeff G)) :
    IsCoprime F G := by
  obtain ⟨a, b, hab⟩ := h
  let S := PowerSeries.C a * F + PowerSeries.C b * G
  have hs : PowerSeries.constantCoeff S = 1 := by simpa [S] using hab
  have hu : IsUnit S := PowerSeries.isUnit_iff_constantCoeff.mpr (hs ▸ isUnit_one)
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv'.mp hu
  refine ⟨u * PowerSeries.C a, u * PowerSeries.C b, ?_⟩
  calc
    u * PowerSeries.C a * F + u * PowerSeries.C b * G = u * S := by dsimp [S]; ring
    _ = 1 := hu

/-- The constructed formal factors remain coprime. -/
theorem liftedFactors_isCoprime (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    IsCoprime (liftedLeftFactor p q hp hpq e) (liftedRightFactor p q hp hpq e) := by
  apply powerSeries_isCoprime_of_constantCoeff
  simpa only [constantCoeff_liftedLeftFactor, constantCoeff_liftedRightFactor] using hpq

/-- An input-facing version: every formally bounded perturbation of the coprime product
has unique formally bounded factors with the prescribed constant terms. -/
theorem existsUnique_formal_factorization (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (H : PowerSeries R[X]) (hH₀ : PowerSeries.constantCoeff H = p * q)
    (hH : ∀ n, (PowerSeries.coeff (n + 1) H).degree < (p.natDegree + q.natDegree : ℕ)) :
    ∃! FG : PowerSeries R[X] × PowerSeries R[X],
      PowerSeries.constantCoeff FG.1 = p ∧ PowerSeries.constantCoeff FG.2 = q ∧
      (∀ n, (PowerSeries.coeff (n + 1) FG.1).degree < p.natDegree) ∧
      (∀ n, (PowerSeries.coeff (n + 1) FG.2).degree < q.natDegree) ∧ FG.1 * FG.2 = H := by
  let e : ℕ → degreeLT R (p.natDegree + q.natDegree) :=
    fun n => ⟨PowerSeries.coeff (n + 1) H, mem_degreeLT.mpr (hH n)⟩
  have hshape : PowerSeries.C (p * q) + PowerSeries.X * factorErrorSeries p q e = H := by
    simpa only [factorErrorSeries, e, hH₀, add_comm] using
      (PowerSeries.eq_X_mul_shift_add_const H).symm
  simpa only [hshape] using existsUnique_formal_factor_lift p q hp hpq e

end

end Surreal.FinitePolynomial
