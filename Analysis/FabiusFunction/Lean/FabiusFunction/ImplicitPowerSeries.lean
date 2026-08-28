import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal implicit roots over complete adic rings

Mathlib proves that a complete adic ring is Henselian by Newton iteration, but
the public `HenselianRing` interface asks the polynomial to be monic.  The
Newton proof never uses monicity.  This module extracts the stronger theorem:
over an arbitrary complete adic commutative ring, every simple approximate
root lifts uniquely inside its adic residue class.

The specialization to `R⟦X⟧` takes the ideal `(X)`.  It gives a formal
implicit-function theorem for a polynomial in an unknown `Z` whose
coefficients are power series in `X`: if the parameter-constant part of the
constant coefficient vanishes and the parameter-constant part of the linear
coefficient is a unit, there is a unique zero-constant series `S(X)` satisfying
`P(S)=0`.

The result assumes no field, domain, characteristic-zero structure,
Noetherianity, finite generation, monicity, degree bound, or analytic
convergence.  It is the reusable formal-series core of the algebraic inverse
germs appearing in the inverse-Fabius frontier.

## Main declarations

* `FormalImplicitRoot.exists_isRoot_sub_mem` is nonmonic Hensel lifting over a
  complete adic ring.
* `FormalImplicitRoot.eq_of_isRoot_of_sub_mem` is its residue-class uniqueness
  principle.
* `FormalImplicitRoot.existsUnique_isRoot_sub_mem` adds uniqueness in the
  prescribed residue class.
* `PowerSeries.Implicit.existsUnique_isRoot_constantCoeff` is the arbitrary
  base-series specialization.
* `PowerSeries.Implicit.existsUnique_zeroConstant_root` is the zero-constant formal
  implicit-function theorem.
* `PowerSeries.Implicit.root`, `constantCoeff_root`, `eval_root`, and `eq_root`
  expose the distinguished root and its elimination rules.
-/

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped Ring

namespace FormalImplicitRoot

/-- **Nonmonic Hensel lifting.** In an `I`-adically complete commutative ring,
an approximate root whose derivative is a unit modulo `I` lifts to an exact
root in the same residue class.  Unlike the public `HenselianRing` projection,
this theorem does not assume that the polynomial is monic. -/
theorem exists_isRoot_sub_mem {A : Type*} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] (P : Polynomial A) (a₀ : A)
    (hP : P.eval a₀ ∈ I)
    (hP' : IsUnit (Ideal.Quotient.mk I (P.derivative.eval a₀))) :
    ∃ a : A, P.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let P' := P.derivative
  let c : ℕ → A := fun n ↦
    Nat.recOn n a₀ fun _ b ↦ b - P.eval b * (P'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - P.eval (c n) * (P'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at hP ⊢
      exact (ih.eval P).trans hP
  have hP'c : ∀ n, IsUnit (P'.eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! hP' using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hPcI : ∀ n, P.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! hP
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
        ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one,
          Finset.sum_singleton, taylor_coeff_zero, taylor_coeff_one, pow_zero,
          pow_one, mul_one, mul_neg, mul_left_comm,
          Ring.mul_inverse_cancel _ (hP'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have hpow : n + 2 ≤ i * (n + 1) := by
          trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hpow ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow
          ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have hcauchy : ∀ m n, m ≤ n →
      c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal A)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right ?_ (hPcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (hcauchy _ _)
  refine ⟨a, ?_, ?_⟩
  · show P.IsRoot a
    suffices ∀ n, P.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal A)] by
      exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval P).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hPcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one,
      sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ hP

/-- Two exact roots in the same `I`-adic residue class agree when the
derivative at the first root is a unit modulo `I`. -/
theorem eq_of_isRoot_of_sub_mem {A : Type*} [CommRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson ⊥) {P : Polynomial A} {a b : A}
    (ha : P.IsRoot a) (hb : P.IsRoot b) (hab : b - a ∈ I)
    (hP' : IsUnit (Ideal.Quotient.mk I (P.derivative.eval a))) : a = b := by
  obtain ⟨d, hd⟩ :=
    Polynomial.exists_mul_sq_add_linear_part_eq_eval_add P a (b - a)
  have hzero : (d * (b - a) + P.derivative.eval a) * (b - a) = 0 := by
    calc
      _ = d * (b - a) ^ 2 + P.derivative.eval a * (b - a) + P.eval a := by
        rw [ha]
        ring
      _ = P.eval (a + (b - a)) := hd
      _ = P.eval b := by rw [show a + (b - a) = b by ring]
      _ = 0 := hb
  have hmapzero : Ideal.Quotient.mk I (b - a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hab
  haveI := isLocalHom_of_le_jacobson_bot I hI
  have hunit : IsUnit (d * (b - a) + P.derivative.eval a) := by
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    simpa only [map_add, map_mul, hmapzero, mul_zero, zero_add] using hP'
  have hba : b - a = 0 := hunit.mul_right_eq_zero.mp hzero
  exact (sub_eq_zero.mp hba).symm

/-- **Unique nonmonic Hensel lift.** A simple approximate root in a complete
adic ring has exactly one exact root in its residue class. -/
theorem existsUnique_isRoot_sub_mem {A : Type*} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] (P : Polynomial A) (a₀ : A)
    (hP : P.eval a₀ ∈ I)
    (hP' : IsUnit (Ideal.Quotient.mk I (P.derivative.eval a₀))) :
    ∃! a : A, P.IsRoot a ∧ a - a₀ ∈ I := by
  obtain ⟨a, ha, ha₀⟩ := exists_isRoot_sub_mem I P a₀ hP hP'
  refine ⟨a, ⟨ha, ha₀⟩, ?_⟩
  intro b hb
  have hba : b - a ∈ I := by
    have := I.sub_mem hb.2 ha₀
    convert this using 1
    ring
  have hsmod : a ≡ a₀ [SMOD I] := SModEq.sub_mem.mpr ha₀
  have hderiv :
      Ideal.Quotient.mk I (P.derivative.eval a) =
        Ideal.Quotient.mk I (P.derivative.eval a₀) :=
    SModEq.def.mp (hsmod.eval P.derivative)
  have hP'a : IsUnit (Ideal.Quotient.mk I (P.derivative.eval a)) := by
    rw [hderiv]
    exact hP'
  exact (eq_of_isRoot_of_sub_mem I (IsAdicComplete.le_jacobson_bot I)
    ha hb.1 hba hP'a).symm

end FormalImplicitRoot

namespace PowerSeries.Implicit

variable {R : Type*} [CommRing R]

/-- **Formal implicit lifting at an arbitrary base series.** If `S₀` solves
`P` modulo the parameter `X` and the derivative at `S₀` has unit scalar
constant coefficient, then `P` has a unique exact root with the same scalar
constant coefficient as `S₀`. -/
theorem existsUnique_isRoot_constantCoeff (P : Polynomial R⟦X⟧) (S₀ : R⟦X⟧)
    (hP : PowerSeries.constantCoeff (P.eval S₀) = 0)
    (hP' : IsUnit
      (PowerSeries.constantCoeff (P.derivative.eval S₀))) :
    ∃! S : R⟦X⟧,
      P.IsRoot S ∧ PowerSeries.constantCoeff S =
        PowerSeries.constantCoeff S₀ := by
  let I : Ideal R⟦X⟧ := .span {PowerSeries.X}
  letI : IsAdicComplete I R⟦X⟧ := by
    dsimp [I]
    infer_instance
  have hPmem : P.eval S₀ ∈ I := by
    simpa only [I, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] using hP
  have hPunit : IsUnit (P.derivative.eval S₀) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr hP'
  have hPquot :
      IsUnit (Ideal.Quotient.mk I (P.derivative.eval S₀)) :=
    hPunit.map (Ideal.Quotient.mk I)
  have hroot := FormalImplicitRoot.existsUnique_isRoot_sub_mem
    I P S₀ hPmem hPquot
  simpa only [I, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
    map_sub, sub_eq_zero] using hroot

/-- **Formal implicit-function theorem for a polynomial over a power-series
ring.** A vanishing parameter constant term and a unit scalar linear term give
a unique zero-constant formal root. -/
theorem existsUnique_zeroConstant_root (P : Polynomial R⟦X⟧)
    (h₀ : PowerSeries.constantCoeff (P.coeff 0) = 0)
    (h₁ : IsUnit (PowerSeries.constantCoeff (P.coeff 1))) :
    ∃! S : R⟦X⟧,
      PowerSeries.constantCoeff S = 0 ∧ P.eval S = 0 := by
  have hP : PowerSeries.constantCoeff (P.eval (0 : R⟦X⟧)) = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact h₀
  have hP' : IsUnit
      (PowerSeries.constantCoeff (P.derivative.eval (0 : R⟦X⟧))) := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative]
    simpa using h₁
  have hroot := existsUnique_isRoot_constantCoeff P (0 : R⟦X⟧) hP hP'
  simpa only [map_zero, Polynomial.IsRoot, and_comm] using hroot

/-- The distinguished zero-constant formal implicit root. -/
noncomputable def root (P : Polynomial R⟦X⟧)
    (h₀ : PowerSeries.constantCoeff (P.coeff 0) = 0)
    (h₁ : IsUnit (PowerSeries.constantCoeff (P.coeff 1))) : R⟦X⟧ :=
  Classical.choose (existsUnique_zeroConstant_root P h₀ h₁)

/-- The distinguished implicit root has zero constant coefficient. -/
@[simp]
theorem constantCoeff_root (P : Polynomial R⟦X⟧)
    (h₀ : PowerSeries.constantCoeff (P.coeff 0) = 0)
    (h₁ : IsUnit (PowerSeries.constantCoeff (P.coeff 1))) :
    PowerSeries.constantCoeff (root P h₀ h₁) = 0 :=
  (Classical.choose_spec (existsUnique_zeroConstant_root P h₀ h₁)).1.1

/-- The distinguished implicit series is a root of `P`. -/
@[simp]
theorem eval_root (P : Polynomial R⟦X⟧)
    (h₀ : PowerSeries.constantCoeff (P.coeff 0) = 0)
    (h₁ : IsUnit (PowerSeries.constantCoeff (P.coeff 1))) :
    P.eval (root P h₀ h₁) = 0 :=
  (Classical.choose_spec (existsUnique_zeroConstant_root P h₀ h₁)).1.2

/-- Every zero-constant root of `P` is the distinguished implicit root. -/
theorem eq_root (P : Polynomial R⟦X⟧)
    (h₀ : PowerSeries.constantCoeff (P.coeff 0) = 0)
    (h₁ : IsUnit (PowerSeries.constantCoeff (P.coeff 1)))
    {S : R⟦X⟧} (hS₀ : PowerSeries.constantCoeff S = 0)
    (hS : P.eval S = 0) : S = root P h₀ h₁ :=
  (Classical.choose_spec (existsUnique_zeroConstant_root P h₀ h₁)).2 S ⟨hS₀, hS⟩

end PowerSeries.Implicit
