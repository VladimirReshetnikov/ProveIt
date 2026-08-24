import GowersSzemeredi.Sections01_03

/-!
# Proofs for Gowers (2001), Sections 1--3

This file proves the elementary finite Fourier identities underlying Sections 2 and 3.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod ComplexConjugate
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma sum_exponential_mul {N : Nat} [NeZero N] (x : ZMod N) :
    ∑ r : ZMod N, exponential (x * r) = if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

@[simp] private lemma exponential_add {N : Nat} [NeZero N] (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma exponential_zero {N : Nat} [NeZero N] :
    exponential (0 : ZMod N) = 1 := by
  exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))

@[simp] private lemma star_exponential {N : Nat} [NeZero N] (x : ZMod N) :
    star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

private def finFourEquiv (X : Type*) : (Fin 4 → X) ≃ X × X × X × X where
  toFun q := (q 0, q 1, q 2, q 3)
  invFun q := ![q.1, q.2.1, q.2.2.1, q.2.2.2]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    rcases q with ⟨a, b, c, d⟩
    rfl

private lemma sum_fin_four {X R : Type*} [Fintype X] [AddCommMonoid R]
    (F : (Fin 4 → X) → R) :
    ∑ q, F q = ∑ a : X, ∑ b : X, ∑ c : X, ∑ d : X, F ![a, b, c, d] := by
  have h := Fintype.sum_equiv (finFourEquiv X) F
    (fun q : X × X × X × X ↦ F ![q.1, q.2.1, q.2.2.1, q.2.2.2])
    (fun q ↦ congrArg F ((finFourEquiv X).left_inv q).symm)
  simpa only [Fintype.sum_prod_type] using h

private lemma fourier_correlation {N : Nat} [NeZero N]
    (f g : ZMod N → Complex) (r : ZMod N) :
    fourier (correlation f g) r = fourier f r * star (fourier g r) := by
  simp only [fourier, correlation, ZMod.dft_apply, smul_eq_mul]
  calc
    ∑ s : ZMod N, exponential (-(s * r)) *
        ∑ t : ZMod N, f t * star (g (t - s)) =
        ∑ t : ZMod N, ∑ s : ZMod N,
          exponential (-(s * r)) * (f t * star (g (t - s))) := by
            simp_rw [mul_sum]
            rw [sum_comm]
    _ = ∑ t : ZMod N, ∑ u : ZMod N,
          exponential (-((t - u) * r)) * (f t * star (g u)) := by
            apply Finset.sum_congr rfl
            intro t _
            rw [← (Equiv.subLeft t).sum_comp]
            simp only [Equiv.subLeft_apply, sub_sub_cancel]
    _ = ∑ t : ZMod N, ∑ u : ZMod N,
          (exponential (-(t * r)) * f t) *
            (exponential (u * r) * star (g u)) := by
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro u _
            rw [show -((t - u) * r) = -(t * r) + u * r by ring, exponential_add]
            ring
    _ = (∑ t : ZMod N, exponential (-(t * r)) * f t) *
          star (∑ u : ZMod N, exponential (-(u * r)) * g u) := by
            simp only [star_sum, star_mul, star_exponential, neg_neg]
            simp_rw [mul_sum, sum_mul]
            conv_rhs => rw [sum_comm]
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro u _
            ring

/-- Fourier identity (1). -/
theorem identity_2_1_holds : identity_2_1 := by
  intro N _ f g r
  exact fourier_correlation f g r

private lemma fourier_parseval {N : Nat} [NeZero N]
    (f g : ZMod N → Complex) :
    (∑ r : ZMod N, fourier f r * star (fourier g r)) =
      (N : Complex) * ∑ s : ZMod N, f s * star (g s) := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]
  calc
    ∑ r : ZMod N,
        (∑ x : ZMod N, exponential (-(x * r)) * f x) *
          star (∑ y : ZMod N, exponential (-(y * r)) * g y) =
        ∑ r : ZMod N, ∑ x : ZMod N, ∑ y : ZMod N,
          (exponential (-(x * r)) * f x) *
            (star (g y) * exponential (y * r)) := by
              simp only [star_sum, star_mul, star_exponential, neg_neg]
              simp_rw [sum_mul, mul_sum]
    _ = ∑ x : ZMod N, ∑ y : ZMod N, ∑ r : ZMod N,
          (exponential (-(x * r)) * f x) *
            (star (g y) * exponential (y * r)) := by
              rw [sum_comm]
              apply Finset.sum_congr rfl
              intro x _
              rw [sum_comm]
    _ = ∑ x : ZMod N, ∑ y : ZMod N,
          (f x * star (g y)) *
            ∑ r : ZMod N, exponential ((y - x) * r) := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              rw [mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              have hchar :
                  exponential (-(x * r)) * exponential (y * r) =
                    exponential ((y - x) * r) := by
                rw [← exponential_add]
                congr 1
                ring
              rw [← hchar]
              ring
    _ = (N : Complex) * ∑ s : ZMod N, f s * star (g s) := by
              simp_rw [sum_exponential_mul]
              simp [sub_eq_zero]
              rw [← sum_mul]
              ring

/-- Fourier identity (2), Parseval's identity. -/
theorem identity_2_2_holds : identity_2_2 := by
  intro N _ f g
  exact fourier_parseval f g

/-- Fourier identity (3), the square-norm form of Parseval. -/
theorem identity_2_3_holds : identity_2_3 := by
  intro N _ f
  have h := fourier_parseval f f
  have hre := congrArg Complex.re h
  simpa [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow] using hre

/-- Fourier identity (4), Fourier inversion. -/
theorem identity_2_4_holds : identity_2_4 := by
  intro N _ f s
  symm
  simpa [fourier, exponential, ZMod.invDFT_apply, smul_eq_mul, mul_comm] using
    congrFun (ZMod.dft.symm_apply_apply f) s

/-- Lemma 2.1 / Fourier identity (5). -/
theorem lemma_2_1_holds : lemma_2_1 := by
  intro N _ f g
  have h := identity_2_3_holds N (correlation f g)
  simpa [fourier_correlation, correlation, norm_mul, mul_pow] using h

private lemma correlation_energy_eq_quadruples {N : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    ((∑ t : ZMod N,
        ‖∑ s : ZMod N, f s * star (f (s - t))‖ ^ 2 : Real) : Complex) =
      ∑ q : Fin 4 → ZMod N,
        if q 0 - q 1 = q 2 - q 3
          then f (q 0) * star (f (q 1) * f (q 2)) * f (q 3)
          else 0 := by
  calc
    ((∑ t : ZMod N,
        ‖∑ s : ZMod N, f s * star (f (s - t))‖ ^ 2 : Real) : Complex) =
        ∑ t : ZMod N, (∑ s : ZMod N, f s * star (f (s - t))) *
          star (∑ u : ZMod N, f u * star (f (u - t))) := by
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ t : ZMod N, ∑ s : ZMod N, ∑ u : ZMod N,
          (f s * star (f (s - t))) * (f (u - t) * star (f u)) := by
            apply Finset.sum_congr rfl
            intro t _
            simp only [star_sum, star_mul, star_star]
            simp_rw [sum_mul, mul_sum]
    _ = ∑ s : ZMod N, ∑ b : ZMod N, ∑ u : ZMod N,
          (f s * star (f b)) * (f (u - (s - b)) * star (f u)) := by
            rw [sum_comm]
            apply Finset.sum_congr rfl
            intro s _
            rw [← (Equiv.subLeft s).sum_comp]
            simp only [Equiv.subLeft_apply, sub_sub_cancel]
    _ = ∑ q : Fin 4 → ZMod N,
          if q 0 - q 1 = q 2 - q 3
            then f (q 0) * star (f (q 1) * f (q 2)) * f (q 3)
            else 0 := by
              rw [sum_fin_four]
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
                Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              apply Finset.sum_congr rfl
              intro c _
              have hiff (d : ZMod N) : a - b = c - d ↔ d = c - (a - b) := by
                constructor
                · intro h
                  calc
                    d = c - (c - d) := by abel
                    _ = c - (a - b) := by rw [← h]
                · intro h
                  rw [h]
                  abel
              simp_rw [hiff]
              rw [Fintype.sum_ite_eq']
              simp only [star_mul]
              ring

/-- Fourier identity (6), in additive-quadruple form. -/
theorem identity_2_6_holds : identity_2_6 := by
  intro N _ f
  have h := lemma_2_1_holds N f f
  have hr :
      (∑ r : ZMod N, ‖fourier f r‖ ^ 4) =
        (N : Real) * ∑ t : ZMod N,
          ‖∑ s : ZMod N, f s * star (f (s - t))‖ ^ 2 := by
    convert h using 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [← correlation_energy_eq_quadruples]
  exact_mod_cast hr

end LeanProofs.GowersSzemeredi
