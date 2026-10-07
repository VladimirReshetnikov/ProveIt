/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use MvPolynomial coefficient additivity and discharge every conversion goal
on Lean 4.32; mathematical statements are unchanged. -/
import OAI.Compat.Core
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Multilinear.Basic
import OAI.Combinatorics.Progressions.Estimates.RowShiftTopSymbol
import OAI.Combinatorics.Progressions.Estimates.TaggedZModOrderBounds
import OAI.Combinatorics.Progressions.Fourier.PolynomialCharacterRowPhase
import OAI.Combinatorics.Progressions.Fourier.PrimePowerCharacterDepth
import OAI.Combinatorics.Progressions.Fourier.PrimePowerTaggedCharacterRows
import OAI.Combinatorics.Progressions.Lattices.FiniteAffineClassAverage
import OAI.Combinatorics.Progressions.Lattices.LargestBadPrimeProduct
import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
import OAI.Combinatorics.Progressions.Probability.UniformHomExpectation

namespace OAI


namespace Erdos3

open MvPolynomial

theorem polynomialTranslate_add_apply {I R : Type*} [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) :
    polynomialTranslate u (polynomialTranslate v P) = polynomialTranslate (u + v) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, polynomialTranslate_C, Pi.add_apply]
    rw [add_assoc]

theorem polynomialTranslate_zero_apply {I R : Type*} [CommRing R] (P : MvPolynomial I R) :
    polynomialTranslate (fun _ => 0) P = P := by
  simp [polynomialTranslate]

noncomputable def polynomialDifference {I R : Type*} [CommRing R] (u : I → R) :
    MvPolynomial I R →ₗ[R] MvPolynomial I R :=
  (polynomialTranslate u).toLinearMap - LinearMap.id

theorem polynomialDifference_apply {I R : Type*} [CommRing R]
    (u : I → R) (P : MvPolynomial I R) :
    polynomialDifference u P = polynomialTranslate u P - P := rfl

theorem polynomialDifference_commute {I R : Type*} [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) :
    polynomialDifference u (polynomialDifference v P) =
      polynomialDifference v (polynomialDifference u P) := by
  simp only [polynomialDifference_apply, map_sub, polynomialTranslate_add_apply]
  rw [add_comm u v]
  abel

theorem polynomialDifference_degree {I R : Type*} [CommRing R]
    (u : I → R) (P : MvPolynomial I R) {d : ℕ} (hP : P.totalDegree ≤ d + 1) :
    (polynomialDifference u P).totalDegree ≤ d := by
  have hd := polynomialTranslate_sub_mem_weightedSupportLT u (1 : I → ℕ)
    (fun _ => by simp) ((mem_weightedSupportLE_one_iff P (d + 1)).mpr hP)
  apply (mem_weightedSupportLE_one_iff _ d).mp
  intro a ha
  have hlt : Finsupp.weight (1 : I → ℕ) a < d + 1 := hd ha
  change Finsupp.weight (1 : I → ℕ) a ≤ d
  omega

theorem polynomialDifference_eval {I R : Type*} [CommRing R]
    (u x : I → R) (P : MvPolynomial I R) :
    eval x (polynomialDifference u P) = eval (x + u) P - eval x P := by
  rw [polynomialDifference_apply, map_sub]
  change aeval x (polynomialTranslate u P) - eval x P = _
  rw [polynomialTranslate, comp_aeval_apply]
  simp only [map_add, aeval_X, aeval_C, Algebra.algebraMap_self_apply]
  rfl

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem degree_le_one_eq_constant_add_row {I R : Type*} [Fintype I] [CommRing R]
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    P = C (P.coeff 0) + rowPolynomial (polynomialLinearRow P) := by
  have he : P = C (P.coeff 0) + homogeneousComponent 1 P := by
    have hd : P.totalDegree = 0 ∨ P.totalDegree = 1 := by omega
    rcases hd with hd | hd
    · rw [homogeneousComponent_eq_zero 1 P (by omega), add_zero]
      exact totalDegree_eq_zero_iff_eq_C.mp hd
    · simpa [hd, Finset.sum_range_succ] using (sum_homogeneousComponent P).symm
  have hr : polynomialLinearRow (homogeneousComponent 1 P) = polynomialLinearRow P := by
    funext i
    simp only [polynomialLinearRow, coeff_homogeneousComponent, Finsupp.degree_single, ite_true]
  exact he.trans (congrArg (fun Q => C (P.coeff 0) + Q)
    ((homogeneous_eq_rowPolynomial _ (homogeneousComponent_isHomogeneous 1 P)).trans
      (congrArg rowPolynomial hr)))

theorem polynomialDifference_C {I R : Type*} [CommRing R] (u : I → R) (c : R) :
    polynomialDifference u (C c) = 0 := by
  rw [polynomialDifference_apply, polynomialTranslate_C, sub_self]

theorem polynomialDifference_row {I R : Type*} [Fintype I] [CommRing R]
    (u a : I → R) :
    polynomialDifference u (rowPolynomial a) = C (∑ i, a i * u i) := by
  simp only [polynomialDifference_apply, rowPolynomial, map_sum, map_mul,
    polynomialTranslate_C, polynomialTranslate_X, mul_add,
    add_sub_cancel_left]

theorem polynomialDifference_affine {I R : Type*} [Fintype I] [CommRing R]
    (u : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference u P = C (∑ i, polynomialLinearRow P i * u i) := by
  conv_lhs => rw [degree_le_one_eq_constant_add_row P hP]
  rw [map_add, polynomialDifference_C, zero_add, polynomialDifference_row]

theorem polynomialDifference_direction_add {I R : Type*} [Fintype I] [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference (u + v) P = polynomialDifference u P + polynomialDifference v P := by
  simp only [polynomialDifference_affine _ P hP, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, map_add]

theorem polynomialDifference_direction_smul {I R : Type*} [Fintype I] [CommRing R]
    (c : R) (u : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference (c • u) P = c • polynomialDifference u P := by
  rw [polynomialDifference_affine _ P hP, polynomialDifference_affine _ P hP,
    smul_eq_C_mul, ← map_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Erdos3


namespace Erdos3

noncomputable def polynomialIterDifference {I R : Type*} [CommRing R] :
    (n : ℕ) → MvPolynomial I R → (Fin n → I → R) → MvPolynomial I R
  | 0, P, _ => P
  | n + 1, P, u => polynomialIterDifference n (polynomialDifference (u 0) P) (Fin.tail u)

theorem polynomialIterDifference_add {I R : Type*} [CommRing R] (n : ℕ)
    (P Q : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (P + Q) u =
      polynomialIterDifference n P u + polynomialIterDifference n Q u := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, map_add]
    exact ih _ _ _

theorem polynomialIterDifference_smul {I R : Type*} [CommRing R] (n : ℕ)
    (c : R) (P : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (c • P) u = c • polynomialIterDifference n P u := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, map_smul]
    exact ih _ _

theorem polynomialIterDifference_commute {I R : Type*} [CommRing R] (n : ℕ)
    (v : I → R) (P : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (polynomialDifference v P) u =
      polynomialDifference v (polynomialIterDifference n P u) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference]
    rw [polynomialDifference_commute, ih]

theorem polynomialIterDifference_degree {I R : Type*} [CommRing R] (n d : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + d) (u : Fin n → I → R) :
    (polynomialIterDifference n P u).totalDegree ≤ d := by
  induction n generalizing P d with
  | zero => simpa only [polynomialIterDifference, zero_add] using hP
  | succ n ih =>
    exact ih d _ (polynomialDifference_degree (u 0) P (by omega)) (Fin.tail u)


open MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [Fintype I] [CommRing R] [Fintype R]

theorem polynomial_phase_difference_mean_sq_le (P : MvPolynomial I R)
    (χ : AddChar R ℂ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ 2 ≤
      𝔼 u : I → R, ‖𝔼 x : I → R, χ (eval x (polynomialDifference u P))‖ := by
  let f : (I → R) → ℂ := fun x => χ (eval x P)
  have hpoint (u x : I → R) : χ (eval x (polynomialDifference u P)) =
      star (multiplicativeDerivative f u x) := by
    rw [polynomialDifference_eval, addChar_sub_star]
    simp only [multiplicativeDerivative, star_mul, star_star, f]
  have hmean (u : I → R) :
      ‖𝔼 x, χ (eval x (polynomialDifference u P))‖ =
      ‖𝔼 x, multiplicativeDerivative f u x‖ := by
    simp only [hpoint, expect_star, norm_star]
  simp_rw [hmean]
  calc
    _ = ‖gowersMoment 1 f‖ := by
      rw [gowersMoment_one, norm_mul, norm_star, pow_two]
    _ ≤ 𝔼 u : I → R, ‖𝔼 x : I → R, multiplicativeDerivative f u x‖ :=
      RCLike.norm_expect_le (K := ℂ)

theorem polynomial_phase_iterDifference_bound (n : ℕ) (P : MvPolynomial I R)
    (χ : AddChar R ℂ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → R,
        ‖𝔼 x : I → R, χ (eval x (polynomialIterDifference n P u))‖ := by
  induction n generalizing P with
  | zero => simp [polynomialIterDifference]
  | succ n ih =>
    calc
      _ = (‖𝔼 x : I → R, χ (eval x P)‖ ^ 2) ^ (2 ^ n) := by
        rw [← pow_mul, pow_succ]; congr 1; omega
      _ ≤ (𝔼 u : I → R,
          ‖𝔼 x : I → R, χ (eval x (polynomialDifference u P))‖) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) (polynomial_phase_difference_mean_sq_le P χ) _
      _ ≤ 𝔼 u : I → R,
          ‖𝔼 x : I → R, χ (eval x (polynomialDifference u P))‖ ^ (2 ^ n) :=
        expect_pow_two_pow_le n _ (fun _ => norm_nonneg _)
      _ ≤ 𝔼 u : I → R, 𝔼 v : Fin n → I → R,
          ‖𝔼 x : I → R, χ (eval x (polynomialIterDifference n
            (polynomialDifference u P) v))‖ :=
        Finset.expect_le_expect (fun u _ => ih (polynomialDifference u P))
      _ = _ := by rw [expect_fin_cons]; rfl

theorem affine_polynomial_phase_mean_zero (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ 1) (χ : AddChar R ℂ) (hχ : Function.Injective χ)
    (hrow : polynomialLinearRow P ≠ 0) :
    (𝔼 x : I → R, χ (eval x P)) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, polynomialLinearRow P i ≠ 0 := by
    by_contra! h
    exact hrow (funext h)
  let u : I → R := Pi.single i 1
  have hlin : (∑ j, polynomialLinearRow P j * u j) = polynomialLinearRow P i := by
    simp [u, Pi.single_apply]
  have heval (x : I → R) : eval (x + u) P = eval x P + polynomialLinearRow P i := by
    have h := congrArg (eval x) (polynomialDifference_affine u P hP)
    rw [polynomialDifference_eval, eval_C, hlin] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  have hshift := expect_translate (fun x : I → R => χ (eval x P)) u
  have hmul : (𝔼 x : I → R, χ (eval x P)) * χ (polynomialLinearRow P i) =
      (𝔼 x : I → R, χ (eval x P)) := by
    conv_rhs => rw [← hshift]
    simp_rw [add_comm u, heval, χ.map_add_eq_mul]
    exact Finset.expect_mul _ _ _
  have hne : χ (polynomialLinearRow P i) ≠ 1 := by
    intro h
    exact hi (hχ (h.trans χ.map_zero_eq_one.symm))
  have hz : (𝔼 x : I → R, χ (eval x P)) * (χ (polynomialLinearRow P i) - 1) = 0 := by
    linear_combination hmul
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hne)

theorem norm_affine_polynomial_phase_mean (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ 1) (χ : AddChar R ℂ) (hχ : Function.Injective χ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ =
      if polynomialLinearRow P = 0 then (1 : ℝ) else 0 := by
  split_ifs with hrow
  · have hp : P = C (P.coeff 0) := by
      rw [degree_le_one_eq_constant_add_row P hP, hrow]
      simp [rowPolynomial]
    conv_lhs => rw [hp]
    simp only [eval_C, Fintype.expect_const, χ.norm_apply]
  · rw [affine_polynomial_phase_mean_zero P hP χ hχ hrow, norm_zero]

theorem polynomial_phase_bias_le_linearRow_probability (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1)
    (χ : AddChar R ℂ) (hχ : Function.Injective χ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → R,
        if polynomialLinearRow (polynomialIterDifference n P u) = 0 then (1 : ℝ) else 0 := by
  have h := polynomial_phase_iterDifference_bound n P χ
  simpa only [norm_affine_polynomial_phase_mean _
    (polynomialIterDifference_degree n 1 P hP _) χ hχ] using h

omit [Fintype I] [Fintype R] in

theorem totalDegree_sub_top_component_le (n : ℕ) (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ n + 1) :
    (P - homogeneousComponent (n + 1) P).totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff _ n).mp
  intro a ha
  have hcoeff : (P - homogeneousComponent (n + 1) P).coeff a ≠ 0 :=
    Finsupp.mem_support_iff.mp ha
  rw [coeff_sub, coeff_homogeneousComponent] at hcoeff
  have hne : a.degree ≠ n + 1 := by
    intro h
    exact hcoeff (by simp [h])
  have haP : a ∈ P.support := by
    apply mem_support_iff.mpr
    simpa only [ite_eq_right hne, sub_zero] using hcoeff
  have hbound := (mem_weightedSupportLE_one_iff P (n + 1)).mpr hP haP
  change Finsupp.weight (fun _ : I => 1) a ≤ n + 1 at hbound
  change Finsupp.weight (fun _ : I => 1) a ≤ n
  rw [← Finsupp.degree_eq_weight_one] at hbound ⊢
  omega

omit [Fintype I] [Fintype R] in

theorem polynomialIterDifference_linearRow_top_component (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1)
    (u : Fin n → I → R) :
    polynomialLinearRow (polynomialIterDifference n P u) =
      polynomialLinearRow (polynomialIterDifference n (homogeneousComponent (n + 1) P) u) := by
  let Q := P - homogeneousComponent (n + 1) P
  have hQ : Q.totalDegree ≤ n := totalDegree_sub_top_component_le n P hP
  have hdiff : (polynomialIterDifference n Q u).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero (polynomialIterDifference_degree n 0 Q (by simpa using hQ) u)
  have hconst := totalDegree_eq_zero_iff_eq_C.mp hdiff
  have hrowQ : polynomialLinearRow (polynomialIterDifference n Q u) = 0 := by
    funext i
    dsimp [polynomialLinearRow]
    rw [hconst, coeff_C]
    have hz : (0 : I →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h
      have hi := congrArg (fun a : I →₀ ℕ => a i) h
      simp at hi
    simp only [ite_eq_right hz]
  have hsplit : P = homogeneousComponent (n + 1) P + Q := by dsimp [Q]; abel
  conv_lhs => rw [hsplit, polynomialIterDifference_add]
  funext i
  simp only [polynomialLinearRow, MvPolynomial.coeff_add]
  have hi := congrFun hrowQ i
  change (polynomialIterDifference n Q u).coeff (Finsupp.single i 1) = 0 at hi
  rw [hi, add_zero]

theorem polynomial_phase_bias_le_top_linearRow_probability (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1)
    (χ : AddChar R ℂ) (hχ : Function.Injective χ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → R,
        if polynomialLinearRow
          (polynomialIterDifference n (homogeneousComponent (n + 1) P) u) = 0
        then (1 : ℝ) else 0 := by
  have h := polynomial_phase_bias_le_linearRow_probability n P hP χ hχ
  simpa only [polynomialIterDifference_linearRow_top_component n P hP] using h

theorem zmod_polynomial_phase_bias_le_linearRow_probability (N : ℕ) [NeZero N]
    (n : ℕ) (P : MvPolynomial I (ZMod N)) (hP : P.totalDegree ≤ n + 1) :
    ‖𝔼 x : I → ZMod N, ZMod.stdAddChar (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → ZMod N,
        if polynomialLinearRow (polynomialIterDifference n P u) = 0 then (1 : ℝ) else 0 :=
  by
    convert polynomial_phase_bias_le_linearRow_probability n P hP
      ZMod.stdAddChar ZMod.injective_stdAddChar using 1
    apply Finset.expect_congr rfl
    intro u _
    split_ifs <;> rfl

theorem zmod_polynomial_phase_decay_of_top_rank (N : ℕ) [NeZero N]
    (n : ℕ) (P : MvPolynomial I (ZMod N)) (hP : P.totalDegree ≤ n + 1)
    (p C B : ℝ) (hp : 0 < p)
    (hrank : (𝔼 u : Fin n → I → ZMod N,
      if polynomialLinearRow
        (polynomialIterDifference n (homogeneousComponent (n + 1) P) u) = 0
      then (1 : ℝ) else 0) ≤ p ^ (-C * B)) :
    ‖𝔼 x : I → ZMod N, ZMod.stdAddChar (eval x P)‖ ≤
      p ^ (-C * B / (2 ^ n : ℕ)) := by
  have h := polynomial_phase_bias_le_top_linearRow_probability n P hP
    ZMod.stdAddChar ZMod.injective_stdAddChar
  have hbound : ‖𝔼 x : I → ZMod N, ZMod.stdAddChar (eval x P)‖ ^ (2 ^ n) ≤
      p ^ (-C * B) := by
    apply h.trans
    convert hrank using 1 <;> first
    | rfl
    | (apply Finset.expect_congr rfl; intro u _; split_ifs <;> rfl)
  apply le_of_pow_le_pow_left₀ (by positivity : (2 ^ n : ℕ) ≠ 0)
    (Real.rpow_nonneg hp.le _)
  calc
    _ ≤ p ^ (-C * B) := hbound
    _ = (p ^ (-C * B / (2 ^ n : ℕ))) ^ (2 ^ n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      congr 1
      have hn : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
      exact (div_mul_cancel₀ _ hn).symm

end Erdos3


namespace Erdos3

open scoped Classical

theorem polynomialIterDifference_update_add {I R : Type*} [Fintype I] [CommRing R] (n : ℕ) :
    ∀ (P : MvPolynomial I R), P.totalDegree ≤ n →
      ∀ (u : Fin n → I → R) (j : Fin n) (a b : I → R),
        polynomialIterDifference n P (Function.update u j (a + b)) =
          polynomialIterDifference n P (Function.update u j a) +
            polynomialIterDifference n P (Function.update u j b) := by
  induction n with
  | zero => intro P hP u j; exact Fin.elim0 j
  | succ n ih =>
    intro P hP u j a b
    cases j using Fin.cases with
    | zero =>
      simp only [polynomialIterDifference, Function.update_self, Fin.tail_update_zero,
        polynomialIterDifference_commute]
      exact polynomialDifference_direction_add a b _
        (polynomialIterDifference_degree n 1 P hP (Fin.tail u))
    | succ j =>
      simp only [polynomialIterDifference, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      exact ih _ (polynomialDifference_degree (u 0) P hP) (Fin.tail u) j a b

theorem polynomialIterDifference_update_smul {I R : Type*} [Fintype I] [CommRing R] (n : ℕ) :
    ∀ (P : MvPolynomial I R), P.totalDegree ≤ n →
      ∀ (u : Fin n → I → R) (j : Fin n) (c : R) (a : I → R),
        polynomialIterDifference n P (Function.update u j (c • a)) =
          c • polynomialIterDifference n P (Function.update u j a) := by
  induction n with
  | zero => intro P hP u j; exact Fin.elim0 j
  | succ n ih =>
    intro P hP u j c a
    cases j using Fin.cases with
    | zero =>
      simp only [polynomialIterDifference, Function.update_self, Fin.tail_update_zero,
        polynomialIterDifference_commute]
      exact polynomialDifference_direction_smul c a _
        (polynomialIterDifference_degree n 1 P hP (Fin.tail u))
    | succ j =>
      simp only [polynomialIterDifference, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      exact ih _ (polynomialDifference_degree (u 0) P hP) (Fin.tail u) j c a

noncomputable def polynomialIterDifferenceMultilinear {I R : Type*} [Fintype I] [CommRing R]
    (n : ℕ) (P : MvPolynomial I R) (hP : P.totalDegree ≤ n) :
    MultilinearMap R (fun _ : Fin n => I → R) (MvPolynomial I R) :=
  MultilinearMap.mk' (polynomialIterDifference n P)
    (polynomialIterDifference_update_add n P hP) (polynomialIterDifference_update_smul n P hP)

theorem polynomialIterDifferenceMultilinear_apply {I R : Type*} [Fintype I] [CommRing R]
    (n : ℕ) (P : MvPolynomial I R) (hP : P.totalDegree ≤ n) (u : Fin n → I → R) :
    polynomialIterDifferenceMultilinear n P hP u = polynomialIterDifference n P u := rfl

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

noncomputable def polynomialCommonScale (c : R) :
    MvPolynomial I R →ₐ[R] MvPolynomial I R :=
  aeval (fun i => C c * X i)

theorem polynomialCommonScale_monomial (c r : R) (a : I →₀ ℕ) :
    polynomialCommonScale c (monomial a r) =
      C (c ^ a.degree) * monomial a r := by
  rw [polynomialCommonScale, aeval_monomial]
  simp only [algebraMap_eq, Finsupp.prod,
    mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.degree_apply]
  ring

theorem polynomialCommonScale_homogeneous (c : R) (d : ℕ)
    (P : MvPolynomial I R) (hP : P.IsHomogeneous d) :
    polynomialCommonScale c P = C (c ^ d) * P := by
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum]
  conv_rhs => rw [← P.support_sum_monomial_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [polynomialCommonScale_monomial]
  have hd : a.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (mem_support_iff.mp ha)
  rw [hd]

theorem polynomialCommonScale_homogeneousComponent (c : R) (d : ℕ)
    (P : MvPolynomial I R) :
    homogeneousComponent d (polynomialCommonScale c P) =
      C (c ^ d) * homogeneousComponent d P := by
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum, map_sum]
  conv_rhs => rw [← P.support_sum_monomial_coeff, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [polynomialCommonScale_monomial, homogeneousComponent_C_mul]
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial (P.coeff a) rfl)]
  by_cases hd : d = a.degree
  · simp only [hd, ite_true]
  · simp only [ite_eq_right hd, mul_zero]

theorem polynomialTranslate_top_component (r : I → R) (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1) :
    homogeneousComponent (n + 1) (polynomialTranslate r P) =
      homogeneousComponent (n + 1) P := by
  have hd := polynomialDifference_degree r P hP
  have hz := homogeneousComponent_eq_zero (n + 1) (polynomialDifference r P) (by omega)
  rw [polynomialDifference_apply, map_sub] at hz
  exact sub_eq_zero.mp hz

noncomputable def polynomialAffineClass (r : I → R) (c : R) :
    MvPolynomial I R →ₐ[R] MvPolynomial I R :=
  (polynomialCommonScale c).comp (polynomialTranslate r)

theorem polynomialAffineClass_eval (r x : I → R) (c : R) (P : MvPolynomial I R) :
    eval x (polynomialAffineClass r c P) = eval (fun i => r i + c * x i) P := by
  change aeval x (polynomialCommonScale c (polynomialTranslate r P)) = _
  rw [polynomialCommonScale, comp_aeval_apply, polynomialTranslate, comp_aeval_apply]
  simp only [map_mul, map_add, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
  change eval (fun i => c * x i + r i) P = eval (fun i => r i + c * x i) P
  exact congrArg (fun y : I → R => eval y P) (funext (fun i => add_comm _ _))

theorem polynomialAffineClass_apply (r : I → R) (c : R) (P : MvPolynomial I R) :
    polynomialAffineClass r c P = aeval (fun i => C c * X i + C (r i)) P := by
  change polynomialCommonScale c (polynomialTranslate r P) = _
  rw [polynomialTranslate, polynomialCommonScale, comp_aeval_apply]
  simp only [map_add, aeval_X, aeval_C, algebraMap_eq]

theorem polynomialAffineClass_degree (r : I → R) (c : R) (d : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ d) :
    (polynomialAffineClass r c P).totalDegree ≤ d := by
  rw [polynomialAffineClass_apply]
  apply (mem_weightedSupportLE_one_iff _ d).mp
  apply weightedSupportLE_aeval (1 : I → ℕ) (1 : I → ℕ) _ _
    ((mem_weightedSupportLE_one_iff P d).mpr hP)
  intro i
  apply (weightedSupportLE (1 : I → ℕ) 1).add_mem
  · exact weightedSupportLE_mul (weightedSupportLE_C _ 0 c) (weightedSupportLE_X _ i)
  · exact weightedSupportLE_C _ 1 (r i)

theorem polynomialAffineClass_mul_eq_constant (r : I → R) (c a : R)
    (hac : a * c = 0) (P : MvPolynomial I R) :
    C a * polynomialAffineClass r c P = C (a * eval r P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [polynomialAffineClass, polynomialCommonScale, polynomialTranslate]
  | add P Q hP hQ =>
    simp only [map_add, mul_add, hP, hQ]
  | mul_X P i hP =>
    have hX : polynomialAffineClass r c (X i) = C c * X i + C (r i) := by
      simp [polynomialAffineClass_apply]
    have heval : eval r (P * X i) = eval r P * r i := by simp
    rw [map_mul, hX, heval]
    calc
      _ = (C a * C c) * (polynomialAffineClass r c P * X i) +
          (C a * polynomialAffineClass r c P) * C (r i) := by ring
      _ = C (a * eval r P) * C (r i) := by
        rw [← map_mul, hac, map_zero, zero_mul, zero_add, hP]
      _ = _ := by rw [← map_mul, mul_assoc]

theorem polynomialAffineClass_top_component (r : I → R) (c : R) (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1) :
    homogeneousComponent (n + 1) (polynomialAffineClass r c P) =
      C (c ^ (n + 1)) * homogeneousComponent (n + 1) P := by
  change homogeneousComponent (n + 1) (polynomialCommonScale c (polynomialTranslate r P)) = _
  rw [polynomialCommonScale_homogeneousComponent, polynomialTranslate_top_component r n P hP]

theorem polynomialAffineClass_phase_bias_bound [Fintype I] [Fintype R]
    (r : I → R) (c : R) (n : ℕ) (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ n + 1) (χ : AddChar R ℂ) (hχ : Function.Injective χ) :
    ‖𝔼 x : I → R, χ (eval (fun i => r i + c * x i) P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → R,
        if polynomialLinearRow
          (polynomialIterDifference n (C (c ^ (n + 1)) * homogeneousComponent (n + 1) P) u) = 0
        then (1 : ℝ) else 0 := by
  have h := polynomial_phase_bias_le_top_linearRow_probability n
    (polynomialAffineClass r c P) (polynomialAffineClass_degree r c (n + 1) P hP) χ hχ
  simpa only [polynomialAffineClass_eval, polynomialAffineClass_top_component r c n P hP] using h

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem polynomialIterDifference_eval {I R : Type*} [CommRing R] (n : ℕ)
    (P : MvPolynomial I R) (u : Fin n → I → R) (base : I → R) :
    eval base (polynomialIterDifference n P u) =
      additiveBoxDifference n
        (fun (w : Fin n → I → R) (_ : Unit) => eval (fun j => base j + ∑ i, w i j) P)
        u (fun _ => 0) () := by
  induction n generalizing P with
  | zero => simp [polynomialIterDifference, additiveBoxDifference]
  | succ n ih =>
    simp only [polynomialIterDifference, additiveBoxDifference]
    rw [ih]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_add]
    apply congrArg (fun F : (Fin n → I → R) → Unit → R =>
      additiveBoxDifference n F (Fin.tail u) (fun _ => 0) ())
    funext w t
    rw [polynomialDifference_eval]
    apply congrArg (fun value : R => value - eval (fun j => base j + ∑ i, w i j) P)
    apply congrArg (fun point : I → R => eval point P)
    funext j
    simp only [Pi.add_apply]
    ring

theorem polynomialIterDifference_topSymbol {I : Type*} (n : ℕ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u : Fin n → I → ℝ) (base : I → ℝ) :
    eval base (polynomialIterDifference n P u) = polynomialTopSymbol n P u := by
  rw [polynomialIterDifference_eval]
  simpa only [Pi.zero_apply, sub_zero] using
    vector_shift_difference_eq_topSymbol base P hP u (fun _ => 0)

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {I R S : Type*} [CommRing R] [CommRing S]

theorem polynomialTranslate_map_coefficients (φ : R →+* S) (u : I → R)
    (P : MvPolynomial I R) :
    map φ (polynomialTranslate u P) =
      polynomialTranslate (fun i => φ (u i)) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, map_X, polynomialTranslate_X, map_add, map_C, hP]

theorem polynomialDifference_map_coefficients (φ : R →+* S) (u : I → R)
    (P : MvPolynomial I R) :
    map φ (polynomialDifference u P) =
      polynomialDifference (fun i => φ (u i)) (map φ P) := by
  simp only [polynomialDifference_apply, map_sub, polynomialTranslate_map_coefficients]

theorem polynomialIterDifference_map_coefficients (φ : R →+* S) (n : ℕ)
    (u : Fin n → I → R) (P : MvPolynomial I R) :
    map φ (polynomialIterDifference n P u) =
      polynomialIterDifference n (map φ P) (fun j i => φ (u j i)) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, ih, polynomialDifference_map_coefficients]
    rfl

theorem polynomialIterDifference_C_mul (c : R) (n : ℕ)
    (u : Fin n → I → R) (P : MvPolynomial I R) :
    polynomialIterDifference n (C c * P) u = C c * polynomialIterDifference n P u := by
  simpa only [smul_eq_C_mul] using polynomialIterDifference_smul n c P u

theorem zmod_mul_denominator_eq_zero_iff (M d : ℕ) [NeZero M] [NeZero d]
    (x : ZMod (M * d)) :
    (d : ZMod (M * d)) * x = 0 ↔
      ZMod.castHom (dvd_mul_right M d) (ZMod M) x = 0 := by
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  rw [mul_comm M d, Nat.mul_dvd_mul_iff_left (NeZero.pos d)]

theorem polynomialIterDifference_scaled_row_reduction (M d : ℕ) [NeZero M] [NeZero d]
    (n : ℕ) (H : MvPolynomial I (ZMod (M * d))) (u : Fin n → I → ZMod (M * d)) :
    polynomialLinearRow (polynomialIterDifference n (C (d : ZMod (M * d)) * H) u) = 0 ↔
      polynomialLinearRow (polynomialIterDifference n
        (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H)
        (fun j i => ZMod.castHom (dvd_mul_right M d) (ZMod M) (u j i))) = 0 := by
  rw [polynomialIterDifference_C_mul, ← polynomialIterDifference_map_coefficients]
  simp only [funext_iff, polynomialLinearRow, coeff_C_mul, coeff_map, Pi.zero_apply,
    zmod_mul_denominator_eq_zero_iff]

theorem polynomialIterDifference_scaled_row_probability [Fintype I]
    (M d : ℕ) [NeZero M] [NeZero d] (n : ℕ)
    (H : MvPolynomial I (ZMod (M * d))) :
    (𝔼 u : Fin n → I → ZMod (M * d),
      if polynomialLinearRow (polynomialIterDifference n (C (d : ZMod (M * d)) * H) u) = 0
      then (1 : ℝ) else 0) =
    𝔼 u : Fin n → I → ZMod M,
      if polynomialLinearRow (polynomialIterDifference n
        (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H) u) = 0
      then (1 : ℝ) else 0 := by
  calc
    _ = 𝔼 u : Fin n → I → ZMod (M * d),
        if polynomialLinearRow (polynomialIterDifference n
          (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H)
          (fun j i => ZMod.castHom (dvd_mul_right M d) (ZMod M) (u j i))) = 0
        then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro u _
      have hevent := polynomialIterDifference_scaled_row_reduction M d n H u
      simp only [hevent]
    _ = _ := expect_mul_modulus_reduction (I := I) n M d
      (fun v => if polynomialLinearRow (polynomialIterDifference n
        (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H) v) = 0
        then (1 : ℝ) else 0)

theorem zmod_polynomial_phase_bias_reduced_denominator [Fintype I]
    (M d : ℕ) [NeZero M] [NeZero d] (n : ℕ)
    (P H : MvPolynomial I (ZMod (M * d))) (hP : P.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = C (d : ZMod (M * d)) * H) :
    ‖𝔼 x : I → ZMod (M * d), ZMod.stdAddChar (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → ZMod M,
        if polynomialLinearRow (polynomialIterDifference n
          (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H) u) = 0
        then (1 : ℝ) else 0 := by
  have h := polynomial_phase_bias_le_top_linearRow_probability n P hP
    ZMod.stdAddChar ZMod.injective_stdAddChar
  rw [htop] at h
  apply h.trans_eq
  convert polynomialIterDifference_scaled_row_probability M d n H using 1
  apply Finset.expect_congr rfl
  intro u _
  split_ifs <;> rfl

theorem zmod_polynomial_phase_bias_reduced_denominator_of_mul [Fintype I]
    (N M d : ℕ) [NeZero N] [NeZero M] [NeZero d] (hN : N = M * d) (n : ℕ)
    (P H : MvPolynomial I (ZMod N)) (hP : P.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = C (d : ZMod N) * H) :
    ‖𝔼 x : I → ZMod N, ZMod.stdAddChar (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → ZMod M,
        if polynomialLinearRow (polynomialIterDifference n
          (map (ZMod.castHom (show M ∣ N from ⟨d, hN⟩) (ZMod M)) H) u) = 0
        then (1 : ℝ) else 0 := by
  subst N
  exact zmod_polynomial_phase_bias_reduced_denominator M d n P H hP htop

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

theorem tagged_affine_phase_degree {s : ℕ} (h : Fin s)
    (F : Fin s → MvPolynomial I R) (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (a : Fin s → R) (r : I → R) (c : R)
    (hkill : ∀ j, h < j → a j * c = 0) :
    (∑ j, C (a j) * polynomialAffineClass r c (F j)).totalDegree ≤ h.val + 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  by_cases hj : h < j
  · rw [polynomialAffineClass_mul_eq_constant r c (a j) (hkill j hj), totalDegree_C]
    exact Nat.zero_le _
  · have hjh : j.val ≤ h.val := by simpa using le_of_not_gt hj
    have hd := totalDegree_mul (C (a j)) (polynomialAffineClass r c (F j))
    rw [totalDegree_C, zero_add] at hd
    exact hd.trans ((polynomialAffineClass_degree r c (j.val + 1) (F j) (hF j)).trans
      (Nat.add_le_add_right hjh 1))

theorem tagged_affine_phase_top_component {s : ℕ} (h : Fin s)
    (F : Fin s → MvPolynomial I R) (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (a : Fin s → R) (r : I → R) (c : R)
    (hkill : ∀ j, h < j → a j * c = 0) :
    homogeneousComponent (h.val + 1) (∑ j, C (a j) * polynomialAffineClass r c (F j)) =
      C (a h * c ^ (h.val + 1)) * homogeneousComponent (h.val + 1) (F h) := by
  rw [map_sum, Finset.sum_eq_single h]
  · rw [homogeneousComponent_C_mul, polynomialAffineClass_top_component r c h.val (F h) (hF h),
      ← mul_assoc, ← map_mul]
  · intro j _ hj
    by_cases hjh : h < j
    · rw [polynomialAffineClass_mul_eq_constant r c (a j) (hkill j hjh)]
      exact homogeneousComponent_eq_zero _ _ (by rw [totalDegree_C]; omega)
    · have hjh' : j.val < h.val := by
        have hle : j ≤ h := le_of_not_gt hjh
        exact_mod_cast (show j < h from lt_of_le_of_ne hle hj)
      apply homogeneousComponent_eq_zero
      have hd := totalDegree_mul (C (a j)) (polynomialAffineClass r c (F j))
      rw [totalDegree_C, zero_add] at hd
      exact (hd.trans (polynomialAffineClass_degree r c (j.val + 1) (F j) (hF j))).trans_lt
        (Nat.add_lt_add_right hjh' 1)
  · simp

theorem zmod_tagged_affine_phase_bias_reduced_denominator [Fintype I]
    (M d : ℕ) [NeZero M] [NeZero d] {s : ℕ} (h : Fin s)
    (F : Fin s → MvPolynomial I (ZMod (M * d)))
    (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (a : Fin s → ZMod (M * d)) (r : I → ZMod (M * d)) (c b : ZMod (M * d))
    (hkill : ∀ j, h < j → a j * c = 0)
    (hdenom : a h * c ^ (h.val + 1) = (d : ZMod (M * d)) * b) :
    ‖𝔼 x : I → ZMod (M * d),
      ZMod.stdAddChar (∑ j, a j * eval (fun i => r i + c * x i) (F j))‖ ^ (2 ^ h.val) ≤
      𝔼 u : Fin h.val → I → ZMod M,
        if polynomialLinearRow (polynomialIterDifference h.val
          (map (ZMod.castHom (dvd_mul_right M d) (ZMod M))
            (C b * homogeneousComponent (h.val + 1) (F h))) u) = 0
        then (1 : ℝ) else 0 := by
  have htop : homogeneousComponent (h.val + 1)
      (∑ j, C (a j) * polynomialAffineClass r c (F j)) =
      C (d : ZMod (M * d)) * (C b * homogeneousComponent (h.val + 1) (F h)) := by
    rw [tagged_affine_phase_top_component h F hF a r c hkill, hdenom, map_mul, mul_assoc]
  have hbound := zmod_polynomial_phase_bias_reduced_denominator M d h.val
    (∑ j, C (a j) * polynomialAffineClass r c (F j))
    (C b * homogeneousComponent (h.val + 1) (F h))
    (tagged_affine_phase_degree h F hF a r c hkill) htop
  simpa only [map_sum, map_mul, eval_C, polynomialAffineClass_eval] using hbound

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

private theorem pow_tag_killed {R : Type*} [CommRing R]
    (p ell : R) (A a k : ℕ) (ha : a ≤ A) (hk : a ≤ k) (hzero : p ^ A = 0) :
    (p ^ (A - a) * ell) * p ^ k = 0 := by
  have hAk : A ≤ A - a + k := by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hAk
  have hpow : p ^ (A - a + k) = 0 := by rw [ht, pow_add, hzero, zero_mul]
  calc
    _ = p ^ (A - a + k) * ell := by rw [pow_add]; ring
    _ = 0 := by rw [hpow, zero_mul]

private theorem pow_tag_top_factor {R : Type*} [CommRing R]
    (p ell : R) (A a k h B : ℕ) (ha : a ≤ A)
    (hB : B = a - h * k) (hBp : 0 < B) :
    (p ^ (A - a) * ell) * (p ^ k) ^ h = p ^ (A - B) * ell := by
  have hka : h * k < a := Nat.sub_pos_iff_lt.mp (hB ▸ hBp)
  have he : A - a + k * h = A - B := by rw [Nat.mul_comm k h]; omega
  calc
    _ = p ^ (A - a + k * h) * ell := by rw [pow_add, pow_mul]; ring
    _ = _ := by rw [he]

theorem zmod_primePower_tag_factors (p A B k : ℕ) [NeZero p]
    (hBA : B ≤ A) {s : ℕ} (h : Fin s) (depth : Fin s → ℕ)
    (hdepth : ∀ j, depth j ≤ A) (hB : B = depth h - (h.val + 1) * k) (hBp : 0 < B)
    (hhigher : ∀ j, h < j → depth j ≤ k)
    (ell : Fin s → ZMod (p ^ B * p ^ (A - B))) :
    (∀ j, h < j →
      (((p : ZMod (p ^ B * p ^ (A - B))) ^ (A - depth j) * ell j) *
        (p : ZMod (p ^ B * p ^ (A - B))) ^ k = 0)) ∧
    (((p : ZMod (p ^ B * p ^ (A - B))) ^ (A - depth h) * ell h) *
      ((p : ZMod (p ^ B * p ^ (A - B))) ^ k) ^ (h.val + 1) =
      (p ^ (A - B) : ℕ) * ell h) := by
  have hzero : (p : ZMod (p ^ B * p ^ (A - B))) ^ A = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    have he : p ^ B * p ^ (A - B) = p ^ A := by
      rw [← pow_add, Nat.add_sub_of_le hBA]
    rw [he]
  constructor
  · intro j hj
    exact pow_tag_killed _ _ A (depth j) k (hdepth j) (hhigher j hj) hzero
  · simpa only [Nat.cast_pow] using
      pow_tag_top_factor (p : ZMod (p ^ B * p ^ (A - B))) (ell h)
        A (depth h) k (h.val + 1) B (hdepth h) hB hBp

theorem zmod_primePower_tagged_affine_phase_bias {Index : Type*} [Fintype Index]
    (p A B k : ℕ) [NeZero p] (hBA : B ≤ A) {s : ℕ} (h : Fin s)
    (depth : Fin s → ℕ) (hdepth : ∀ j, depth j ≤ A)
    (hB : B = depth h - (h.val + 1) * k) (hBp : 0 < B)
    (hhigher : ∀ j, h < j → depth j ≤ k)
    (F : Fin s → MvPolynomial Index (ZMod (p ^ B * p ^ (A - B))))
    (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (ell : Fin s → ZMod (p ^ B * p ^ (A - B)))
    (r : Index → ZMod (p ^ B * p ^ (A - B))) :
    ‖𝔼 x : Index → ZMod (p ^ B * p ^ (A - B)),
      ZMod.stdAddChar (∑ j, (p : ZMod (p ^ B * p ^ (A - B))) ^ (A - depth j) * ell j *
        eval (fun i => r i + (p : ZMod (p ^ B * p ^ (A - B))) ^ k * x i) (F j))‖ ^
          (2 ^ h.val) ≤
      𝔼 u : Fin h.val → Index → ZMod (p ^ B),
        if polynomialLinearRow (polynomialIterDifference h.val
          (map (ZMod.castHom (dvd_mul_right (p ^ B) (p ^ (A - B))) (ZMod (p ^ B)))
            (C (ell h) * homogeneousComponent (h.val + 1) (F h))) u) = 0
        then (1 : ℝ) else 0 := by
  obtain ⟨hkill, hdenom⟩ := zmod_primePower_tag_factors p A B k hBA h depth hdepth hB hBp hhigher ell
  exact zmod_tagged_affine_phase_bias_reduced_denominator (p ^ B) (p ^ (A - B)) h F hF
    (fun j => (p : ZMod (p ^ B * p ^ (A - B))) ^ (A - depth j) * ell j) r
    ((p : ZMod (p ^ B * p ^ (A - B))) ^ k) (ell h) hkill hdenom

theorem zmod_primePower_tagged_affine_phase_bias_at_modulus {Index : Type*} [Fintype Index]
    (p A B k : ℕ) [NeZero p] (hBA : B ≤ A) {s : ℕ} (h : Fin s)
    (depth : Fin s → ℕ) (hdepth : ∀ j, depth j ≤ A)
    (hB : B = depth h - (h.val + 1) * k) (hBp : 0 < B)
    (hhigher : ∀ j, h < j → depth j ≤ k)
    (F : Fin s → MvPolynomial Index (ZMod (p ^ A)))
    (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (ell : Fin s → ZMod (p ^ A)) (r : Index → ZMod (p ^ A)) :
    ‖𝔼 x : Index → ZMod (p ^ A),
      ZMod.stdAddChar (∑ j, (p : ZMod (p ^ A)) ^ (A - depth j) * ell j *
        eval (fun i => r i + (p : ZMod (p ^ A)) ^ k * x i) (F j))‖ ^ (2 ^ h.val) ≤
      𝔼 u : Fin h.val → Index → ZMod (p ^ B),
        if polynomialLinearRow (polynomialIterDifference h.val
          (map (ZMod.castHom (Nat.pow_dvd_pow p hBA) (ZMod (p ^ B)))
            (C (ell h) * homogeneousComponent (h.val + 1) (F h))) u) = 0
        then (1 : ℝ) else 0 := by
  let c : ZMod (p ^ A) := (p : ZMod (p ^ A)) ^ k
  let a : Fin s → ZMod (p ^ A) := fun j => (p : ZMod (p ^ A)) ^ (A - depth j) * ell j
  have hzero : (p : ZMod (p ^ A)) ^ A = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ A)
  have hkill : ∀ j, h < j → a j * c = 0 := by
    intro j hj
    exact pow_tag_killed _ _ A (depth j) k (hdepth j) (hhigher j hj) hzero
  have hdenom : a h * c ^ (h.val + 1) = (p ^ (A - B) : ℕ) * ell h := by
    simpa only [Nat.cast_pow] using
      pow_tag_top_factor (p : ZMod (p ^ A)) (ell h) A (depth h) k (h.val + 1) B
        (hdepth h) hB hBp
  have htop : homogeneousComponent (h.val + 1)
      (∑ j, C (a j) * polynomialAffineClass r c (F j)) =
      C (p ^ (A - B) : ZMod (p ^ A)) *
        (C (ell h) * homogeneousComponent (h.val + 1) (F h)) := by
    rw [tagged_affine_phase_top_component h F hF a r c hkill, hdenom,
      Nat.cast_pow, map_mul, mul_assoc]
  have hN : p ^ A = p ^ B * p ^ (A - B) := by
    rw [← pow_add, Nat.add_sub_of_le hBA]
  have hbound := zmod_polynomial_phase_bias_reduced_denominator_of_mul
    (p ^ A) (p ^ B) (p ^ (A - B)) hN h.val
    (∑ j, C (a j) * polynomialAffineClass r c (F j))
    (C (ell h) * homogeneousComponent (h.val + 1) (F h))
    (tagged_affine_phase_degree h F hF a r c hkill) (by simpa only [Nat.cast_pow] using htop)
  simpa only [map_sum, map_mul, eval_C, polynomialAffineClass_eval, a, c] using hbound

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def modularRankDecayExponent (s : ℕ) (C : ℝ) : ℝ :=
  C / ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ)

def modularRankChargeFactor (s : ℕ) : ℕ := 4 * s * (2 ^ s * s.factorial)

noncomputable def primePowerHomogeneousRankProbability
    {V J : Type*} [Fintype V] [Fintype J]
    (p A B n : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : J → MvPolynomial V (ZMod (p ^ A))) (row : J → ZMod (p ^ B)) : ℝ :=
  𝔼 u : Fin n → V → ZMod (p ^ B),
    if polynomialLinearRow (polynomialIterDifference n
      (polynomialCharacterRow row (fun i =>
        map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
          (homogeneousComponent (n + 1) (F i)))) u) = 0 then 1 else 0

private theorem norm_le_rpow_div_two_pow (n : ℕ) (z : ℂ) (p t : ℝ) (hp : 0 < p)
    (hbound : ‖z‖ ^ (2 ^ n) ≤ p ^ t) :
    ‖z‖ ≤ p ^ (t / (2 ^ n : ℕ)) := by
  apply le_of_pow_le_pow_left₀ (by positivity : (2 ^ n : ℕ) ≠ 0)
    (Real.rpow_nonneg hp.le _)
  calc
    _ ≤ p ^ t := hbound
    _ = (p ^ (t / (2 ^ n : ℕ))) ^ (2 ^ n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      congr 1
      have hn : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
      exact (div_mul_cancel₀ _ hn).symm

theorem primePower_row_phase_decay_large
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A a b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (depth : Fin s → ℕ) (hdepth : ∀ j, depth j ≤ A)
    (hmax : ∀ j, depth j ≤ a) (hattained : ∃ j, depth j = a)
    (coeff : ∀ j, J j → ZMod (p ^ A))
    (hunit : ∀ j, 0 < depth j → ∀ {B : ℕ} (hB : B ≤ depth j),
      ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p (hB.trans (hdepth j)))
        (ZMod (p ^ B)) (coeff j i)))
    (hlarge : modularRankChargeFactor s * (b + e) < a)
    (r : V → ZMod (p ^ A)) :
    ‖𝔼 x : V → ZMod (p ^ A),
      ZMod.stdAddChar (∑ j, (p : ZMod (p ^ A)) ^ (A - depth j) *
        ∑ i, coeff j i * eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤
      (p : ℝ) ^ (-modularRankDecayExponent s C * a) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  obtain ⟨h, k, B, hek, hhigher, hB, hbB, hBa, hnumeric⟩ :=
    exists_modular_uncharged_decay_parameters hs depth a b e hmax hattained hlarge p C hpR hC
  have hBh : B ≤ depth h := hB ▸ Nat.sub_le _ _
  have hBA : B ≤ A := hBh.trans (hdepth h)
  have hBp : 0 < B := (Nat.zero_le b).trans_lt hbB
  let Fs (j : Fin s) : MvPolynomial V (ZMod (p ^ A)) := polynomialCharacterRow (coeff j) (F j)
  have hFs : ∀ j, (Fs j).totalDegree ≤ j.val + 1 := by
    intro j
    exact polynomialCharacterRow_totalDegree_le _ _ (hF j)
  let f : (V → ZMod (p ^ A)) → ℂ := fun t =>
    ZMod.stdAddChar (∑ j, (p : ZMod (p ^ A)) ^ (A - depth j) * ∑ i, coeff j i * eval t (F j i))
  have hclasses (t : V → ZMod (p ^ A)) :
      ‖𝔼 x : V → ZMod (p ^ A), f (fun v => t v + (p : ZMod (p ^ A)) ^ k * x v)‖ ≤
        (p : ℝ) ^ (-C * B / (2 ^ h.val : ℕ)) := by
    have hphase := zmod_primePower_tagged_affine_phase_bias_at_modulus p A B k hBA h
      depth hdepth hB hBp hhigher Fs hFs (fun _ => 1) t
    have hr := hrank B hbB hBA h
      (fun i => ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)) (coeff h i))
      (hunit h (hBp.trans_le hBh) hBh)
    have hprob : (𝔼 u : Fin h.val → V → ZMod (p ^ B),
        if polynomialLinearRow (polynomialIterDifference h.val
          (map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
            (homogeneousComponent (h.val + 1) (Fs h))) u) = 0 then (1 : ℝ) else 0) ≤
          (p : ℝ) ^ (-C * B) := by
      simpa only [primePowerHomogeneousRankProbability, Fs,
        polynomialCharacterRow_homogeneousComponent, polynomialCharacterRow_map] using hr
    have hbias : ‖𝔼 x : V → ZMod (p ^ A),
        f (fun v => t v + (p : ZMod (p ^ A)) ^ k * x v)‖ ^ (2 ^ h.val) ≤
          (p : ℝ) ^ (-C * B) := by
      apply le_trans ?_ hprob
      simpa only [mul_one, map_one, one_mul, f, Fs, polynomialCharacterRow_eval] using hphase
    exact norm_le_rpow_div_two_pow h.val _ p (-C * B) (by exact_mod_cast hp.pos) hbias
  have hcoarse := norm_scalar_affine_class_mean_le
    ((p : ZMod (p ^ A)) ^ e) ((p : ZMod (p ^ A)) ^ (k - e)) r f
    ((p : ℝ) ^ (-C * B / (2 ^ h.val : ℕ))) (by
      simpa only [← pow_add, Nat.add_sub_of_le hek] using hclasses)
  exact hcoarse.trans hnumeric

theorem primePower_polynomial_character_decay
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A a b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) (horder : orderOf χ = p ^ a)
    (r : V → ZMod (p ^ A)) :
    ‖𝔼 x : V → ZMod (p ^ A),
      χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤
      (p : ℝ) ^ (modularRankDecayExponent s C * modularRankChargeFactor s * (b + e)) *
        (p : ℝ) ^ (-modularRankDecayExponent s C * a) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hP : 0 ≤ modularRankDecayExponent s C := by
    dsimp [modularRankDecayExponent]
    positivity
  have hnorm : ‖𝔼 x : V → ZMod (p ^ A),
      χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤ 1 := by
    calc
      _ ≤ 𝔼 x : V → ZMod (p ^ A),
          ‖χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ :=
        RCLike.norm_expect_le (K := ℂ)
      _ = 1 := by simp only [χ.norm_apply, Fintype.expect_const]
  apply modular_local_decay_budget hpR hP (by positivity) (by positivity) hnorm
  intro hlargeR
  have hlarge : modularRankChargeFactor s * (b + e) < a := by
    exact_mod_cast hlargeR
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  obtain ⟨depth, hdepth, coeff, hcoord, hunit, hphase⟩ :=
    exists_primePower_tagged_ambient_rows hp χ
  obtain ⟨hmax, hattained⟩ := primePower_character_tag_depth_max hp χ depth hcoord horder
  have h := primePower_row_phase_decay_large hs p A a b e hp C hC F hF hrank
    depth hdepth hmax hattained coeff hunit hlarge r
  simpa only [hphase, Nat.cast_pow] using h

theorem primePower_polynomial_image_characteristic_decay
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) :
    ‖finiteImageCharacteristic (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (fun x j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i)) χ‖ ≤
      ((p ^ (b + e) : ℕ) : ℝ) ^ (modularRankDecayExponent s C * modularRankChargeFactor s) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
  have hkill : χ ^ (p ^ A) = 1 := by
    ext x
    rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow]
    have hz : (p ^ A) • x = 0 := by
      ext j i
      simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    rw [hz, AddChar.map_zero_eq_one, AddChar.one_apply]
  obtain ⟨a, _, horder⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hkill)
  have h := primePower_polynomial_character_decay hs p A a b e hp C hC F hF hrank χ horder r
  rw [finiteImageCharacteristic, FiniteProbabilityWeights.uniform_complexMean]
  apply h.trans_eq
  rw [horder, Nat.cast_pow, Nat.cast_pow,
    ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ p),
    ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ p)]
  congr 1 <;> congr 1 <;> push_cast <;> ring

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem totalDegree_map_le {V R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (F : MvPolynomial V R) : (map φ F).totalDegree ≤ F.totalDegree := by
  unfold totalDegree
  apply Finset.sup_le
  intro m hm
  exact le_totalDegree (support_map_subset φ F hm)

noncomputable def integerPolynomialRankProbability
    {V J : Type*} [Fintype V] [Fintype J]
    (p B n : ℕ) [NeZero p]
    (F : J → MvPolynomial V ℤ) (row : J → ZMod (p ^ B)) : ℝ :=
  𝔼 u : Fin n → V → ZMod (p ^ B),
    if polynomialLinearRow (polynomialIterDifference n
      (polynomialCharacterRow row (fun i =>
        map (Int.castRingHom (ZMod (p ^ B)))
          (homogeneousComponent (n + 1) (F i)))) u) = 0 then 1 else 0

theorem map_integerPolynomial_homogeneousComponent
    {V : Type*} (p A B d : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : MvPolynomial V ℤ) :
    map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent d (map (Int.castRingHom (ZMod (p ^ A))) F)) =
      map (Int.castRingHom (ZMod (p ^ B))) (homogeneousComponent d F) := by
  have hcomp : (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))).comp
      (Int.castRingHom (ZMod (p ^ A))) = Int.castRingHom (ZMod (p ^ B)) :=
    RingHom.eq_intCast' _
  rw [← map_homogeneousComponent, MvPolynomial.map_map, hcomp]

theorem primePowerHomogeneousRankProbability_integerPolynomial
    {V J : Type*} [Fintype V] [Fintype J]
    (p A B n : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : J → MvPolynomial V ℤ) (row : J → ZMod (p ^ B)) :
    primePowerHomogeneousRankProbability p A B n hBA
      (fun i => map (Int.castRingHom (ZMod (p ^ A))) (F i)) row =
      integerPolynomialRankProbability p B n F row := by
  unfold primePowerHomogeneousRankProbability integerPolynomialRankProbability
  have hF : (fun i => map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent (n + 1) (map (Int.castRingHom (ZMod (p ^ A))) (F i)))) =
      (fun i => map (Int.castRingHom (ZMod (p ^ B)))
        (homogeneousComponent (n + 1) (F i))) := by
    funext i
    exact map_integerPolynomial_homogeneousComponent p A B (n + 1) hBA (F i)
  rw [hF]

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem primePower_crt_coprime {L : Type*} (p A : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) :
    Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)) := by
  intro l k hlk
  exact Nat.coprime_pow_primes (A l) (A k) (hp l) (hp k) (hinj.ne hlk)

theorem crt_integer_polynomial_characteristic_decay
    {L V : Type*} [Fintype L] [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A b e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (l : L) (B : ℕ) (_ : b l < B) (_hBA : B ≤ A l) (j : Fin s)
      (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability (p l) B j.val (F j) row ≤
        (p l : ℝ) ^ (-C * B))
    (r : ∀ l, V → ZMod (p l ^ A l))
    (χ : AddChar (∀ j, J j → ZMod (∏ l, p l ^ A l)) ℂ) :
    ‖finiteImageCharacteristic
      (FiniteProbabilityWeights.pi (fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l))))
      (fun x j i => eval₂ (Int.castRingHom (ZMod (∏ l, p l ^ A l)))
        (crtInput (fun l => p l ^ A l) (primePower_crt_coprime p A hp hinj)
          (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)) (F j i)) χ‖ ≤
      (∏ l, ((p l ^ (b l + e l) : ℕ) : ℝ)) ^
        (modularRankDecayExponent s C * modularRankChargeFactor s) *
          (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
  let q : L → ℕ := fun l => p l ^ A l
  let : ∀ l, NeZero (q l) := fun l => inferInstanceAs (NeZero (p l ^ A l))
  let : NeZero (∏ l, q l) := ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => NeZero.ne (q l))⟩
  let hq := primePower_crt_coprime p A hp hinj
  let E := taggedOutputCRTEquiv J q hq
  let law := fun l => FiniteProbabilityWeights.uniform (V → ZMod (q l))
  let Y : ∀ l, (V → ZMod (q l)) → (∀ j, J j → ZMod (q l)) :=
    fun l x j i => eval₂ (Int.castRingHom (ZMod (q l)))
      (fun v => r l v + (p l : ZMod (q l)) ^ e l * x v) (F j i)
  let cap : L → ℝ := fun l => ((p l ^ (b l + e l) : ℕ) : ℝ)
  have hkill : ∀ l (z : ∀ j, J j → ZMod (q l)), q l • z = 0 := by
    intro l z
    ext j i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hlocal (l : L) (ψ : AddChar (∀ j, J j → ZMod (q l)) ℂ) :
      ‖finiteImageCharacteristic (law l) (Y l) ψ‖ ≤
        cap l ^ (modularRankDecayExponent s C * modularRankChargeFactor s) *
          (orderOf ψ : ℝ) ^ (-modularRankDecayExponent s C) := by
    have hFl : ∀ j i, (map (Int.castRingHom (ZMod (p l ^ A l))) (F j i)).totalDegree ≤
        j.val + 1 := by
      intro j i
      apply le_trans _ (hF j i)
      exact Finset.sup_mono (support_map_subset _ _)
    have h := primePower_polynomial_image_characteristic_decay hs (p l) (A l) (b l) (e l)
      (hp l) C hC (fun j i => map (Int.castRingHom (ZMod (p l ^ A l))) (F j i))
      hFl (by
        intro B hbB hBA j row hunit
        rw [primePowerHomogeneousRankProbability_integerPolynomial]
        exact hrank l B hbB hBA j row hunit) (r l) ψ
    simpa only [eval_map, law, Y, cap, q] using h
  have hglobal := finiteImageCharacteristic_crt_decay E law Y q hkill hq cap
    (modularRankDecayExponent s C * modularRankChargeFactor s)
    (modularRankDecayExponent s C) (fun l => Nat.cast_nonneg _) hlocal χ
  have houtput : (fun x : ∀ l, V → ZMod (q l) => E.symm (fun l => Y l (x l))) =
      (fun x j i => eval₂ (Int.castRingHom (ZMod (∏ l, p l ^ A l)))
        (crtInput (fun l => p l ^ A l) hq
          (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)) (F j i)) := by
    funext x
    exact taggedOutputCRTEquiv_symm_integerPolynomial_eval J q hq F
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)
  rw [houtput] at hglobal
  exact hglobal

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtPrimePowerPolynomialLaw (p A : L → ℕ) [∀ l, NeZero (p l)] :
    FiniteProbabilityWeights (∀ l, V → ZMod (p l ^ A l)) :=
  FiniteProbabilityWeights.pi (fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))

noncomputable def crtPrimePowerPolynomialMap {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Fin s) (i : J j) : ZMod (∏ l, p l ^ A l) :=
  eval₂ (Int.castRingHom (ZMod (∏ l, p l ^ A l)))
    (crtInput (fun l => p l ^ A l) hq
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)) (F j i)

noncomputable def crtPolynomialCharge (p b e : L → ℕ) (s : ℕ) (C : ℝ) : ℝ :=
  (∏ l, ((p l ^ (b l + e l) : ℕ) : ℝ)) ^
    (modularRankDecayExponent s C * modularRankChargeFactor s)

theorem crt_integer_polynomial_density_order_bounds
    {s : ℕ} (hs : 0 < s) {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A b e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (l : L) (B : ℕ), b l < B → B ≤ A l → ∀ (j : Fin s)
      (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability (p l) B j.val (F j) row ≤ (p l : ℝ) ^ (-C * B))
    (r : ∀ l, V → ZMod (p l ^ A l)) (T : ℕ) (hT : 0 < T) :
    letI : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    let law := crtPrimePowerPolynomialLaw (V := V) p A
    let Y := crtPrimePowerPolynomialMap p A e (primePower_crt_coprime p A hp hinj) F r
    let cap := crtPolynomialCharge p b e s C
    let S := Finset.univ.filter
      (fun χ : AddChar (∀ j, J j → ZMod (∏ l, p l ^ A l)) ℂ => orderOf χ ≤ T)
    (∀ z, (Fintype.card (∀ j, J j → ZMod (∏ l, p l ^ A l)) : ℝ) *
      finiteImageMass law Y z ≤ 1 + cap) ∧
    S.card ≤ T ^ (Fintype.card (Sigma J) + 1) ∧
    (∑ χ ∈ S, ‖finiteImageCharacteristic law Y χ‖) ≤
      (T : ℝ) ^ (Fintype.card (Sigma J) + 1) ∧
    ∀ z, ‖(Fintype.card (∀ j, J j → ZMod (∏ l, p l ^ A l)) : ℂ) * finiteImageMass law Y z -
      ∑ χ ∈ S, finiteImageCharacteristic law Y χ * star (χ z)‖ ≤ cap / T := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  dsimp only
  have hcap : 0 ≤ crtPolynomialCharge p b e s C :=
    Real.rpow_nonneg (Finset.prod_nonneg (fun l _ => Nat.cast_nonneg _)) _
  have hdecay (χ : AddChar (∀ j, J j → ZMod (∏ l, p l ^ A l)) ℂ) :=
    crt_integer_polynomial_characteristic_decay hs p A b e hp hinj C hC F hF hrank r χ
  have h := taggedZModImage_order_bounds J (∏ l, p l ^ A l)
    (crtPrimePowerPolynomialLaw (V := V) p A)
    (crtPrimePowerPolynomialMap p A e (primePower_crt_coprime p A hp hinj) F r)
    hcap hP hdecay T hT
  dsimp only at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card] using h.1
  · exact h.2.1
  · exact h.2.2.1
  · simpa only [← Nat.card_eq_fintype_card] using h.2.2.2

end Erdos3


namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_not_bad {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) {a : ℕ}
    (ha : largestTestedBadDepth A bad p x < a) (hA : a ≤ A p) : ¬ bad p a x := by
  intro hbad
  have hmem : a ∈ (Finset.Icc 1 (A p)).filter (fun a => bad p a x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hA⟩, hbad⟩
  exact (not_le_of_gt ha) (Finset.le_sup (f := id) hmem)

theorem crtPolynomialCharge_le_of_bad_product {L : Type*} [Fintype L]
    (p b e : L → ℕ) (s : ℕ) {C : ℝ} (hC : 0 ≤ C) {R : ℕ}
    (hbad : (∏ l, p l ^ b l) ≤ R) :
    crtPolynomialCharge p b e s C ≤
      ((R * ∏ l, p l ^ e l : ℕ) : ℝ) ^
        (modularRankDecayExponent s C * modularRankChargeFactor s) := by
  have hP : 0 ≤ modularRankDecayExponent s C := by
    unfold modularRankDecayExponent
    positivity
  unfold crtPolynomialCharge
  apply Real.rpow_le_rpow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) ?_
    (mul_nonneg hP (Nat.cast_nonneg _))
  rw [← Nat.cast_prod]
  exact_mod_cast (show (∏ l, p l ^ (b l + e l)) ≤ R * ∏ l, p l ^ e l from by
    simp_rw [pow_add]
    rw [Finset.prod_mul_distrib]
    exact Nat.mul_le_mul_right _ hbad)

end Erdos3

end OAI
