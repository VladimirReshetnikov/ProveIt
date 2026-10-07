/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Geometry.MultilinearBoxInverse
import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
import OAI.Combinatorics.Progressions.Polynomial.DiagonalTensorPolynomial

namespace OAI

section

namespace Erdos3

noncomputable def polynomialTopSymbolMultilinear {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    MultilinearMap ℝ (fun _ : Fin n => I → ℝ) ℝ :=
  (MvPolynomial.aeval (fun _ : I => (0 : ℝ))).toLinearMap.compMultilinearMap
    (polynomialIterDifferenceMultilinear n P hP)

theorem polynomialTopSymbolMultilinear_apply {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u : Fin n → I → ℝ) :
    polynomialTopSymbolMultilinear n P hP u = polynomialTopSymbol n P u := by
  change MvPolynomial.eval (fun _ => 0) (polynomialIterDifference n P u) = _
  exact polynomialIterDifference_topSymbol n P hP u _

theorem polynomialTopSymbol_update_add {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u : Fin n → I → ℝ) (j : Fin n) (a b : I → ℝ) :
    polynomialTopSymbol n P (Function.update u j (a + b)) =
      polynomialTopSymbol n P (Function.update u j a) +
        polynomialTopSymbol n P (Function.update u j b) := by
  simpa only [polynomialTopSymbolMultilinear_apply] using
    (polynomialTopSymbolMultilinear n P hP).map_update_add u j a b

theorem polynomialTopSymbol_update_smul {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u : Fin n → I → ℝ) (j : Fin n) (c : ℝ) (a : I → ℝ) :
    polynomialTopSymbol n P (Function.update u j (c • a)) =
      c * polynomialTopSymbol n P (Function.update u j a) := by
  simpa only [polynomialTopSymbolMultilinear_apply, smul_eq_mul] using
    (polynomialTopSymbolMultilinear n P hP).map_update_smul u j c a

end Erdos3

end

section

namespace Erdos3

noncomputable def rowDirectionLinear {K I : Type*} (a : K → ℝ) :
    (I → ℝ) →ₗ[ℝ] ((K × I) → ℝ) :=
  LinearMap.pi (fun z => a z.1 • LinearMap.proj z.2)

theorem rowDirectionLinear_apply {K I : Type*} (a : K → ℝ) (u : I → ℝ) (z : K × I) :
    rowDirectionLinear a u z = a z.1 * u z.2 := rfl

noncomputable def rowTopSymbolMultilinear {K I : Type*} [Fintype K] [Fintype I]
    (n : ℕ) (P : MvPolynomial (K × I) ℝ) (hP : P.totalDegree ≤ n) (a : Fin n → K → ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => I → ℝ) ℝ :=
  (polynomialTopSymbolMultilinear n P hP).compLinearMap (fun i => rowDirectionLinear (a i))

theorem rowTopSymbolMultilinear_apply {K I : Type*} [Fintype K] [Fintype I]
    (n : ℕ) (P : MvPolynomial (K × I) ℝ) (hP : P.totalDegree ≤ n)
    (a : Fin n → K → ℝ) (u : Fin n → I → ℝ) :
    rowTopSymbolMultilinear n P hP a u =
      polynomialTopSymbol n P (fun i z => a i z.1 * u i z.2) := by
  change polynomialTopSymbolMultilinear n P hP (fun i => rowDirectionLinear (a i) (u i)) = _
  rw [polynomialTopSymbolMultilinear_apply]
  rfl

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem paired_multilinear_common_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ a : (Fin (n + 1) → I) → ℤ, ∀ j,
        |F (fun i => Pi.single (j i) (1 : ℝ)) - (a j : ℝ) / D| ≤
          multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  exact exists_common_rational_approximations_varying (I := Fin (n + 1) → I)
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ)))
    (fun j : Fin (n + 1) → I => multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ))
    (fun j : Fin (n + 1) → I =>
      multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)))
    (fun j : Fin (n + 1) → I =>
      paired_multilinear_box_coordinate_approximation F N s hs hζ hN hbias j)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem row_top_common_approximation {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    {n : ℕ} (P : MvPolynomial (K × I) ℝ) (hP : P.totalDegree ≤ n + 1)
    (a : Fin (n + 1) → K → ℝ) (N s : I → ℕ) (hs : ∀ k, 0 < s k)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((polynomialTopSymbol (n + 1) P (fun i z => a i z.1 *
          ((s z.2 : ℝ) * ((x i z.2).val : ℝ) - (s z.2 : ℝ) * ((y i z.2).val : ℝ))) : ℝ) :
            CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ m : (Fin (n + 1) → I) → ℤ, ∀ j,
        |polynomialTopSymbol (n + 1) P
          (fun i z => a i z.1 * (Pi.single (j i) (1 : ℝ) : I → ℝ) z.2) - (m j : ℝ) / D| ≤
          multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  let F := rowTopSymbolMultilinear (n + 1) P hP a
  have hb : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
    simpa only [F, rowTopSymbolMultilinear_apply] using hbias
  have h := paired_multilinear_common_approximation F N s hs hζ hN hb
  simpa only [F, rowTopSymbolMultilinear_apply] using h

theorem tensorDenominatorBound_le {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I]
    {B S : ℝ} (hB : 0 ≤ B) (s : I → ℝ) (hs : ∀ i, 0 ≤ s i) (hS : ∀ i, s i ≤ S) :
    (∏ j : H → I, (B * ∏ i, s (j i))) ≤ (B * S ^ Fintype.card H) ^ (Fintype.card I ^ Fintype.card H) := by
  have hj (j : H → I) : (∏ i, s (j i)) ≤ S ^ Fintype.card H := by
    calc
      (∏ i, s (j i)) ≤ ∏ _i : H, S := Finset.prod_le_prod₀ (fun i _ => hs (j i)) (fun i _ => hS (j i))
      _ = S ^ Fintype.card H := by simp
  calc
    (∏ j : H → I, (B * ∏ i, s (j i))) ≤ ∏ _j : H → I, (B * S ^ Fintype.card H) :=
      Finset.prod_le_prod₀ (fun j _ => mul_nonneg hB (Finset.prod_nonneg (fun i _ => hs (j i))))
        (fun j _ => mul_le_mul_of_nonneg_left (hj j) hB)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDiagonalPolynomial_coeff_bound {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    {B : ℝ} (hB : 0 ≤ B) (hθ : ∀ j, |θ j| ≤ B / ∏ i, T (j i))
    (α : I →₀ ℕ) :
    |(tensorDiagonalPolynomial θ).coeff α| ≤
      (Fintype.card I : ℝ) ^ h * B / monomialScale T α := by
  rw [tensorDiagonalPolynomial_eq_sum_monomial]
  simp only [MvPolynomial.coeff_sum]
  have hj (j : Fin h → I) :
      |(MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| ≤
        B / monomialScale T α := by
    by_cases he : productBlockExponent j = α
    · simpa [he, ← monomialScale_productBlockExponent j T] using hθ j
    · simp only [MvPolynomial.coeff_monomial, he, ite_false, abs_zero]
      exact div_nonneg hB (monomialScale_pos T hT α).le
  calc
    |∑ j : Fin h → I, (MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| ≤
        ∑ j : Fin h → I, |(MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin h → I, B / monomialScale T α := Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp [mul_div_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDiagonalPolynomial_rational_split {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (m : (Fin h → I) → ℤ) (D : ℕ) :
    tensorDiagonalPolynomial θ = tensorDiagonalPolynomial (fun j => θ j - (m j : ℝ) / D) +
      MvPolynomial.C (1 / (D : ℝ)) *
        MvPolynomial.map (Int.castRingHom ℝ) (tensorDiagonalPolynomial m) := by
  rw [tensorDiagonalPolynomial_map, ← tensorDiagonalPolynomial_mul, ← tensorDiagonalPolynomial_add]
  congr 1
  funext j
  simp only [Int.coe_castRingHom, div_eq_mul_inv]
  ring

theorem tensorDiagonalPolynomial_approximation {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (m : (Fin h → I) → ℤ) (D : ℕ)
    (T : I → ℝ) (hT : ∀ i, 0 < T i) {B : ℝ} (hB : 0 ≤ B)
    (hθ : ∀ j, |θ j - (m j : ℝ) / D| ≤ B / ∏ i, T (j i)) :
    ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
      tensorDiagonalPolynomial θ = E + MvPolynomial.C (1 / (D : ℝ)) *
        MvPolynomial.map (Int.castRingHom ℝ) Q ∧
      ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ h * B / monomialScale T α := by
  exact ⟨tensorDiagonalPolynomial (fun j => θ j - (m j : ℝ) / D),
    tensorDiagonalPolynomial m, tensorDiagonalPolynomial_rational_split θ m D,
    tensorDiagonalPolynomial_coeff_bound _ T hT hB hθ⟩

theorem integerPolynomialQuotient_coeff {I : Type*} (D : ℕ) (Q : MvPolynomial I ℤ)
    (α : I →₀ ℕ) :
    (MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q).coeff α =
      ((Q.coeff α : ℤ) : ℝ) / D := by
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Int.coe_castRingHom, div_eq_mul_inv]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensor_product_scale_le {I : Type*} {h : ℕ} (T H : I → ℝ)
    (hH : ∀ i, 0 ≤ H i) {A : ℝ} (hscale : ∀ i, H i ≤ A * T i)
    (j : Fin h → I) :
    (∏ i, H (j i)) ≤ A ^ h * ∏ i, T (j i) := by
  calc
    (∏ i, H (j i)) ≤ ∏ i, (A * T (j i)) :=
      Finset.prod_le_prod₀ (fun i _ => hH (j i)) (fun i _ => hscale (j i))
    _ = _ := by simp [Finset.prod_mul_distrib]

theorem tensor_entry_bound_rescale {I : Type*} {h : ℕ}
    (f : (Fin h → I) → ℝ) (T H : I → ℝ)
    (hT : ∀ i, 0 < T i) (hH : ∀ i, 0 < H i) {A B : ℝ}
    (hscale : ∀ i, H i ≤ A * T i) (hB : 0 ≤ B)
    (hf : ∀ j, |f j| ≤ B / ∏ i, T (j i)) :
    ∀ j, |f j| ≤ (A ^ h * B) / ∏ i, H (j i) := by
  intro j
  apply (hf j).trans
  apply (div_le_div_iff₀ (Finset.prod_pos (fun i _ => hT (j i)))
    (Finset.prod_pos (fun i _ => hH (j i)))).mpr
  calc
    B * ∏ i, H (j i) ≤ B * (A ^ h * ∏ i, T (j i)) :=
      mul_le_mul_of_nonneg_left (tensor_product_scale_le T H (fun i => (hH i).le) hscale j) hB
    _ = (A ^ h * B) * ∏ i, T (j i) := by ring

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem paired_multilinear_polynomial_approximation {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (P : MvPolynomial I ℝ) (hP : ∀ w, MvPolynomial.eval w P = F (fun _ => w))
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
        P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ (n + 1) *
          (A ^ (n + 1) * multiaffineBiasBudget n ζ) / monomialScale H α := by
  obtain ⟨D, hD, hDb, m, hm⟩ := paired_multilinear_common_approximation F N s hs hζ hN hbias
  have hT (k : I) : 0 < (s k : ℝ) * (N k : ℝ) := by
    exact mul_pos (Nat.cast_pos.mpr (hs k)) ((multiaffineBiasBudget_pos n hζ).trans_le (hN k))
  have hmH := tensor_entry_bound_rescale
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ)) - (m j : ℝ) / D)
    (fun k => (s k : ℝ) * (N k : ℝ)) H hT hH hscale (multiaffineBiasBudget_pos n hζ).le hm
  obtain ⟨E, Q, hE, hcoeff⟩ := tensorDiagonalPolynomial_approximation
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ))) m D
    H hH (mul_nonneg (pow_nonneg hA _) (multiaffineBiasBudget_pos n hζ).le) hmH
  have he : P = tensorDiagonalPolynomial
      (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ))) := by
    apply MvPolynomial.funext
    intro w
    rw [hP, tensorDiagonalPolynomial_multilinear_eval]
  exact ⟨D, hD, hDb, E, Q, he.trans hE, hcoeff⟩

end Erdos3

end

end OAI
