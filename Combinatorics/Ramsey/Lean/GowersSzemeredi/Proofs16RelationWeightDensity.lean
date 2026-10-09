import GowersSzemeredi.Proofs16BohrSizeFactorization

/-! The relation weight is close to a real number in [0,1]. This supplies
the bounded density factor that is not explicit in the factorization lemma. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A relation weight is within the truncation error of a real density.
No annulus regularity hypothesis is needed for this fact. -/
theorem relationWeightMixed_near_density {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (gamma : ι → ZMod N) (a : ι → Nat) {c R : Nat}
    (ha : ∀ i, 2 * a i < N) (hc : 2 * c < N) {epsilon : Real}
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ epsilon) :
    ∃ delta : Real, 0 ≤ delta ∧ delta ≤ 1 ∧
      ‖relationWeightMixed gamma a c R - (delta : Complex)‖ ≤ epsilon := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hNC : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
  let P : Real := ∑ x : ZMod N, ∏ i, trapezoid (a i) c (gamma i * x)
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun x _ =>
    Finset.prod_nonneg fun i _ => trapezoid_nonneg _ _ _
  have hP1 : P ≤ N := by
    calc
      _ ≤ ∑ _x : ZMod N, (1 : Real) := Finset.sum_le_sum fun x _ =>
        Finset.prod_le_one (fun i _ => trapezoid_nonneg _ _ _) (fun i _ => trapezoid_le_one _ _ _)
      _ = _ := by simp
  refine ⟨P / N, div_nonneg hP0 hN.le, (div_le_one hN).mpr hP1, ?_⟩
  have hsum : ∑ x : ZMod N, boundedCharacterProduct gamma R
      (fun i r => trapezoidRelationCoeff (a i) c (r : ZMod N)) x =
      (N : Complex) * relationWeightMixed gamma a c R := by
    rw [sum_boundedCharacterProduct]
    rfl
  have hcast : (P : Complex) =
      ∑ x : ZMod N, ((∏ i, trapezoid (a i) c (gamma i * x) : Real) : Complex) := by
    simp only [P, Complex.ofReal_sum]
  have herror : ‖(P : Complex) - (N : Complex) * relationWeightMixed gamma a c R‖ ≤ epsilon * N := by
    rw [← hsum, hcast, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x : ZMod N, ‖((∏ i, trapezoid (a i) c (gamma i * x) : Real) : Complex) -
          boundedCharacterProduct gamma R
            (fun i r => trapezoidRelationCoeff (a i) c (r : ZMod N)) x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ZMod N, epsilon := Finset.sum_le_sum fun x _ =>
        (trapezoid_mixed_uniform_truncation gamma a ha hc R x).trans htrunc
      _ = _ := by simp; ring
  have heq : (N : Complex) * (relationWeightMixed gamma a c R - ((P / N : Real) : Complex)) =
      (N : Complex) * relationWeightMixed gamma a c R - P := by
    push_cast
    field_simp [hNC]
  rw [norm_sub_rev, ← heq, norm_mul, Complex.norm_natCast] at herror
  exact (mul_le_mul_iff_right₀ hN).mp (by nlinarith only [herror])

/-- Splitting with the fixed block identifies the common relation class
with the relations of the varying block, by setting the fixed coefficients to zero. -/
theorem latticeWeightMixed_eq_relationWeight_of_split {N : Nat} [NeZero N]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (gamma : ι → ZMod N) (ell : κ → ZMod N) (b : κ → Nat) (c R : Nat)
    (Lambda : Set (κ → centeredBall N R))
    (hsplit : ∀ (nu : ι → centeredBall N R) (mu : κ → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * ell j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ mu ∈ Lambda)) :
    latticeWeightMixed b c R Lambda = relationWeightMixed ell b c R := by
  have hzero : (0 : ZMod N) ∈ centeredBall N R := by simp [centeredBall, centeredAbs]
  have hrel (mu : κ → centeredBall N R) : mu ∈ Lambda ↔ ∑ j, (mu j : ZMod N) * ell j = 0 := by
    have h := hsplit (fun _ => ⟨0, hzero⟩) mu
    simpa using h.symm
  unfold latticeWeightMixed relationWeightMixed
  simp only [hrel]

/-- The common relation weight has a genuine approximate density whenever
one splitting tuple exists. -/
theorem latticeWeightMixed_near_density_of_split {N : Nat} [NeZero N]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (gamma : ι → ZMod N) (ell : κ → ZMod N) (b : κ → Nat) {c R : Nat}
    (hb : ∀ j, 2 * b j < N) (hc : 2 * c < N)
    (Lambda : Set (κ → centeredBall N R))
    (hsplit : ∀ (nu : ι → centeredBall N R) (mu : κ → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * ell j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ mu ∈ Lambda))
    {epsilon : Real}
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card κ - 1 ≤ epsilon) :
    ∃ delta : Real, 0 ≤ delta ∧ delta ≤ 1 ∧
      ‖latticeWeightMixed b c R Lambda - (delta : Complex)‖ ≤ epsilon := by
  rw [latticeWeightMixed_eq_relationWeight_of_split gamma ell b c R Lambda hsplit]
  exact relationWeightMixed_near_density ell b hb hc htrunc

end LeanProofs.GowersSzemeredi
