import GowersSzemeredi.Proofs17PhaseRemoval

/-!
# Minkowski's inequality for the Gowers norm

This module proves Lemma 3.9.  Expanding the cube form of `f + g` gives one
mixed cube form for every Boolean choice of `f` or `g` at each vertex.
Gowers--Cauchy--Schwarz bounds each mixed term, and the resulting sum is the
binomial expansion of the required power.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def minkowskiChoice {N d : Nat} (f g : ZMod N → Complex)
    (h : (Fin d → Bool) → Bool) :
    (Fin d → Bool) → ZMod N → Complex :=
  fun e => if h e then f else g

private lemma parityConj_add {d : Nat} (e : Fin d → Bool) (z w : Complex) :
    parityConj e (z + w) = parityConj e z + parityConj e w := by
  unfold parityConj
  split <;> simp

private lemma minkowski_vertex_expansion {N d : Nat}
    (f g : ZMod N → Complex) (x : Point N d) (s : ZMod N) :
    (∏ e : Fin d → Bool,
        parityConj e ((f + g) (cubeArgument s x e))) =
      ∑ h : (Fin d → Bool) → Bool,
        ∏ e : Fin d → Bool,
          parityConj e
            (minkowskiChoice f g h e (cubeArgument s x e)) := by
  let A : (e : Fin d → Bool) → Bool → Complex := fun e b =>
    parityConj e ((if b then f else g) (cubeArgument s x e))
  calc
    (∏ e : Fin d → Bool,
        parityConj e ((f + g) (cubeArgument s x e))) =
        ∏ e : Fin d → Bool, ∑ b : Bool, A e b := by
      apply Finset.prod_congr rfl
      intro e _
      rw [Fintype.sum_bool]
      simp [A, parityConj_add]
    _ = ∑ h : (Fin d → Bool) → Bool,
        ∏ e : Fin d → Bool, A e (h e) := Fintype.prod_sum A
    _ = ∑ h : (Fin d → Bool) → Bool,
        ∏ e : Fin d → Bool,
          parityConj e
            (minkowskiChoice f g h e (cubeArgument s x e)) := by
      rfl

private lemma minkowski_cubeForm_expansion {N d : Nat} [NeZero N]
    (f g : ZMod N → Complex) :
    cubeForm (d := d) (fun (_ : Fin d → Bool) => f + g) =
      ∑ h : (Fin d → Bool) → Bool, cubeForm (minkowskiChoice f g h) := by
  calc
    cubeForm (d := d) (fun (_ : Fin d → Bool) => f + g) =
        ∑ x : Point N d, ∑ s : ZMod N,
          ∑ h : (Fin d → Bool) → Bool,
            ∏ e : Fin d → Bool,
              parityConj e
                (minkowskiChoice f g h e (cubeArgument s x e)) := by
      unfold cubeForm
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro s _
      exact minkowski_vertex_expansion f g x s
    _ = ∑ x : Point N d, ∑ h : (Fin d → Bool) → Bool,
        ∑ s : ZMod N,
          ∏ e : Fin d → Bool,
            parityConj e
              (minkowskiChoice f g h e (cubeArgument s x e)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ h : (Fin d → Bool) → Bool, ∑ x : Point N d,
        ∑ s : ZMod N,
          ∏ e : Fin d → Bool,
            parityConj e
              (minkowskiChoice f g h e (cubeArgument s x e)) := by
      rw [Finset.sum_comm]
    _ = ∑ h : (Fin d → Bool) → Bool,
        cubeForm (minkowskiChoice f g h) := by rfl

private lemma minkowski_binomial_sum {N d : Nat} [NeZero N]
    (f g : ZMod N → Complex) :
    (∑ h : (Fin d → Bool) → Bool,
        ∏ e : Fin d → Bool,
          ‖cubeForm (d := d)
            (fun (_ : Fin d → Bool) => minkowskiChoice f g h e)‖ ^
              ((1 : Real) / (2 : Real) ^ d)) =
      (gowersNorm d f + gowersNorm d g) ^ ((2 : Nat) ^ d) := by
  let A : Real := gowersNorm d f
  let B : Real := gowersNorm d g
  let C : (Fin d → Bool) → Bool → Real := fun _ b => if b then A else B
  calc
    (∑ h : (Fin d → Bool) → Bool,
        ∏ e : Fin d → Bool,
          ‖cubeForm (d := d)
            (fun (_ : Fin d → Bool) => minkowskiChoice f g h e)‖ ^
              ((1 : Real) / (2 : Real) ^ d)) =
        ∑ h : (Fin d → Bool) → Bool,
          ∏ e : Fin d → Bool, C e (h e) := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : h e <;>
        simp [C, A, B, minkowskiChoice, gowersNorm, he,
          constant_cubeForm_eq_sum_cubeDifference]
    _ = ∏ e : Fin d → Bool, ∑ b : Bool, C e b :=
      (Fintype.prod_sum C).symm
    _ = ∏ _e : Fin d → Bool, (A + B) := by
      apply Finset.prod_congr rfl
      intro e _
      rw [Fintype.sum_bool]
      simp [C]
    _ = (A + B) ^ ((2 : Nat) ^ d) := by
      rw [Finset.prod_const]
      simp [Fintype.card_fin, Fintype.card_bool]
    _ = (gowersNorm d f + gowersNorm d g) ^ ((2 : Nat) ^ d) := by rfl

/-- **Gowers, Lemma 3.9.** The Gowers norm satisfies Minkowski's
inequality. -/
theorem lemma_3_9_holds : lemma_3_9 := by
  intro N d _ _hd f g
  let A : Real := gowersNorm d f
  let B : Real := gowersNorm d g
  let m : Nat := (2 : Nat) ^ d
  have hA : 0 ≤ A := Real.rpow_nonneg (norm_nonneg _) _
  have hB : 0 ≤ B := Real.rpow_nonneg (norm_nonneg _) _
  have hm : m ≠ 0 := by positivity
  have hnorm :
      ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f + g)‖ ≤
        (A + B) ^ m := by
    calc
      ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f + g)‖ =
          ‖∑ h : (Fin d → Bool) → Bool,
            cubeForm (minkowskiChoice f g h)‖ := by
        rw [minkowski_cubeForm_expansion]
      _ ≤ ∑ h : (Fin d → Bool) → Bool,
          ‖cubeForm (minkowskiChoice f g h)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ h : (Fin d → Bool) → Bool,
          ∏ e : Fin d → Bool,
            ‖cubeForm (d := d)
              (fun (_ : Fin d → Bool) => minkowskiChoice f g h e)‖ ^
                ((1 : Real) / (2 : Real) ^ d) := by
        apply Finset.sum_le_sum
        intro h _
        exact gowers_cauchy_schwarz (minkowskiChoice f g h)
      _ = (gowersNorm d f + gowersNorm d g) ^ ((2 : Nat) ^ d) :=
        minkowski_binomial_sum f g
      _ = (A + B) ^ m := by rfl
  change ‖∑ x : Point N d, ∑ s : ZMod N, cubeDifference (f + g) x s‖ ^
      ((1 : Real) / (2 : Real) ^ d) ≤ A + B
  rw [← constant_cubeForm_eq_sum_cubeDifference]
  rw [show ((1 : Real) / (2 : Real) ^ d) = (m : Real)⁻¹ by
    simp only [m, one_div, Nat.cast_pow, Nat.cast_ofNat]]
  apply le_of_pow_le_pow_left₀ hm (add_nonneg hA hB)
  rw [Real.rpow_inv_natCast_pow (norm_nonneg _) hm]
  exact hnorm

end LeanProofs.GowersSzemeredi
