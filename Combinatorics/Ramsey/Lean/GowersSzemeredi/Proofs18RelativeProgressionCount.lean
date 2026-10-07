import GowersSzemeredi.Proofs03FourFactorSymmetry
import GowersSzemeredi.Proofs18RelativeBalance

/-! Counting four-term progressions relative to a support, using uniformity
of 1_A - delta 1_S rather than ambient density. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The four-factor telescoping identity, retaining the support function in
each preceding position. -/
theorem fourFactor_telescoping {N : Nat} [NeZero N] (f g : ZMod N → Complex) :
    progressionAverage (fun _ : Fin 4 => f) - progressionAverage (fun _ : Fin 4 => g) =
      progressionAverage ![f - g, f, f, f] +
      progressionAverage ![g, f - g, f, f] +
      progressionAverage ![g, g, f - g, f] +
      progressionAverage ![g, g, g, f - g] := by
  unfold progressionAverage
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Pi.sub_apply]
  ring

/-- Replacing a bounded function by another costs at most four von Neumann
errors when their difference is quadratic-uniform. -/
theorem fourFactor_counting_bound {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (f g : ZMod N → Complex)
    (hf : DiscValued f) (hg : DiscValued g) (hh : DiscValued (f - g))
    (alpha : Real) (hα : 0 ≤ alpha) (hu : UniformOfDegree (f - g) alpha 2) :
    ‖progressionAverage (fun _ : Fin 4 => f) - progressionAverage (fun _ : Fin 4 => g)‖ ≤
      4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 := by
  let a := progressionAverage ![f - g, f, f, f]
  let b := progressionAverage ![g, f - g, f, f]
  let c := progressionAverage ![g, g, f - g, f]
  let d := progressionAverage ![g, g, g, f - g]
  have ha := fourFactor_uniform_bound hN ![f - g, f, f, f]
    (by intro i; fin_cases i <;> first | exact hf | exact hg | exact hh) alpha hα 0 hu
  have hb := fourFactor_uniform_bound hN ![g, f - g, f, f]
    (by intro i; fin_cases i <;> first | exact hf | exact hg | exact hh) alpha hα 1 hu
  have hc := fourFactor_uniform_bound hN ![g, g, f - g, f]
    (by intro i; fin_cases i <;> first | exact hf | exact hg | exact hh) alpha hα 2 hu
  have hd := fourFactor_uniform_bound hN ![g, g, g, f - g]
    (by intro i; fin_cases i <;> first | exact hf | exact hg | exact hh) alpha hα 3 hu
  have htriangle : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    linarith [norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]
  rw [fourFactor_telescoping]
  change ‖a + b + c + d‖ ≤ _
  calc
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := htriangle
    _ ≤ _ := by dsimp [a, b, c, d]; linarith

theorem progressionAverage_const_mul {N k : Nat} [NeZero N]
    (f : Fin k → ZMod N → Complex) (c : Complex) :
    progressionAverage (fun i x => c * f i x) = c ^ k * progressionAverage f := by
  unfold progressionAverage
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.mul_sum]

/-- Relative uniformity compares the actual count to the count in the
support, scaled by the fourth power of its relative density. -/
theorem relative_fourFactor_counting_bound {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha 2) :
    ‖progressionAverage (fun _ : Fin 4 => indicator A) -
        (delta : Complex) ^ 4 * progressionAverage (fun _ : Fin 4 => indicator S)‖ ≤
      4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 := by
  classical
  have hf : DiscValued (indicator A) := by
    intro x
    by_cases hx : x ∈ A <;> simp [indicator, hx]
  have hg : DiscValued (fun x => (delta : Complex) * indicator S x) := by
    intro x
    by_cases hx : x ∈ S
    · simpa [indicator, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ] using hδone
    · simp [indicator, hx]
  have heq : indicator A - (fun x => (delta : Complex) * indicator S x) =
      relativeBalanced A S delta := by
    funext x
    exact (relativeBalanced_eq_indicators A S delta x).symm
  have h := fourFactor_counting_bound hN (indicator A) (fun x => (delta : Complex) * indicator S x)
    hf hg (heq ▸ relativeBalanced_discValued A S delta hAS hδ hδone) alpha hα (heq ▸ hu)
  rwa [progressionAverage_const_mul] at h

end LeanProofs.GowersSzemeredi
