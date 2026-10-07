import OAI.Combinatorics.Progressions.Estimates.PeriodicIsometricAction

namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [PseudoMetricSpace X]

def Commutes (A B : IsometricCircleAction X) : Prop :=
  ∀ t u x, A.act t (B.act u x) = B.act u (A.act t x)

theorem Commutes.symm {A B : IsometricCircleAction X} (h : A.Commutes B) : B.Commutes A :=
  fun t u x => (h u t x).symm

theorem component_equivariant (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    {f : X → ℂ} (g : X → X) (z : ℂ)
    (hg : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.component N h f (g x) = z * A.component N h f x := by
  unfold component fejerComponent circleFourierComponent
  change (fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
    z * ((fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar))
  have heq : (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
      z * (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hg, hf]
    ring
  rw [heq]
  ring

theorem component_preserves_character (A B : IsometricCircleAction X) (hAB : A.Commutes B)
    (N : ℕ) (h n : ℤ) {f : X → ℂ}
    (hf : ∀ t x, f (B.act t x) = character (n • t) * f x) (t : Circle) (x : X) :
    A.component N h f (B.act t x) = character (n • t) * A.component N h f x :=
  A.component_equivariant N h (B.act t) (character (n • t)) (fun u x => hAB u t x) (hf t) x

theorem component_sum {ι : Type*} (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    (s : Finset ι) (f : ι → X → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (x : X) :
    A.component N h (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, A.component N h (f i) x := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  unfold component fejerComponent circleFourierComponent
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.mul_sum s _ _
  · intro i hi
    exact integrable_circleFourierComponent (-h) (hf i hi) x

end Erdos3.CircleFourier.IsometricCircleAction

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [AddAction (ι → Circle) X] [ContinuousVAdd (ι → Circle) X]

def torusCoordinateAction (hact : ∀ t : ι → Circle, Isometry (fun x : X => t +ᵥ x))
    (i : ι) : IsometricCircleAction X where
  act t x := (Pi.single i t : ι → Circle) +ᵥ x
  zero_act x := by simp
  add_act t u x := by simp only [Pi.single_add, add_vadd]
  continuous_act := by
    have hs : Continuous (fun p : Circle × X => (Pi.single i p.1 : ι → Circle)) := by
      apply continuous_pi
      intro j
      by_cases h : j = i
      · subst j
        simpa only [Pi.single_eq_same] using (continuous_fst : Continuous (fun p : Circle × X => p.1))
      · simpa only [Pi.single_eq_of_ne h] using
          (continuous_const : Continuous (fun _p : Circle × X => (0 : Circle)))
    exact hs.vadd continuous_snd
  isometry_act t := hact (Pi.single i t)

omit [Fintype ι] in
theorem torusCoordinateAction_commutes
    (hact : ∀ t : ι → Circle, Isometry (fun x : X => t +ᵥ x)) (i j : ι) :
    (torusCoordinateAction hact i).Commutes (torusCoordinateAction hact j) := by
  intro t u x
  change (Pi.single i t : ι → Circle) +ᵥ ((Pi.single j u : ι → Circle) +ᵥ x) =
    (Pi.single j u : ι → Circle) +ᵥ ((Pi.single i t : ι → Circle) +ᵥ x)
  rw [← add_vadd, ← add_vadd, add_comm]

omit [PseudoMetricSpace X] [ContinuousVAdd (ι → Circle) X] in

theorem torus_character_of_coordinate_characters (f : X → ℂ) (n : ι → ℤ)
    (hf : ∀ (i : ι) (t : Circle) x,
      f ((Pi.single i t : ι → Circle) +ᵥ x) = character (n i • t) * f x)
    (t : ι → Circle) (x : X) :
    f (t +ᵥ x) = (∏ i, character (n i • t i)) * f x := by
  have hs (s : Finset ι) : ∀ x, f ((∑ i ∈ s, Pi.single i (t i) : ι → Circle) +ᵥ x) =
      (∏ i ∈ s, character (n i • t i)) * f x := by
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | @insert i s hi ih =>
      intro x
      rw [Finset.sum_insert hi, add_vadd, hf, ih, Finset.prod_insert hi, mul_assoc]
  simpa only [Finset.univ_sum_single] using hs Finset.univ x

end Erdos3.CircleFourier

end

end OAI
