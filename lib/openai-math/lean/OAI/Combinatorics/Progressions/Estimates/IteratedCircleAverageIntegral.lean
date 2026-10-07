import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Fourier.TorusCircleActions

namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

theorem integral_circleCharacter (n : ℤ) :
    (∫ t : Circle, character (n • t) ∂circleHaar) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ite_false]
    exact integral_eq_zero_of_add_right_eq_neg (μ := circleHaar)
      (fourier_add_half_inv_index hn (by norm_num))

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def average (A : IsometricCircleAction X) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFourierComponent 0 f

theorem average_eq_integral (A : IsometricCircleAction X) (f : X → ℂ) (x : X) :
    A.average f x = ∫ t : Circle, f (A.act t x) ∂circleHaar := by
  simp [average, circleFourierComponent]
  rfl

theorem average_lipschitz (A : IsometricCircleAction X) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LipschitzWith L (A.average f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFourierComponent 0 hf A.isometry_act

theorem average_norm_le (A : IsometricCircleAction X) {f : X → ℂ} {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖A.average f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_circleFourierComponent_le 0 f hf x

theorem average_const (A : IsometricCircleAction X) (c : ℂ) (x : X) :
    A.average (fun _ => c) x = c := by
  simp [average_eq_integral]

theorem average_invariant (A : IsometricCircleAction X) (f : X → ℂ) (t : Circle) (x : X) :
    A.average f (A.act t x) = A.average f x := by
  let := A.toAddAction
  change circleFourierComponent 0 f (t +ᵥ x) = circleFourierComponent 0 f x
  simpa only [neg_zero, zero_smul, character_zero, one_mul] using
    circleFourierComponent_vadd 0 f t x

theorem average_unit_interval (A : IsometricCircleAction X) {f : X → ℂ}
    (hf : Continuous f) (hb : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) (x : X) :
    (A.average f x).im = 0 ∧ 0 ≤ (A.average f x).re ∧ (A.average f x).re ≤ 1 := by
  have hcont : Continuous (fun t : Circle => f (A.act t x)) :=
    hf.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const))
  have hi := circle_integrable_of_continuous hcont
  have him : (∫ t : Circle, f (A.act t x) ∂circleHaar).im =
      ∫ t : Circle, (f (A.act t x)).im ∂circleHaar := (integral_im hi).symm
  have hre : (∫ t : Circle, f (A.act t x) ∂circleHaar).re =
      ∫ t : Circle, (f (A.act t x)).re ∂circleHaar := (integral_re hi).symm
  rw [average_eq_integral, him, hre]
  refine ⟨?_, integral_nonneg (fun t => (hb (A.act t x)).2.1), ?_⟩
  · simp_rw [(hb _).1]
    simp
  · have hle := integral_mono (circle_integrable_of_continuous (Complex.continuous_re.comp hcont))
      (integrable_const (1 : ℝ)) (fun t => (hb (A.act t x)).2.2)
    simpa using hle

theorem average_sub (A : IsometricCircleAction X) {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (x : X) :
    A.average (fun y => f y - g y) x = A.average f x - A.average g x := by
  simp only [average_eq_integral]
  apply integral_sub
  · exact circle_integrable_of_continuous
      (hf.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))
  · exact circle_integrable_of_continuous
      (hg.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))

theorem average_sub_norm_le (A : IsometricCircleAction X) {f g : X → ℂ} {B : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, ‖f x - g x‖ ≤ B) (x : X) :
    ‖A.average f x - A.average g x‖ ≤ B := by
  rw [← A.average_sub hf hg]
  exact A.average_norm_le hfg x

theorem average_sum {ι : Type*} (A : IsometricCircleAction X) (s : Finset ι)
    (f : ι → X → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (x : X) :
    A.average (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, A.average (f i) x := by
  simp only [average_eq_integral]
  apply integral_finsetSum
  intro i hi
  exact circle_integrable_of_continuous
    ((hf i hi).comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))

theorem average_equivariant (A : IsometricCircleAction X) {f : X → ℂ}
    (g : X → X) (z : ℂ) (hcomm : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.average f (g x) = z * A.average f x := by
  simp only [average_eq_integral]
  simp_rw [hcomm, hf]
  exact integral_const_mul z _

theorem average_eigenfunction (A : IsometricCircleAction X) {f : X → ℂ} (n : ℤ)
    (hf : ∀ t x, f (A.act t x) = character (n • t) * f x) (x : X) :
    A.average f x = if n = 0 then f x else 0 := by
  rw [average_eq_integral]
  simp_rw [hf]
  rw [integral_mul_const, integral_circleCharacter]
  split_ifs <;> simp

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleAverage (A : α → IsometricCircleAction X) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).average (iteratedCircleAverage A is f)

theorem iteratedCircleAverage_lipschitz (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (iteratedCircleAverage A is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).average_lipschitz ih

theorem iteratedCircleAverage_norm_le (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedCircleAverage A is f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).average_norm_le ih

theorem iteratedCircleAverage_unit_interval (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hb : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) :
    ∀ x, (iteratedCircleAverage A is f x).im = 0 ∧
      0 ≤ (iteratedCircleAverage A is f x).re ∧ (iteratedCircleAverage A is f x).re ≤ 1 := by
  induction is with
  | nil => exact hb
  | cons i is ih =>
    exact (A i).average_unit_interval (iteratedCircleAverage_lipschitz A is hf).continuous ih

theorem iteratedCircleAverage_sub_norm_le (A : α → IsometricCircleAction X) (is : List α)
    {f g : X → ℂ} {Lf Lg : ℝ≥0} {B : ℝ} (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfg : ∀ x, ‖f x - g x‖ ≤ B) :
    ∀ x, ‖iteratedCircleAverage A is f x - iteratedCircleAverage A is g x‖ ≤ B := by
  induction is with
  | nil => exact hfg
  | cons i is ih =>
    exact (A i).average_sub_norm_le (iteratedCircleAverage_lipschitz A is hf).continuous
      (iteratedCircleAverage_lipschitz A is hg).continuous ih

theorem iteratedCircleAverage_sum {ι : Type*} (A : α → IsometricCircleAction X) (is : List α)
    (s : Finset ι) (f : ι → X → ℂ) (L : ι → ℝ≥0) (hf : ∀ i ∈ s, LipschitzWith (L i) (f i)) :
    ∀ x, iteratedCircleAverage A is (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, iteratedCircleAverage A is (f i) x := by
  induction is with
  | nil => intro x; rfl
  | cons i is ih =>
    have heq : iteratedCircleAverage A is (fun y => ∑ j ∈ s, f j y) =
        fun y => ∑ j ∈ s, iteratedCircleAverage A is (f j) y := funext ih
    intro x
    change (A i).average (iteratedCircleAverage A is (fun y => ∑ j ∈ s, f j y)) x = _
    rw [heq]
    exact (A i).average_sum s _ (fun j hj => (iteratedCircleAverage_lipschitz A is (hf j hj)).continuous) x

theorem iteratedCircleAverage_equivariant (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} (g : X → X) (z : ℂ)
    (hcomm : ∀ i ∈ is, ∀ t x, (A i).act t (g x) = g ((A i).act t x))
    (hf : ∀ x, f (g x) = z * f x) :
    ∀ x, iteratedCircleAverage A is f (g x) = z * iteratedCircleAverage A is f x := by
  induction is with
  | nil => exact hf
  | cons i is ih =>
    exact (A i).average_equivariant g z (hcomm i (by simp))
      (ih (fun j hj => hcomm j (by simp [hj])))

theorem iteratedCircleAverage_invariant (A : α → IsometricCircleAction X) (is : List α)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : α) (hj : j ∈ is) (t : Circle) (x : X) :
    iteratedCircleAverage A is f ((A j).act t x) = iteratedCircleAverage A is f x := by
  induction is generalizing x with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact (A i).average_invariant _ t x
    · have htcomm : ∀ a ∈ is, ∀ b ∈ is, (A a).Commutes (A b) :=
        fun a ha b hb => hcomm a (by simp [ha]) b (by simp [hb])
      have ht : ∀ y, iteratedCircleAverage A is f ((A j).act t y) =
          (1 : ℂ) * iteratedCircleAverage A is f y := by
        intro y
        simpa using ih htcomm hj y
      simpa only [iteratedCircleAverage, one_mul] using (A i).average_equivariant ((A j).act t) 1
        (fun u y => hcomm i (by simp) j (by simp [hj]) u t y) ht x

theorem iteratedCircleAverage_eigenfunction (A : α → IsometricCircleAction X) (is : List α)
    (n : α → ℤ) (f : X → ℂ)
    (hf : ∀ i ∈ is, ∀ t x, f ((A i).act t x) = character (n i • t) * f x) :
    iteratedCircleAverage A is f = if ∀ i ∈ is, n i = 0 then f else fun _ => 0 := by
  classical
  induction is with
  | nil => simp [iteratedCircleAverage]
  | cons i is ih =>
    have ht := ih (fun j hj => hf j (by simp [hj]))
    rw [iteratedCircleAverage, ht]
    by_cases htail : ∀ j ∈ is, n j = 0
    · have htail' : (∀ j ∈ is, n j = 0) = True := eq_true htail
      simp only [List.forall_mem_cons, htail', ite_true, and_true]
      funext x
      rw [(A i).average_eigenfunction (n i) (hf i (by simp))]
      split_ifs <;> rfl
    · have htail' : (∀ j ∈ is, n j = 0) = False := eq_false htail
      simp only [List.forall_mem_cons, htail', ite_false, and_false]
      funext x
      exact (A i).average_const 0 x

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory

variable {α : Type*}

def CircleAverageTuple : List α → Type
  | [] => Unit
  | _ :: is => Circle × CircleAverageTuple is

instance circleAverageTupleMeasurableSpace : (is : List α) → MeasurableSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (MeasurableSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleMeasurableSpace is
      inferInstanceAs (MeasurableSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleTopologicalSpace : (is : List α) → TopologicalSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (TopologicalSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleTopologicalSpace is
      inferInstanceAs (TopologicalSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleSecondCountableTopology :
    (is : List α) → SecondCountableTopology (CircleAverageTuple is)
  | [] => inferInstanceAs (SecondCountableTopology Unit)
  | _ :: is =>
      let _ := circleAverageTupleSecondCountableTopology is
      inferInstanceAs (SecondCountableTopology (Circle × CircleAverageTuple is))

instance circleAverageTupleBorelSpace : (is : List α) → BorelSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (BorelSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleBorelSpace is
      inferInstanceAs (BorelSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleCompactSpace : (is : List α) → CompactSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (CompactSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleCompactSpace is
      inferInstanceAs (CompactSpace (Circle × CircleAverageTuple is))

noncomputable def circleAverageTupleMeasure : (is : List α) → Measure (CircleAverageTuple is)
  | [] => Measure.dirac ()
  | _ :: is => circleHaar.prod (circleAverageTupleMeasure is)

instance circleAverageTupleMeasure_probability :
    (is : List α) → IsProbabilityMeasure (circleAverageTupleMeasure is)
  | [] => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | _ :: is =>
      let _ := circleAverageTupleMeasure_probability is
      inferInstanceAs (IsProbabilityMeasure (circleHaar.prod (circleAverageTupleMeasure is)))

variable {X : Type*} [PseudoMetricSpace X]

def iteratedCircleAction (A : α → IsometricCircleAction X) :
    (is : List α) → CircleAverageTuple is → X → X
  | [], _, x => x
  | i :: is, t, x => iteratedCircleAction A is t.2 ((A i).act t.1 x)

theorem continuous_iteratedCircleAction (A : α → IsometricCircleAction X) (is : List α) :
    Continuous (fun p : CircleAverageTuple is × X =>
      iteratedCircleAction A is p.1 p.2) := by
  induction is with
  | nil => exact continuous_snd
  | cons i is ih =>
      change Continuous (fun p : (Circle × CircleAverageTuple is) × X =>
        iteratedCircleAction A is p.1.2 ((A i).act p.1.1 p.2))
      exact ih.comp (continuous_fst.snd.prodMk
        ((A i).continuous_act.comp (continuous_fst.fst.prodMk continuous_snd)))

theorem continuous_iteratedCircleAction_parameter (A : α → IsometricCircleAction X)
    (is : List α) (x : X) : Continuous (fun t => iteratedCircleAction A is t x) :=
  (continuous_iteratedCircleAction A is).comp (continuous_id.prodMk continuous_const)

theorem integrable_iteratedCircleAction (A : α → IsometricCircleAction X)
    (is : List α) {f : X → ℂ} (hf : Continuous f) (x : X) :
    Integrable (fun t => f (iteratedCircleAction A is t x))
      (circleAverageTupleMeasure is) :=
  (hf.comp (continuous_iteratedCircleAction_parameter A is x)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem iteratedCircleAverage_eq_integral (A : α → IsometricCircleAction X)
    (is : List α) {f : X → ℂ} (hf : Continuous f) (x : X) :
    iteratedCircleAverage A is f x =
      ∫ t, f (iteratedCircleAction A is t x) ∂circleAverageTupleMeasure is := by
  induction is generalizing x with
  | nil =>
      change f x = ∫ _ : CircleAverageTuple ([] : List α), f x
        ∂circleAverageTupleMeasure ([] : List α)
      simp
  | cons i is ih =>
      change (A i).average (iteratedCircleAverage A is f) x =
        ∫ t : Circle × CircleAverageTuple is,
          f (iteratedCircleAction A is t.2 ((A i).act t.1 x))
          ∂circleHaar.prod (circleAverageTupleMeasure is)
      rw [(A i).average_eq_integral]
      have hint : Integrable
          (fun t : Circle × CircleAverageTuple is =>
            f (iteratedCircleAction A is t.2 ((A i).act t.1 x)))
          (circleHaar.prod (circleAverageTupleMeasure is)) :=
        integrable_iteratedCircleAction A (i :: is) hf x
      rw [integral_prod _ hint]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => ih ((A i).act t x)))

end Erdos3.CircleFourier

end

end OAI
