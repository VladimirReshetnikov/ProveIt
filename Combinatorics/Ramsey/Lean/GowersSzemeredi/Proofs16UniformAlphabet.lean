import GowersSzemeredi.Proofs16AlphabetConcentration
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Pi

/-! Independent uniform letters and one-symbol concentration on any
finite set of positions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace LeanProofs.GowersSzemeredi

def alphabetWordMeasure (I C : Type*) [Fintype I] [Fintype C] [Nonempty C] [MeasurableSpace C] :
    Measure (I → C) := Measure.pi (fun _ : I => (PMF.uniformOfFintype C).toMeasure)

instance alphabetWordMeasure_probability (I C : Type*) [Fintype I] [Fintype C]
    [Nonempty C] [MeasurableSpace C] : IsProbabilityMeasure (alphabetWordMeasure I C) := by
  unfold alphabetWordMeasure
  infer_instance

theorem alphabet_uniform_indicator_mean {C : Type*} [Fintype C] [Nonempty C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C] (c : C) :
    (∫ x : C, (if x = c then (1 : Real) else 0) ∂(PMF.uniformOfFintype C).toMeasure) =
      1 / Fintype.card C := by
  have h := integral_indicator_const (μ := (PMF.uniformOfFintype C).toMeasure)
    (1 : Real) (measurableSet_singleton c)
  simpa [Set.indicator, Measure.real, PMF.toMeasure_apply_singleton,
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv] using h

theorem alphabetWordMeasure_symbol_concentration {I C : Type*} [Fintype I] [Fintype C]
    [Nonempty C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C]
    (T : Finset I) (c : C) (epsilon : Real) (hε : 0 ≤ epsilon) :
    (alphabetWordMeasure I C).real {w | (1 / (Fintype.card C : Real) + epsilon) * T.card ≤
      ((T.filter (fun i => w i = c)).card : Real)} ≤ Real.exp (-2 * epsilon ^ 2 * T.card) := by
  classical
  let ν := (PMF.uniformOfFintype C).toMeasure
  let X : I → (I → C) → Real := fun i w => if w i = c then 1 else 0
  have hletter : Measurable (fun x : C => if x = c then (1 : Real) else 0) := measurable_of_countable _
  have hi : iIndepFun X (alphabetWordMeasure I C) :=
    iIndepFun_pi (μ := fun _ : I => ν) (fun _ => hletter.aemeasurable)
  have hm (i : I) : AEMeasurable (X i) (alphabetWordMeasure I C) :=
    (hletter.comp (measurable_pi_apply i)).aemeasurable
  have hb (i : I) : ∀ᵐ w ∂alphabetWordMeasure I C, X i w ∈ Set.Icc (0 : Real) 1 := by
    apply ae_of_all
    intro w
    dsimp [X]
    split_ifs <;> constructor <;> norm_num
  have hmean (i : I) : (∫ w, X i w ∂alphabetWordMeasure I C) = 1 / (Fintype.card C : Real) := by
    change (∫ w : I → C, (if w i = c then (1 : Real) else 0) ∂Measure.pi (fun _ : I => ν)) = _
    exact (integral_comp_eval (μ := fun _ : I => ν) (i := i)
      (f := fun x : C => if x = c then (1 : Real) else 0) hletter.aestronglyMeasurable).trans
      (alphabet_uniform_indicator_mean c)
  have ht := finiteAlphabet_hoeffding (alphabetWordMeasure I C) X hi hm hb T
    (1 / (Fintype.card C : Real)) epsilon hε (fun i _ => hmean i)
  have he (w : I → C) : (∑ i ∈ T, X i w) = ((T.filter (fun i => w i = c)).card : Real) := by
    simp [X]
  simpa only [he] using ht

end LeanProofs.GowersSzemeredi
