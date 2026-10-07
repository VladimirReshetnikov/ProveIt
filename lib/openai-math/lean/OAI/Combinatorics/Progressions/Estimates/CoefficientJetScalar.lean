import OAI.Combinatorics.Progressions.Lattices.IntegerMatrixRealDensity
import OAI.Combinatorics.Progressions.Probability.SigmaFiniteProductMeasure
import OAI.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

def CoefficientAxisRow (K : Type*) {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ} :
    LayerSamplerAxis I n → Type _
  | ⟨j, .inl _⟩ => BoundedCoefficientExponent K (j.val+1) → ℝ
  | ⟨j, .inr _⟩ => BoundedCoefficientExponent K (j.val+1) → ℤ

instance coefficientAxisRowMeasurable (K : Type*) {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    (a : LayerSamplerAxis I n) : MeasurableSpace (CoefficientAxisRow K a) :=
  match a with
  | ⟨j, .inl _⟩ => inferInstanceAs (MeasurableSpace (BoundedCoefficientExponent K (j.val+1) → ℝ))
  | ⟨j, .inr _⟩ => inferInstanceAs (MeasurableSpace (BoundedCoefficientExponent K (j.val+1) → ℤ))

abbrev CoefficientAxisArrays (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ) :=
  ∀ a : LayerSamplerAxis I n, CoefficientAxisRow K a

def coefficientAxisEquiv (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ) :
    CoefficientSamplerArrays (K := K) I n ≃ᵐ CoefficientAxisArrays K I n :=
  (MeasurableEquiv.piCongrRight (fun j =>
    (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientAxisRow K ⟨j, a⟩)).symm)).trans
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm

theorem coefficientAxisEquiv_continuous (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    (a : CoefficientSamplerArrays (K := K) I n) (j : Fin m) (i : I j) :
    coefficientAxisEquiv K I n a ⟨j, Sum.inl i⟩ = (a j).1 i := rfl

theorem coefficientAxisEquiv_integer (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    (a : CoefficientSamplerArrays (K := K) I n) (j : Fin m) (i : Fin (n j)) :
    coefficientAxisEquiv K I n a ⟨j, Sum.inr i⟩ = (a j).2 i := rfl

variable {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val+1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val+1) → PMF ℤ)

noncomputable def coefficientAxisLaw [Fintype K] :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientAxisRow K a)
  | ⟨j, .inl i⟩ => Measure.pi (fun d => affineCoefficientMeasure (c j i d) (w j i d))
  | ⟨j, .inr i⟩ => Measure.pi (fun d => (p j i d).toMeasure)

theorem coefficientAxisLaw_probability [Fintype K]
    (hw : ∀ j i d, 0 < w j i d) (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (coefficientAxisLaw c w p a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    let : ∀ d, IsProbabilityMeasure (affineCoefficientMeasure (c j i d) (w j i d)) :=
      fun d => affineCoefficientMeasure_probability _ (hw j i d)
    change IsProbabilityMeasure (Measure.pi (fun d => affineCoefficientMeasure (c j i d) (w j i d)))
    infer_instance
  | inr i =>
    change IsProbabilityMeasure (Measure.pi (fun d => (p j i d).toMeasure))
    infer_instance

theorem coefficientAxisEquiv_measurePreserving [Fintype K] [∀ j, Fintype (I j)]
    (hw : ∀ j i d, 0 < w j i d) :
    MeasurePreserving (coefficientAxisEquiv K I n)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      (Measure.pi (coefficientAxisLaw c w p)) := by
  let laws := coefficientAxisLaw c w p
  let : ∀ a, IsProbabilityMeasure (laws a) := coefficientAxisLaw_probability c w p hw
  have hinner (j : Fin m) : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientAxisRow K ⟨j, a⟩)).symm
      (mixedScalarArrayLaw (c j) (w j) (p j))
      (Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun a => laws ⟨j, a⟩)
  have houter := measurePreserving_pi
    (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) hinner
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm
      (Measure.pi (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)))
      (Measure.pi laws) :=
    ⟨(MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm.measurable,
      sigmaProductMeasure_flatten laws⟩
  exact hflat.comp houter

def coefficientAxisSplitEquiv (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    CoefficientSamplerArrays (K := K) I n ≃ᵐ
      (∀ a : {a // P a}, CoefficientAxisRow K a.val) ×
        (∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) :=
  (coefficientAxisEquiv K I n).trans (MeasurableEquiv.piEquivPiSubtypeProd (CoefficientAxisRow K) P)

theorem coefficientAxisSplitEquiv_symm_left
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    (u : ∀ a : {a // P a}, CoefficientAxisRow K a.val)
    (v : ∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) (a : {a // P a}) :
    coefficientAxisEquiv K I n ((coefficientAxisSplitEquiv K I n P).symm (u, v)) a.val = u a := by
  exact congrArg (fun z => z.1 a) ((coefficientAxisSplitEquiv K I n P).apply_symm_apply (u, v))

theorem coefficientAxisSplitEquiv_symm_right
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    (u : ∀ a : {a // P a}, CoefficientAxisRow K a.val)
    (v : ∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) (a : {a // ¬P a}) :
    coefficientAxisEquiv K I n ((coefficientAxisSplitEquiv K I n P).symm (u, v)) a.val = v a := by
  exact congrArg (fun z => z.2 a) ((coefficientAxisSplitEquiv K I n P).apply_symm_apply (u, v))

theorem coefficientAxisSplitEquiv_measurePreserving [Fintype K] [∀ j, Fintype (I j)]
    (hw : ∀ j i d, 0 < w j i d) (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    MeasurePreserving (coefficientAxisSplitEquiv K I n P)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      ((Measure.pi (fun a : {a // P a} => coefficientAxisLaw c w p a.val)).prod
        (Measure.pi (fun a : {a // ¬P a} => coefficientAxisLaw c w p a.val))) := by
  let : ∀ a, IsProbabilityMeasure (coefficientAxisLaw c w p a) := coefficientAxisLaw_probability c w p hw
  exact (measurePreserving_piEquivPiSubtypeProd (coefficientAxisLaw c w p) P).comp
    (coefficientAxisEquiv_measurePreserving c w p hw)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

def CoefficientJetAxisRow (O : Fin m → Type*) : LayerSamplerAxis I n → Type _
  | ⟨j, .inl _⟩ => O j → ℝ
  | ⟨j, .inr _⟩ => O j → ℤ

instance coefficientJetAxisRowMeasurable (O : Fin m → Type*) (a : LayerSamplerAxis I n) :
    MeasurableSpace (CoefficientJetAxisRow O a) :=
  match a with
  | ⟨j, .inl _⟩ => inferInstanceAs (MeasurableSpace (O j → ℝ))
  | ⟨j, .inr _⟩ => inferInstanceAs (MeasurableSpace (O j → ℤ))

noncomputable def coefficientJetAxisReference (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientJetAxisRow O a)
  | ⟨j, .inl _⟩ => (volume : Measure (O j → ℝ))
  | ⟨j, .inr _⟩ => (Measure.count : Measure (O j → ℤ))

instance coefficientJetAxisReference_sigmaFinite (O : Fin m → Type*) [∀ j, Fintype (O j)]
    (a : LayerSamplerAxis I n) : SigmaFinite (coefficientJetAxisReference O a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    change SigmaFinite (volume : Measure (O j → ℝ))
    infer_instance
  | inr i =>
    change SigmaFinite (Measure.count : Measure (O j → ℤ))
    infer_instance

noncomputable def coefficientJetAxisMap {K : Type*} [Fintype K] {O : Fin m → Type*}
    (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val+1)) ℤ) :
    ∀ a : LayerSamplerAxis I n, CoefficientAxisRow K a → CoefficientJetAxisRow O a
  | ⟨j, .inl _⟩, c => (A j).map (Int.cast : ℤ → ℝ) *ᵥ c
  | ⟨j, .inr _⟩, c => A j *ᵥ c

theorem coefficientJetAxisMap_measurable {K : Type*} [Fintype K] {O : Fin m → Type*}
    [∀ j, Fintype (O j)]
    (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val+1)) ℤ)
    (a : LayerSamplerAxis I n) : Measurable (coefficientJetAxisMap A a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    exact (matrixSupCLM ((A j).map (Int.cast : ℤ → ℝ))).continuous.measurable
  | inr i =>
    change Measurable (fun c : BoundedCoefficientExponent K (j.val+1) → ℤ => A j *ᵥ c)
    exact measurable_of_countable _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {m : ℕ} {I O O' : Fin m → Type*} {n : Fin m → ℕ}
variable (e : ∀ j, O' j ≃ O j)

noncomputable def coefficientJetRowReindex (a : LayerSamplerAxis I n) :
    CoefficientJetAxisRow O a ≃ᵐ CoefficientJetAxisRow O' a :=
  match a with
  | ⟨j, .inl _⟩ => (MeasurableEquiv.piCongrLeft (fun _ : O j => ℝ) (e j)).symm
  | ⟨j, .inr _⟩ => (MeasurableEquiv.piCongrLeft (fun _ : O j => ℤ) (e j)).symm

variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]

theorem coefficientJetRowReindex_measurePreserving (a : LayerSamplerAxis I n) :
    MeasurePreserving (coefficientJetRowReindex e a)
      (coefficientJetAxisReference O a) (coefficientJetAxisReference O' a) := by
  rcases a with ⟨j, i | i⟩
  · exact (volume_measurePreserving_piCongrLeft (fun _ : O j => ℝ) (e j)).symm
  · change MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : O j => ℤ) (e j)).symm
      (Measure.count : Measure (O j → ℤ)) (Measure.count : Measure (O' j → ℤ))
    have h := (measurePreserving_piCongrLeft (fun _ : O j => (Measure.count : Measure ℤ)) (e j)).symm
    simpa only [pi_count_measure] using h

variable (P : LayerSamplerAxis I n → Prop)

noncomputable def coefficientJetRowsReindex :
    (∀ a : {a // P a}, CoefficientJetAxisRow O a.val) ≃ᵐ
      (∀ a : {a // P a}, CoefficientJetAxisRow O' a.val) :=
  MeasurableEquiv.piCongrRight (fun a => coefficientJetRowReindex e a.val)

variable [∀ j, Fintype (I j)] [DecidablePred P]

theorem coefficientJetRowsReindex_measurePreserving :
    MeasurePreserving (coefficientJetRowsReindex e P)
      (Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O a.val))
      (Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O' a.val)) :=
  measurePreserving_pi _ _ (fun a => coefficientJetRowReindex_measurePreserving e a.val)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

def CoefficientJetScalar : LayerSamplerAxis I n → Type
  | ⟨_, .inl _⟩ => ℝ
  | ⟨_, .inr _⟩ => ℤ

instance coefficientJetScalarMeasurable (a : LayerSamplerAxis I n) :
    MeasurableSpace (CoefficientJetScalar a) :=
  match a with
  | ⟨_, .inl _⟩ => inferInstanceAs (MeasurableSpace ℝ)
  | ⟨_, .inr _⟩ => inferInstanceAs (MeasurableSpace ℤ)

noncomputable def coefficientJetScalarReference :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientJetScalar a)
  | ⟨_, .inl _⟩ => (volume : Measure ℝ)
  | ⟨_, .inr _⟩ => (Measure.count : Measure ℤ)

instance coefficientJetScalarReference_sigmaFinite (a : LayerSamplerAxis I n) :
    SigmaFinite (coefficientJetScalarReference a) := by
  rcases a with ⟨j, i | i⟩
  · change SigmaFinite (volume : Measure ℝ)
    infer_instance
  · change SigmaFinite (Measure.count : Measure ℤ)
    infer_instance

def coefficientJetScalarEquiv (O : Fin m → Type*) (a : LayerSamplerAxis I n) :
    CoefficientJetAxisRow O a ≃ᵐ (O a.1 → CoefficientJetScalar a) :=
  match a with
  | ⟨_, .inl _⟩ => MeasurableEquiv.refl _
  | ⟨_, .inr _⟩ => MeasurableEquiv.refl _

theorem coefficientJetScalarEquiv_measurePreserving (O : Fin m → Type*)
    [∀ j, Fintype (O j)] (a : LayerSamplerAxis I n) :
    MeasurePreserving (coefficientJetScalarEquiv O a)
      (coefficientJetAxisReference O a)
      (Measure.pi (fun _ : O a.1 => coefficientJetScalarReference a)) := by
  rcases a with ⟨j, i | i⟩
  · exact MeasurePreserving.id (volume : Measure (O j → ℝ))
  · change MeasurePreserving id (Measure.count : Measure (O j → ℤ))
      (Measure.pi (fun _ : O j => (Measure.count : Measure ℤ)))
    rw [pi_count_measure]
    exact MeasurePreserving.id _

end Erdos3.VectorPolynomial

end

end OAI
