import OAI.Combinatorics.Progressions.Estimates.AllocatedSiteBufferLog

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedLongProfileDensity (f : (output → ℝ) → ℝ)
    (z : AllocatedLongJetRows B U b S O) : ℝ :=
  (∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) *
    f (allocatedLongJetRealCoordinates B U b S z) / scale

theorem allocatedLongProfileDensity_measurable (f : (output → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedLongProfileDensity B U b S x rows modulus residue f) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U b S O =>
      ∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U b S x rows modulus residue a).comp (measurable_pi_apply a))
  exact (hm.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S))).div_const _

theorem allocatedLongProfileDensity_nonneg
    (f : (output → ℝ) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z)
    (z : AllocatedLongJetRows B U b S O) :
    0 ≤ allocatedLongProfileDensity B U b S x rows modulus residue f z := by
  apply div_nonneg (mul_nonneg ?_ (hf _))
    (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))
  apply Finset.prod_nonneg
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact zero_le_one
  · exact hm j _

theorem allocatedLongProfileDensity_ne_zero
    (f : (output → ℝ) → ℝ) (z : AllocatedLongJetRows B U b S O)
    (hz : allocatedLongProfileDensity B U b S x rows modulus residue f z ≠ 0) :
    f (allocatedLongJetRealCoordinates B U b S z) ≠ 0 := by
  intro he
  apply hz
  simp only [allocatedLongProfileDensity, he, mul_zero, zero_div]

theorem allocatedLongProfileDensity_integrable
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C) :
    Integrable (allocatedLongProfileDensity B U b S x rows modulus residue f) reference :=
  (allocatedLongMaskedProfile_integrable B U b S x rows modulus residue
    f hf hT hs hC hCf hb hm).div_const _

theorem allocatedLongProfileDensity_proxy [Fintype α] [∀ j, DecidableEq (O j)]
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (z : AllocatedLongJetRows B U b S O) :
    allocatedLongProfileDensity B U b S x rows modulus residue
      (allocatedContinuousLongJetProxy B U b S x u rows s hA) z =
      allocatedLongJetProxy B U b S x u rows s hA modulus residue z / scale := by
  rw [allocatedLongJetProxy_continuous]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := O) a)

theorem allocatedLongProfileDensity_integral_abs_bound
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C) :
    (∫ z, |allocatedLongProfileDensity B U b S x rows modulus residue f z| ∂reference) ≤
      (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
        (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
  let A : ℝ := C ^ Fintype.card (LayerSamplerAxis I n) * Cf
  let box := allocatedLongJetBox B U b S O T
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) hCf
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hbox : MeasurableSet box := allocatedLongJetBox_measurable B U b S O T
  have hi := allocatedLongProfileDensity_integrable B U b S x rows modulus residue
    f hf hT hs hC hCf hb hm
  have hmajor : Integrable (box.indicator (fun _ : AllocatedLongJetRows B U b S O => A / scale)) reference :=
    (integrableOn_const (allocatedLongJetBox_measure_lt_top B U b S O T).ne).integrable_indicator hbox
  have hbound (z : AllocatedLongJetRows B U b S O) :
      |allocatedLongProfileDensity B U b S x rows modulus residue f z| ≤
        box.indicator (fun _ => A / scale) z := by
    by_cases hz : z ∈ box
    · rw [Set.indicator_of_mem hz, allocatedLongProfileDensity, abs_div, abs_of_pos hscale, abs_mul]
      apply div_le_div_of_nonneg_right _ hscale.le
      exact (mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (allocatedLongJetMask_product_bound B U b S x rows modulus residue hC hm z) hCf)
    · rw [Set.indicator_of_notMem hz, allocatedLongProfileDensity,
        allocatedLongProfile_zero_off_box B U b S f hT hs z hz, mul_zero, zero_div, abs_zero]
  calc
    _ ≤ ∫ z, box.indicator (fun _ => A / scale) z ∂reference := integral_mono hi.abs hmajor hbound
    _ = (A / scale) * (reference).real box := by
      rw [integral_indicator hbox, setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ (A / scale) * ((2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * scale) :=
      mul_le_mul_of_nonneg_left (allocatedLongJetBox_measure_bound B U b S O hT) (div_nonneg hA hscale.le)
    _ = _ := by dsimp only [A]; field_simp [hscale.ne']

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "invVolume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))⁻¹
local notation "radius" => idealSiteEnvelopeRadius α m

local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))

variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)

noncomputable def allocatedSiteTermDensity
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : AllocatedLongJetRows B U b S jets) : ℂ :=
  ((∏ a, allocatedLongJetMask B U b S x jetRows modulus residue a (z a) : ℝ) : ℂ) *
    ((∏ s, f s (allocatedIdealSiteCoordinates B U b S z s)) / ((volume : ℝ) : ℂ)) / ((scale : ℝ) : ℂ)

theorem allocatedSiteTermDensity_sum
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {T : Type*} [Fintype T] (c : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : AllocatedLongJetRows B U b S jets) :
    (∑ i, c i * allocatedSiteTermDensity B U b S x modulus residue (f i) z) =
      ((∏ a, allocatedLongJetMask B U b S x jetRows modulus residue a (z a) : ℝ) : ℂ) *
        ((∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / ((volume : ℝ) : ℂ)) / ((scale : ℝ) : ℂ) := by
  simp only [allocatedSiteTermDensity, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem allocatedSiteTermDensity_error
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hR : ∀ j, 0 < R j) (ideal : (output → ℝ) → ℝ)
    {T : Type*} [Fintype T] (c : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ z : AllocatedLongJetRows B U b S jets,
      ‖(ideal (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / ((volume : ℝ) : ℂ)‖ ≤
        ε * allocatedIdealSiteEnvelope B U b S z)
    (z : AllocatedLongJetRows B U b S jets) :
    ‖(allocatedLongProfileDensity B U b S x jetRows modulus residue ideal z : ℂ) -
      ∑ i, c i * allocatedSiteTermDensity B U b S x modulus residue (f i) z‖ ≤
      ε * |allocatedLongProfileDensity B U b S x jetRows modulus residue
        (allocatedSiteBuffer B U b S) z| := by
  let mask : ℝ := ∏ a, allocatedLongJetMask B U b S x jetRows modulus residue a (z a)
  have hfactor : (allocatedLongProfileDensity B U b S x jetRows modulus residue ideal z : ℂ) -
      ∑ i, c i * allocatedSiteTermDensity B U b S x modulus residue (f i) z =
      ((mask : ℂ) / ((scale : ℝ) : ℂ)) *
        ((ideal (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
          (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / ((volume : ℝ) : ℂ)) := by
    rw [allocatedSiteTermDensity_sum]
    simp only [allocatedLongProfileDensity, Complex.ofReal_div, Complex.ofReal_mul, mask]
    ring
  rw [hfactor, norm_mul, norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (|mask| / |scale|) * (ε * allocatedIdealSiteEnvelope B U b S z) :=
      mul_le_mul_of_nonneg_left (he z) (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ (|mask| / |scale|) *
        (ε * allocatedSiteBuffer B U b S (allocatedLongJetRealCoordinates B U b S z)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (allocatedIdealSiteEnvelope_le_buffer B U b S hR z) hε)
        (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [allocatedLongProfileDensity, abs_div, abs_mul,
        abs_of_nonneg (allocatedSiteBuffer_range B U b S hR _).1, mask]
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedUnmaskedLongProfile_probability_mass
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1) → ℝ) → ℝ)
    (K Ro : ℝ≥0) (hf : LipschitzWith K f) (hf0 : ∀ v, 0 ≤ f v)
    (hfi : Integrable f) (hmass : (∫ v, f v) = 1)
    (hs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0) {Cf : ℝ} (hfb : ∀ v, |f v| ≤ Cf)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (herror : mixedOutputGridAllowance (allocatedLongIntegerSelect B U b S (O := O)) Ro K * mesh ≤ 1) :
    Integrable (allocatedUnmaskedLongProfileDensity B U b S f) (allocatedLongJetReference B U b S O) ∧
      (∫ z, |allocatedUnmaskedLongProfileDensity B U b S f z| ∂allocatedLongJetReference B U b S O) ≤ 2 := by
  have hi := allocatedUnmaskedLongProfileDensity_integrable B U b S f hf.continuous.measurable
    Ro.coe_nonneg hs hfb
  have hfg : Integrable (fun v => f v - (0 : ℝ)) := by simpa only [sub_zero] using hfi
  have hint : (∫ v, |f v - (0 : ℝ)|) ≤ 1 := by
    simp only [sub_zero, abs_of_nonneg (hf0 _)]
    exact hmass.le
  have hbound := allocatedUnmaskedLongProfile_l1 B U b S f (fun _ => 0) Ro
    hf (LipschitzWith.const 0) hs (fun _ _ => rfl) hfb (fun _ => (show |(0 : ℝ)| ≤ 0 by norm_num))
    hfg hint hmesh0 hmesh1 hmesh
  have hscale : 0 < ∏ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
      allocatedLongJetOutputScale B U b S (O := O) a :=
    Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have heq : (fun z => allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - 0|) z) =
      (fun z => |allocatedUnmaskedLongProfileDensity B U b S f z|) := by
    funext z
    simp only [allocatedUnmaskedLongProfileDensity, sub_zero, abs_div, abs_of_pos hscale]
  rw [heq] at hbound
  refine ⟨hi, hbound.trans ?_⟩
  simp only [NNReal.coe_zero, add_zero]
  have h := herror
  dsimp only [mixedOutputGridAllowance] at h
  nlinarith only [h]

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

theorem allocatedLongProfileDensity_integral_mass
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1) → ℝ) → ℝ)
    (hf : Measurable f)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S f) (allocatedLongJetReference B U b S O))
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C) :
    Integrable (allocatedLongProfileDensity B U b S x rows modulus residue f) (allocatedLongJetReference B U b S O) ∧
      (∫ z, |allocatedLongProfileDensity B U b S x rows modulus residue f z| ∂allocatedLongJetReference B U b S O) ≤
        C ^ Fintype.card (LayerSamplerAxis I n) *
          (∫ z, |allocatedUnmaskedLongProfileDensity B U b S f z| ∂allocatedLongJetReference B U b S O) := by
  have hpoint (z : AllocatedLongJetRows B U b S O) :
      |allocatedLongProfileDensity B U b S x rows modulus residue f z| ≤
        C ^ Fintype.card (LayerSamplerAxis I n) * |allocatedUnmaskedLongProfileDensity B U b S f z| := by
    rw [allocatedLongProfileDensity, allocatedUnmaskedLongProfileDensity, mul_div_assoc, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (allocatedLongJetMask_product_bound B U b S x rows modulus residue hC hm z) (abs_nonneg _)
  have hmajor := hi.abs.const_mul (C ^ Fintype.card (LayerSamplerAxis I n))
  have him : Integrable (allocatedLongProfileDensity B U b S x rows modulus residue f)
      (allocatedLongJetReference B U b S O) := by
    apply hmajor.mono' (allocatedLongProfileDensity_measurable B U b S x rows modulus residue f hf).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hpoint z)
  refine ⟨him, (integral_mono him.abs hmajor hpoint).trans_eq ?_⟩
  exact integral_const_mul _ _

end Erdos3.VectorPolynomial

end

end OAI
