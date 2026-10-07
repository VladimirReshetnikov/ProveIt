/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Sampling.AllocatedLongGridIntegral

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U basis S O

theorem allocatedLongJetRealCoordinates_measurable :
    Measurable (allocatedLongJetRealCoordinates B U basis S (O := O)) := by
  apply Measurable.of_eval
  intro q
  rcases q with ⟨⟨⟨j, i | i⟩, ha⟩, o⟩
  · exact (measurable_pi_apply o).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inl i⟩, ha⟩) from measurable_pi_apply _)
  · exact (measurable_of_countable
      (fun z : O j → ℤ => (z o : ℝ) / (basisAxisScale (basis j) i : ℝ))).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inr i⟩, ha⟩) from measurable_pi_apply _)

theorem allocatedLongJetBox_of_realCoordinates {T : ℝ} (hT : 0 ≤ T)
    (z : AllocatedLongJetRows B U basis S O)
    (hz : ‖allocatedLongJetRealCoordinates B U basis S z‖ ≤ T) :
    z ∈ allocatedLongJetBox B U basis S O T := by
  apply Set.mem_univ_pi.mpr
  intro a
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change ‖(fun o : O j => z ⟨⟨j, .inl i⟩, ha⟩ o) - 0‖ ≤ T
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg hT).mpr
    intro o
    exact (norm_le_pi_norm (allocatedLongJetRealCoordinates B U basis S z)
      ⟨⟨⟨j, .inl i⟩, ha⟩, o⟩).trans hz
  · change z ⟨⟨j, .inr i⟩, ha⟩ ∈ rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T
    apply Fintype.mem_piFinset.mpr
    intro o
    have ho : |(z ⟨⟨j, .inr i⟩, ha⟩ o : ℝ) / (basisAxisScale (basis j) i : ℝ)| ≤ T :=
      (norm_le_pi_norm (allocatedLongJetRealCoordinates B U basis S z)
        ⟨⟨⟨j, .inr i⟩, ha⟩, o⟩).trans hz
    have hh : (0 : ℝ) < basisAxisScale (basis j) i :=
      Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
    obtain ⟨hlo, hhi⟩ := abs_le.mp ho
    have hlo' := (le_div_iff₀ hh).mp hlo
    have hhi' := (div_le_iff₀ hh).mp hhi
    apply Finset.mem_Icc.mpr
    exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem allocatedLongProfile_zero_off_box
    (f : (output → ℝ) → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hs : ∀ v, T < ‖v‖ → f v = 0)
    (z : AllocatedLongJetRows B U basis S O)
    (hz : z ∉ allocatedLongJetBox B U basis S O T) :
    f (allocatedLongJetRealCoordinates B U basis S z) = 0 :=
  hs _ (lt_of_not_ge (fun h => hz (allocatedLongJetBox_of_realCoordinates B U basis S hT z h)))

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

theorem allocatedLongJetMask_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetMask B U basis S x rows modulus residue a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact measurable_const
  · change Measurable (allocatedIntegerKernelMask B U basis S x rows j modulus (residue j))
    exact measurable_of_countable _

omit [∀ j, Fintype (O j)] in
theorem allocatedLongJetMask_product_bound {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (z : AllocatedLongJetRows B U basis S O) :
    |∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) := by
  have hr (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a (z a) ∧
      allocatedLongJetMask B U basis S x rows modulus residue a (z a) ≤ C := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact ⟨zero_le_one, hC⟩
    · exact hm j _
  rw [abs_of_nonneg (Finset.prod_nonneg (fun a _ => (hr a).1))]
  calc
    _ ≤ ∏ _a : {a // ¬grid a}, C :=
      Finset.prod_le_prod₀ (fun a _ => (hr a).1) (fun a _ => (hr a).2)
    _ = C ^ Fintype.card {a // ¬grid a} := by simp
    _ ≤ _ := pow_le_pow_right₀ hC (Fintype.card_subtype_le _)

theorem allocatedLongMaskedProfile_integrable
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C) :
    Integrable (fun z : AllocatedLongJetRows B U basis S O =>
      (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z)) reference := by
  let box := allocatedLongJetBox B U basis S O T
  have hbox : MeasurableSet box := allocatedLongJetBox_measurable B U basis S O T
  have hmajor : Integrable (box.indicator
      (fun _ : AllocatedLongJetRows B U basis S O => C ^ Fintype.card (LayerSamplerAxis I n) * Cf))
      reference :=
    (integrableOn_const (allocatedLongJetBox_measure_lt_top B U basis S O T).ne).integrable_indicator hbox
  have hmask : Measurable (fun z : AllocatedLongJetRows B U basis S O =>
      ∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U basis S x rows modulus residue a).comp (measurable_pi_apply a))
  apply hmajor.mono' (hmask.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U basis S))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  dsimp only [Pi.mul_apply, Function.comp_apply]
  by_cases hz : z ∈ box
  · rw [Set.indicator_of_mem hz, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right
        (allocatedLongJetMask_product_bound B U basis S x rows modulus residue hC hm z) hCf)
  · rw [Set.indicator_of_notMem hz, allocatedLongProfile_zero_off_box B U basis S f hT hs z hz]
    simp

theorem allocatedLongMaskedProfile_test_integrable
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ)
    (hφb : ∀ z, ‖φ z‖ ≤ 1) :
    Integrable (fun z : AllocatedLongJetRows B U basis S O =>
      (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z /
        ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ))
      reference := by
  exact ((allocatedLongMaskedProfile_integrable B U basis S x rows modulus residue
    f hf hT hs hC hCf hb hm).ofReal.mul_bdd hφ.aestronglyMeasurable
      (Filter.Eventually.of_forall hφb)).div_const _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O))
local notation "reference" => allocatedLongJetReference B U basis S O
local notation "scale" => ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)

theorem allocatedLongGridDensityTest_sub (f g : (output → ℝ) → ℝ)
    (v : realOutput → ℝ) (qs : Finset (integerOutput → ℤ)) (φ : (integerOutput → ℤ) → ℂ) :
    allocatedLongGridDensityTest B U basis S x rows modulus residue (fun z => f z - g z) v qs φ =
      allocatedLongGridDensityTest B U basis S x rows modulus residue f v qs φ -
      allocatedLongGridDensityTest B U basis S x rows modulus residue g v qs φ := by
  simp only [allocatedLongGridDensityTest, mul_sub, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib, sub_div]

theorem allocatedLongReference_test_comparison
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfb : ∀ v, |f v| ≤ Cf) (hgb : ∀ v, |g v| ≤ Cg)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ)
    (hφb : ∀ z, ‖φ z‖ ≤ 1) :
    ‖(∫ z : AllocatedLongJetRows B U basis S O,
        (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
          f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z / scale ∂reference) -
      (∫ z : AllocatedLongJetRows B U basis S O,
        (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
          g (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z / scale ∂reference)‖ ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  have hfi := allocatedLongMaskedProfile_test_integrable B U basis S x rows modulus residue
    f hf.continuous.measurable Ro.coe_nonneg hfs hC hCf hfb hm φ hφ hφb
  have hgi := allocatedLongMaskedProfile_test_integrable B U basis S x rows modulus residue
    g hg.continuous.measurable Ro.coe_nonneg hgs hC hCg hgb hm φ hφ hφb
  have hdi := allocatedLongMaskedProfile_test_integrable B U basis S x rows modulus residue
    (fun v => f v - g v) (hf.continuous.measurable.sub hg.continuous.measurable)
    Ro.coe_nonneg (fun v hv => by rw [hfs v hv, hgs v hv, sub_self])
    hC (add_nonneg hCf hCg)
    (fun v => (abs_sub (f v) (g v)).trans (add_le_add (hfb v) (hgb v))) hm φ hφ hφb
  let qs : Finset (integerOutput → ℤ) := rectangularWeightIndices (fun _ => 0) (allocatedLongLatticeScale B U basis S) (Ro : ℝ)
  have heq := allocatedLongGridDensityTest_integral B U basis S x rows modulus residue
    (fun v => f v - g v) φ (fun _ => qs)
    (fun v k hk => by
      rw [allocatedLongRowsFromGrid_zero_off_indices B U basis S f hfs v k hk,
        allocatedLongRowsFromGrid_zero_off_indices B U basis S g hgs v k hk, sub_self]) hdi
  rw [← integral_sub hfi hgi]
  simp_rw [← sub_div, ← sub_mul, ← Complex.ofReal_sub, ← mul_sub]
  rw [heq]
  simp_rw [allocatedLongGridDensityTest_sub]
  exact allocatedLongGridDensityTest_comparison B U basis S x rows modulus residue
    f g Ro hf hg hfs hgs hfg he hmesh0 hmesh1 hmesh hC hm (fun _ => qs)
    (fun v k => φ (allocatedLongRowsFromGrid B U basis S v k)) (fun v k _ => hφb _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U b S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U b S (O := O))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedUnmaskedLongProfileDensity (f : (output → ℝ) → ℝ)
    (z : AllocatedLongJetRows B U b S O) : ℝ :=
  f (allocatedLongJetRealCoordinates B U b S z) / scale

theorem allocatedUnmaskedLongProfileDensity_measurable
    (f : (output → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedUnmaskedLongProfileDensity B U b S f) :=
  (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S)).div_const _

theorem allocatedUnmaskedLongProfileDensity_integrable
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    {Cf : ℝ} (hb : ∀ v, |f v| ≤ Cf) :
    Integrable (allocatedUnmaskedLongProfileDensity B U b S f) reference := by
  have hi : Integrable (fun z : AllocatedLongJetRows B U b S O =>
      f (allocatedLongJetRealCoordinates B U b S z)) reference := by
    let box := allocatedLongJetBox B U b S O T
    have hbox : MeasurableSet box := allocatedLongJetBox_measurable B U b S O T
    have hmajor : Integrable (box.indicator (fun _ : AllocatedLongJetRows B U b S O => Cf)) reference :=
      (integrableOn_const (allocatedLongJetBox_measure_lt_top B U b S O T).ne).integrable_indicator hbox
    apply hmajor.mono' (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    dsimp only [Function.comp_apply]
    by_cases hz : z ∈ box
    · rw [Set.indicator_of_mem hz, Real.norm_eq_abs]
      exact hb _
    · rw [Set.indicator_of_notMem hz, allocatedLongProfile_zero_off_box B U b S f hT hs z hz]
      exact norm_zero.le
  exact hi.div_const _

theorem allocatedUnmaskedLongProfile_l1
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    {Cf Cg : ℝ} (hfb : ∀ v, |f v| ≤ Cf) (hgb : ∀ v, |g v| ≤ Cg)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) :
    (∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z ∂reference) ≤
      ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
        ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh) := by
  let F := fun v => |f v - g v|
  have hF : LipschitzWith (Kf + Kg) F := densityDifference_lipschitz hf hg
  have hFs : ∀ v, (Ro : ℝ) < ‖v‖ → F v = 0 := by
    intro v hv
    simp only [F, hfs v hv, hgs v hv, sub_self, abs_zero]
  have hFi := allocatedUnmaskedLongProfileDensity_integrable B U b S F hF.continuous.measurable
    Ro.coe_nonneg hFs (fun v => by
      simpa only [F, abs_abs] using (abs_sub (f v) (g v)).trans (add_le_add (hfb v) (hgb v)))
  let qs : Finset (integerOutput → ℤ) := rectangularWeightIndices (fun _ => 0) (allocatedLongLatticeScale B U b S) (Ro : ℝ)
  have ht := fixed_mixed_output_grid_error (allocatedLongIntegerSelect B U b S (O := O))
    F (fun _ => 0) Ro hF (LipschitzWith.const 0) hFs (fun _ _ => rfl)
    (by simpa only [F, sub_zero] using hfg.abs)
    (by simpa only [F, sub_zero, abs_abs] using he)
    (fun _ _ => 0) (fun _ => allocatedLongLatticeScale B U b S)
    (fun _ => allocatedLongLatticeScale_pos B U b S) hmesh0 hmesh1
    (fun _ q => (allocatedLongLatticeScale_mesh B U b S q).trans hmesh)
    (fun _ => qs) (fun _ _ => 1) (fun _ _ => 1)
    (show (0 : ℝ) ≤ 1 by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)
  have heq := allocatedLongRowsFromGrid_integral_finset B U b S
    (fun z => (allocatedUnmaskedLongProfileDensity B U b S F z : ℂ)) hFi.ofReal
    (fun _ => qs) (by
      intro v k hk
      simp only [allocatedUnmaskedLongProfileDensity,
        allocatedLongRowsFromGrid_zero_off_indices B U b S F hFs v k hk, zero_div, Complex.ofReal_zero])
  have hgrid : (∫ z, (allocatedUnmaskedLongProfileDensity B U b S F z : ℂ) ∂reference) =
      ∫ v, gridDensityTest (selectedOutputSlice (allocatedLongIntegerSelect B U b S (O := O)) F v)
        (fun _ => 0) (allocatedLongLatticeScale B U b S) qs (fun _ => 1) (fun _ => 1) -
      gridDensityTest (selectedOutputSlice (allocatedLongIntegerSelect B U b S (O := O)) (fun _ => 0) v)
        (fun _ => 0) (allocatedLongLatticeScale B U b S) qs (fun _ => 1) (fun _ => 1) := by
    rw [heq]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro v
    simp only [allocatedUnmaskedLongProfileDensity, Complex.ofReal_div, gridDensityTest,
      selectedOutputSlice, allocatedLongRowsFromGrid_realCoordinates, allocatedLongLatticeScale_product,
      one_mul, mul_one, Complex.ofReal_zero, Finset.sum_const_zero, zero_div, sub_zero, Finset.sum_div]
  rw [← hgrid, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun z => div_nonneg (abs_nonneg _)
      (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))))] at ht
  simpa only [NNReal.coe_add, NNReal.coe_zero, add_zero, one_mul] using ht

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_long_reference_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        {mesh C : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (_hC : 1 ≤ C)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
        allocatedLongIntegerCoordinate B U basis S q}
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
      let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
        bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
          (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
      let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
        (Real.exp P * (partitionedIdealRadius α m + 1)))
      ∀ (φ : AllocatedLongJetRows B U basis S O → ℂ), Measurable φ →
      (∀ z, ‖φ z‖ ≤ 1) →
      ‖(∫ z : AllocatedLongJetRows B U basis S O,
          (allocatedLongJetProxy B U basis S x u rows s hA modulus residue z : ℂ) * φ z /
            ((∏ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
              allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)
          ∂allocatedLongJetReference B U basis S O) -
        (∫ z : AllocatedLongJetRows B U basis S O,
          (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
            ideal (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z /
            ((∏ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
              allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)
          ∂allocatedLongJetReference B U basis S O)‖ ≤
        C ^ Fintype.card (LayerSamplerAxis I n) *
          (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh)) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_proxy_l1_comparison
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount modulus residue mesh C hmesh0 hmesh1 hmesh hC hm
  dsimp only
  intro φ hφ hφb
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσt j).trans ht1
  have hL1 := (hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA).1
  have hp := allocatedContinuousLongJetProxy_output_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1
  have hip := physicalActiveProfileIdeal_probability (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hpp := allocatedContinuousLongJetProxy_probability B U basis hR hσ S x u rows s hA hσ1
  have hil := physicalActiveProfileIdeal_lipschitz (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRi a.1)
  let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
    (Real.exp P * (partitionedIdealRadius α m + 1)))
  have hRoP : Real.exp (allocatedJetSupportLog (G := G) B α O P) ≤ (Ro : ℝ) :=
    (le_max_left _ _).trans (Real.le_coe_toNNReal _)
  have hRoI : Real.exp P * (partitionedIdealRadius α m + 1) ≤ (Ro : ℝ) :=
    (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  have hib := physicalActiveProfileIdeal_bound (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  simp_rw [allocatedLongJetProxy_continuous]
  apply allocatedLongReference_test_comparison B U basis S x rows modulus residue
    (Cf := (Real.exp (allocatedDensityLog (G := G) B α O P)) ^ Fintype.card (LayerSamplerAxis I n))
    _ _ Ro hp.2 hil
    (fun v hv => allocatedContinuousLongJetProxy_zero_off_ball B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 v (hRoP.trans_lt hv))
    (fun v hv => physicalActiveProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
      (fun a => R a.1) (fun a => hR a.1)
      (fun a => Nat.succ_le_of_lt a.1.isLt) δ hδ hδ1
      ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRP a.1) v (hRoI.trans_lt hv))
    (by positivity)
    (mul_nonneg (inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le)))
      (NNReal.coe_nonneg _))
    (fun v => by rw [abs_of_nonneg (hp.1 v).1]; exact (hp.1 v).2) hib
    (hpp.2.1.sub hip.2.1) _ hmesh0 hmesh1 hmesh hC hm φ hφ hφb
  simpa only [abs_sub_comm] using hL1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_actual_profile_control
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        {mesh : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
        allocatedLongIntegerCoordinate B U basis S q}
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
      let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
        bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
          (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
      let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
        (Real.exp P * (partitionedIdealRadius α m + 1)))
      let proxy := allocatedContinuousLongJetProxy B U basis S x u rows s hA
      let Cp : ℝ≥0 := bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ci : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ * δ⁻¹ ^ Fintype.card (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1)
      LipschitzWith Kp proxy ∧ LipschitzWith Ki ideal ∧
        (∀ z, |proxy z| ≤ Cp) ∧ (∀ z, |ideal z| ≤ Ci) ∧
        Integrable (allocatedUnmaskedLongProfileDensity B U basis S (fun z => |proxy z - ideal z|))
          (allocatedLongJetReference B U basis S O) ∧
        (∫ z, allocatedUnmaskedLongProfileDensity B U basis S (fun v => |proxy v - ideal v|) z
          ∂allocatedLongJetReference B U basis S O) ≤
          ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_proxy_l1_comparison
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount mesh hmesh0 hmesh1 hmesh
  dsimp only
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσt j).trans ht1
  have hL1 := (hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA).1
  have hp := allocatedContinuousLongJetProxy_output_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1
  have hip := physicalActiveProfileIdeal_probability (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hpp := allocatedContinuousLongJetProxy_probability B U basis hR hσ S x u rows s hA hσ1
  have hil := physicalActiveProfileIdeal_lipschitz (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRi a.1)
  let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
    (Real.exp P * (partitionedIdealRadius α m + 1)))
  have hRoP : Real.exp (allocatedJetSupportLog (G := G) B α O P) ≤ (Ro : ℝ) :=
    (le_max_left _ _).trans (Real.le_coe_toNNReal _)
  have hRoI : Real.exp P * (partitionedIdealRadius α m + 1) ≤ (Ro : ℝ) :=
    (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  have hib := physicalActiveProfileIdeal_bound (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hps : ∀ v, (Ro : ℝ) < ‖v‖ →
      allocatedContinuousLongJetProxy B U basis S x u rows s hA v = 0 := fun v hv =>
    allocatedContinuousLongJetProxy_zero_off_ball B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 v (hRoP.trans_lt hv)
  have his : ∀ v, (Ro : ℝ) < ‖v‖ →
      physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ v = 0 := fun v hv =>
    physicalActiveProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
      (fun a => R a.1) (fun a => hR a.1) (fun a => Nat.succ_le_of_lt a.1.isLt) δ hδ hδ1
      ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRP a.1) v (hRoI.trans_lt hv)
  have hpb : ∀ v, |allocatedContinuousLongJetProxy B U basis S x u rows s hA v| ≤
      (Real.exp (allocatedDensityLog (G := G) B α O P)) ^ Fintype.card (LayerSamplerAxis I n) := by
    intro v
    rw [abs_of_nonneg (hp.1 v).1]
    exact (hp.1 v).2
  have hdiffi := allocatedUnmaskedLongProfileDensity_integrable B U basis S
    (fun z => |allocatedContinuousLongJetProxy B U basis S x u rows s hA z -
      physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ z|)
    (hp.2.continuous.measurable.sub hil.continuous.measurable).abs Ro.coe_nonneg
    (fun z hz => by rw [hps z hz, his z hz, sub_self, abs_zero])
    (fun z => by rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hpb z) (hib z)))
  refine ⟨hp.2, hil, ?_, ?_, hdiffi, ?_⟩
  · intro z
    change |allocatedContinuousLongJetProxy B U basis S x u rows s hA z| ≤
      (Real.exp (allocatedDensityLog (G := G) B α O P)) ^ Fintype.card (LayerSamplerAxis I n)
    exact hpb z
  · intro z
    have hnonneg : 0 ≤ (∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹ := inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hib z
  · apply allocatedUnmaskedLongProfile_l1 B U basis S _ _ Ro hp.2 hil hps his
      hpb hib (hpp.2.1.sub hip.2.1) _ hmesh0 hmesh1 hmesh
    simpa only [abs_sub_comm] using hL1

end Erdos3.VectorPolynomial

end

end OAI
