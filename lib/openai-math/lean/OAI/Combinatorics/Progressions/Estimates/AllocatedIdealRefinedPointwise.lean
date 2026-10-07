import OAI.Combinatorics.Progressions.Sampling.AllocatedIdealGridEnvelope

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)

include h

theorem AllocatedComparisonDimensions.active_outputs
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    (Fintype.card (Σ a : {a // ¬P a}, O a.val.1) : ℝ) ≤ D := by
  let emb : (Σ a : {a // ¬P a}, O a.val.1) ↪ (Σ a : LayerSamplerAxis I n, O a.1) :=
    Function.Embedding.sigmaMap (Function.Embedding.subtype (fun a => ¬P a))
      (fun a => Function.Embedding.refl (O a.val.1))
  have hc := Fintype.card_le_of_embedding emb
  exact (Nat.cast_le.mpr hc).trans h.outputs

theorem allocatedMaskPower_le_exp {C w : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hCw : C ≤ Real.exp w) :
    C ^ Fintype.card (LayerSamplerAxis I n) ≤ Real.exp (D * w) := by
  calc
    _ ≤ (Real.exp w) ^ Fintype.card (LayerSamplerAxis I n) := pow_le_pow_left₀ hC hCw _
    _ = Real.exp ((Fintype.card (LayerSamplerAxis I n) : ℝ) * w) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h.axes hw)

theorem allocatedPhysicalIdeal_error_le
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    {T : Type*} [Fintype T] (select : T ↪ (Σ a : {a // ¬P a}, O a.val.1))
    (R : Fin m → ℝ) (hR : ∀ j, 0 ≤ R j)
    {δ : ℝ≥0} {p e w E C η ε mesh : ℝ}
    (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hCw : C ≤ Real.exp w)
    (hη : η ≤ physicalIdealErrorShare E (allocatedIdealVolumeEnvelope m D p))
    (hε : ε ≤ physicalIdealErrorShare E (D * w))
    (hmesh : mesh ≤ physicalIdealErrorShare E (D * w + allocatedIdealMeshEnvelope m D p e)) :
    let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩
    let Kp : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound *
      bound ^ Fintype.card (LayerSamplerAxis I n)
    let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬P a}, O a.val.1), R q.1.val.1)⁻¹‖₊ *
      (affineProductProfileLip (Σ a : {a // ¬P a}, O a.val.1) δ *
        NNReal.mk (Real.exp p) (Real.exp_pos p).le)
    let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O p))
      (Real.exp p * (partitionedIdealRadius α m + 1)))
    (2 * Real.exp (allocatedJetSupportLog (G := G) B α O p) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * η +
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card T * ((Kp : ℝ) + Ki) * mesh)) ≤
      Real.exp (-E) := by
  have hc := allocatedIdealGridAllowance_le_exp B h hp select
    (fun q => R q.1.val.1) (fun q => hR q.1.val.1) he
    (h.active_outputs B P) (fun q => hRi q.1.val.1) hδ
  dsimp only at hc ⊢
  have herr := physicalIdeal_three_errors_le
    (by positivity)
    (pow_nonneg hC (Fintype.card (LayerSamplerAxis I n)))
    (mixedOutputGridAllowance_nonneg select (NNReal.coe_nonneg _) (by positivity))
    (allocatedCoefficientErrorVolume_le_exp B h hp)
    (allocatedMaskPower_le_exp B h hC hw hCw) hc hη hε hmesh
  simpa only [mixedOutputGridAllowance, mul_assoc] using herr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def allocatedPhysicalIdealLengthEnvelope {A : Type*} [Semiring A]
    (m : ℕ) (D p e w E : A) : A :=
  allocatedTestLengthEnvelope m D p (E + 3) +
    (E + D * w + allocatedIdealMeshEnvelope m D p e + 3)

theorem allocatedPhysicalIdealLengthEnvelope_nonneg (m : ℕ) {D p e w E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ allocatedPhysicalIdealLengthEnvelope m D p e w E := by
  have ht := allocatedTestLengthEnvelope_nonneg m hD hp (show 0 ≤ E + 3 by positivity)
  have hg := allocatedIdealGridEnvelope_nonneg m hD hp he
  unfold allocatedPhysicalIdealLengthEnvelope allocatedIdealMeshEnvelope
  positivity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D p e w E : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)
variable (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)

include h hp he hw hE

theorem allocatedPhysicalIdealLengthEnvelope_bounds :
    allocatedJointLengthLog (G := G) B α O p
        (E + allocatedIdealVolumeEnvelope m D p + 3) ≤
      allocatedPhysicalIdealLengthEnvelope m D p e w E ∧
    E + D * w + allocatedIdealMeshEnvelope m D p e + 3 ≤
      allocatedPhysicalIdealLengthEnvelope m D p e w E := by
  have hD := h.nonneg
  have hs := allocatedSupportEnvelope_nonneg m hD hp
  have hg := allocatedIdealGridEnvelope_nonneg m hD hp he
  have hm : 0 ≤ E + D * w + allocatedIdealMeshEnvelope m D p e + 3 := by
    unfold allocatedIdealMeshEnvelope; positivity
  have ht := allocatedTestLengthEnvelope_nonneg m hD hp (show 0 ≤ E + 3 by positivity)
  have heq : E + allocatedIdealVolumeEnvelope m D p + 3 =
      allocatedTestEnvelope m D p (E + 3) := by
    unfold allocatedIdealVolumeEnvelope allocatedTestEnvelope
    ring
  constructor
  · apply (allocatedJointLengthLog_le_envelope B h hp
      (show 0 ≤ E + allocatedIdealVolumeEnvelope m D p + 3 by
        unfold allocatedIdealVolumeEnvelope; positivity)).trans
    rw [heq]
    change allocatedTestLengthEnvelope m D p (E + 3) ≤
      allocatedTestLengthEnvelope m D p (E + 3) + _
    exact le_add_of_nonneg_right hm
  · exact le_add_of_nonneg_left ht

theorem allocatedPhysicalIdealLength_spec (degree : ℕ) {S : ℝ}
    (hS : Real.exp (allocatedPhysicalIdealLengthEnvelope m D p e w E) ≤ S) :
    Real.exp (allocatedJointLengthLog (G := G) B α O p
        (E + allocatedIdealVolumeEnvelope m D p + 3)) ≤ S ∧
    1 / S ^ (degree + 1) ≤
      physicalIdealErrorShare E (D * w + allocatedIdealMeshEnvelope m D p e) := by
  have hb := allocatedPhysicalIdealLengthEnvelope_bounds B h hp he hw hE
  have hD := h.nonneg
  have hg := allocatedIdealGridEnvelope_nonneg m hD hp he
  refine ⟨(Real.exp_le_exp.mpr hb.1).trans hS, ?_⟩
  apply physicalIdealErrorShare_scale_mesh degree hE
    (show 0 ≤ D * w + allocatedIdealMeshEnvelope m D p e by
      unfold allocatedIdealMeshEnvelope; positivity)
  have heq : E + (D * w + allocatedIdealMeshEnvelope m D p e) + 3 =
      E + D * w + allocatedIdealMeshEnvelope m D p e + 3 := by ring
  rw [heq]
  exact (Real.exp_le_exp.mpr hb.2).trans hS

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def allocatedIdealScaleInput {A : Type*} [Semiring A]
    (m : ℕ) (D p e w E : A) : A :=
  D + p + allocatedPhysicalIdealLengthEnvelope m D p e w E + 1

def allocatedIdealScaleLog {A : Type*} [Semiring A]
    (m : ℕ) (D p e w E : A) : A :=
  let Q := allocatedIdealScaleInput m D p e w E
  (1 + Q ^ 2) * (5 * Q + 49)

theorem allocatedIdealScaleInput_bounds (m : ℕ) {D p e w E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    let L := allocatedPhysicalIdealLengthEnvelope m D p e w E
    let Q := allocatedIdealScaleInput m D p e w E
    0 ≤ L ∧ 0 ≤ Q ∧ D ≤ Q ∧ p ≤ Q ∧ L + 1 ≤ Q ∧
      Q ≤ allocatedIdealScaleLog m D p e w E := by
  have hL := allocatedPhysicalIdealLengthEnvelope_nonneg m hD hp he hw hE
  have hQ : 0 ≤ allocatedIdealScaleInput m D p e w E := by
    unfold allocatedIdealScaleInput
    positivity
  refine ⟨hL, hQ, ?_, ?_, ?_, le_allocatedScaleLog hQ⟩
  all_goals dsimp only [allocatedIdealScaleInput]; linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem AllocatedComparisonDimensions.integer_axes {D : ℝ}
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (n j : ℝ) ≤ D := by
  have hi : Function.Injective (fun i : Fin (n j) =>
      (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) := by
    intro a b hab
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Sum.inr.injEq] using hab
  have hc := Fintype.card_le_of_injective _ hi
  exact (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hc)).trans h.axes

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedIdealScale (D p e w E : ℝ) :
    LayerSamplerScale (G := G) B U basis R σ :=
  selectedLayerSamplerScale B U basis R σ hR hσ
    ⌈Real.exp (allocatedPhysicalIdealLengthEnvelope m D p e w E)⌉₊

theorem allocatedIdealScale_lower (D p e w E : ℝ) :
    Real.exp (allocatedPhysicalIdealLengthEnvelope m D p e w E) ≤
      ((allocatedIdealScale (G := G) B U basis hR hσ D p e w E).value : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr
    (selectedLayerSamplerScale_bounds B U basis R σ hR hσ _).1)

theorem allocatedIdealScale_upper {D p e w E : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) :
    ((allocatedIdealScale (G := G) B U basis hR hσ D p e w E).value : ℝ) ≤
      Real.exp (allocatedIdealScaleLog m D p e w E) := by
  obtain ⟨hL, hQ, hDQ, hpQ, hLQ, _⟩ :=
    allocatedIdealScaleInput_bounds m hdim.nonneg hp he hw hE
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (allocatedIdealScaleInput m D p e w E) :=
    (hdim.profile.trans hDQ).trans (by linarith [Real.add_one_le_exp (allocatedIdealScaleInput m D p e w E)])
  have hL₀ : (⌈Real.exp (allocatedPhysicalIdealLengthEnvelope m D p e w E)⌉₊ : ℝ) ≤
      Real.exp (allocatedIdealScaleInput m D p e w E) :=
    (natCeil_le_exp_succ_of_le hL le_rfl).trans (Real.exp_le_exp.mpr hLQ)
  exact selectedLayerSamplerScale_exp_bound B U basis R σ hR hσ _ hQ
    (hdim.degree.trans hDQ) (fun j => (hdim.integer_axes B j).trans hDQ)
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hpQ))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpQ))
    (fun j => (hdim.coefficients j).trans hDQ) hA hL₀

theorem allocatedIdealScale_ready {D p e w E : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    let S := allocatedIdealScale (G := G) B U basis hR hσ D p e w E
    Real.exp (allocatedJointLengthLog (G := G) B α O p
        (E + allocatedIdealVolumeEnvelope m D p + 3)) ≤ S.value ∧
      1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
        physicalIdealErrorShare E (D * w + allocatedIdealMeshEnvelope m D p e) :=
  allocatedPhysicalIdealLength_spec B hdim hp he hw hE (layerTailDegree m)
    (allocatedIdealScale_lower B U basis hR hσ D p e w E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedPhysicalIdealLengthEnvelope_ge_parameter (m : ℕ) {D p e w E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    p ≤ allocatedPhysicalIdealLengthEnvelope m D p e w E := by
  have hs := allocatedSupportEnvelope_nonneg m hD hp
  have hg := allocatedIdealGridEnvelope_nonneg m hD hp he
  have hr : p ≤ allocatedIdealRadiusEnvelope m D p := by
    have hm : 0 ≤ ((m + 1 : ℕ) : ℝ) * D := mul_nonneg (Nat.cast_nonneg _) hD
    unfold allocatedIdealRadiusEnvelope
    norm_cast at hm ⊢
    linarith
  have hpg := hr.trans (allocatedIdealGridEnvelope_bounds m hD hp he).1
  have hmesh : p ≤ allocatedIdealMeshEnvelope m D p e := by
    have hd : 0 ≤ D * (allocatedIdealGridEnvelope m D p e + 4) := by positivity
    unfold allocatedIdealMeshEnvelope
    linarith
  have ht := allocatedTestLengthEnvelope_nonneg m hD hp (show 0 ≤ E + 3 by positivity)
  have hdw : 0 ≤ D * w := mul_nonneg hD hw
  unfold allocatedPhysicalIdealLengthEnvelope
  linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedIdealScale_principal_profile_le {D p e w E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hRP : ∀ j, R j ≤ Real.exp p) (j : Fin m) (i : Fin (n j)) :
    principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) ≤
      ((allocatedIdealScale (G := G) B U basis hR hσ D p e w E).value : ℝ) := by
  have hprofile : principalProfileSize (R j)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) ≤ R j := by
    unfold principalProfileSize
    apply div_le_self (hR j).le
    have hc : (0 : ℝ) ≤ Finset.card (layerIntegerPrincipalSlots (G := G) B j i) := Nat.cast_nonneg _
    linarith
  exact hprofile.trans ((hRP j).trans
    ((Real.exp_le_exp.mpr (allocatedPhysicalIdealLengthEnvelope_ge_parameter m hD hp he hw hE)).trans
      (allocatedIdealScale_lower B U basis hR hσ D p e w E)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedIdealMeshEnvelope_ge_input (m : ℕ) {D p e : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) :
    p ≤ allocatedIdealMeshEnvelope m D p e := by
  have hs := allocatedSupportEnvelope_nonneg m hD hp
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  have hproxy : 0 ≤ allocatedProxyLipEnvelope m D p := by
    unfold allocatedProxyLipEnvelope
    positivity
  have hideal : 0 ≤ allocatedIdealLipEnvelope D p e := by
    unfold allocatedIdealLipEnvelope
    positivity
  have hrest : 0 ≤ allocatedSupportEnvelope m D p + (m + 1 : ℕ) * D + 2 +
      allocatedProxyLipEnvelope m D p + allocatedIdealLipEnvelope D p e + 1 := by positivity
  have hgrid : p ≤ allocatedIdealGridEnvelope m D p e := by
    dsimp only [allocatedIdealGridEnvelope, allocatedIdealRadiusEnvelope]
    push_cast at hrest
    linarith
  have hg := allocatedIdealGridEnvelope_nonneg m hD hp he
  have hfront : 0 ≤ D * (allocatedIdealGridEnvelope m D p e + 4) := by positivity
  unfold allocatedIdealMeshEnvelope
  linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedIdeal_refined_length_bound {D p e w E T : ℝ} (N : ℕ)
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hstride : (N : ℝ) * T ≤ p) :
    allocatedRefinedJointLengthLog (G := G) B α O p
      (E + allocatedIdealVolumeEnvelope m D p + 3) ((m + 1 : ℕ) * p + N * T) ≤
      allocatedPhysicalIdealLengthEnvelope m D p e w E := by
  have hD := hdim.nonneg
  have hs := allocatedSupportEnvelope_nonneg m hD hp
  have hvol : 0 ≤ allocatedIdealVolumeEnvelope m D p := by
    unfold allocatedIdealVolumeEnvelope
    positivity
  have hjoint := allocatedJointLengthLog_le_envelope B hdim hp
    (show 0 ≤ E + allocatedIdealVolumeEnvelope m D p + 3 by positivity)
  have heq : E + allocatedIdealVolumeEnvelope m D p + 3 =
      allocatedTestEnvelope m D p (E + 3) := by
    unfold allocatedIdealVolumeEnvelope allocatedTestEnvelope
    ring
  rw [heq] at hjoint
  have hmesh := hstride.trans (allocatedIdealMeshEnvelope_ge_input m hD hp he)
  have hDw : 0 ≤ D * w := mul_nonneg hD hw
  apply (allocatedRefinedJointLengthLog_stride_cost (G := G) B α O p
    (E + allocatedIdealVolumeEnvelope m D p + 3) N hT).trans
  change _ ≤ allocatedTestLengthEnvelope m D p (E + 3) + _
  change _ ≤ allocatedTestLengthEnvelope m D p (E + 3) at hjoint
  rw [heq]
  linarith

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedIdealScale_refined_threshold {D p e w E T : ℝ} (N : ℕ)
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hstride : (N : ℝ) * T ≤ p) :
    Real.exp (allocatedRefinedJointLengthLog (G := G) B α O p
      (E + allocatedIdealVolumeEnvelope m D p + 3) ((m + 1 : ℕ) * p + N * T)) ≤
      ((allocatedIdealScale (G := G) B U b hR hσ D p e w E).value : ℝ) :=
  (Real.exp_le_exp.mpr (allocatedIdeal_refined_length_bound B N hdim hp he hw hE hT hstride)).trans
    (allocatedIdealScale_lower B U b hR hσ D p e w E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable {D p e w E : ℝ}

theorem allocatedIdealScale_refined_pointwise
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp p)
    (hRP : ∀ j, R j ≤ Real.exp p) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) :
    let S := allocatedIdealScale (G := G) B U b hR hσ D p e w E
    let grid := allocatedGridAxis (I := I) U b S.value
    let sides := allocatedPrincipalSides B U b S
    ∀ (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
    {M : ℕ} (_hM : 0 < M) (_hMP : (M : ℝ) ≤ Real.exp p)
    (selection : α ↪ G) (_hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (_hq : Fintype.card α ≤ m + 1) (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j z, (rows j z).card ≤ j.val + 1) (hσ1 : ∀ j, σ j ≤ 1)
    {N : ℕ} {T : ℝ} (_hT : 0 ≤ T) (_hstride : (N : ℝ) * T ≤ p)
    (modulus : ℕ)
    (_hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
    (refined : ℕ) (hRefined : 0 < refined)
    (_hbound : (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * p + N * T))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined)
    (hsize : ∀ a, (Fintype.card α + 1) * refined ≤
      principalAxisLength (fun a => ¬grid a) sides a)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (_hr : ∀ v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue j),
    ∀ z : AllocatedLongJetRows B U b S O,
      |(allocatedLongResidueWeights B U b S refined hRefined r hsize).mean
          (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) *
            allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA modulus residue z| ≤
          physicalIdealErrorShare E (allocatedIdealVolumeEnvelope m D p) := by
  intro S grid sides x rows M hM hMP selection hx hq hinj hrows hσ1 N T hT hstride
    modulus hperiod s hA hi refined hRefined hbound u r hsize residue hr
  have hs := allocatedSupportEnvelope_nonneg m hdim.nonneg hp
  have hD := hdim.nonneg
  have hvol : 0 ≤ allocatedIdealVolumeEnvelope m D p := by
    unfold allocatedIdealVolumeEnvelope
    positivity
  exact allocatedFixedKernel_refined_pointwise (P := p)
    (E := E + allocatedIdealVolumeEnvelope m D p + 3) (T := (m + 1 : ℕ) * p + N * T)
    (η := physicalIdealErrorShare E (allocatedIdealVolumeEnvelope m D p))
    B U b hR hσ S x rows hM selection hx hq hinj hrows hσ1
    hp (by positivity) (by positivity)
    (physicalIdealErrorShare_pos _ _) (physicalIdealErrorShare_le_one hE hvol)
    hMP hRP hRi hσi hcount (physicalIdealErrorShare_inv _ _).le
    (allocatedIdealScale_refined_threshold B U b hR hσ N hdim hp he hw hE hT hstride)
    modulus hperiod s hA hi refined hRefined hbound u r hsize residue hr

end Erdos3.VectorPolynomial

end

end OAI
