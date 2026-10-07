import OAI.Combinatorics.Progressions.Probability.AllocatedAmbientDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerMixedCap (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  (allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹^Fintype.card (I j) *
    (allocatedLayerCommonCap (G := G) B R σ L j)^(n j)

noncomputable def allocatedLayerMixedLip (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  (allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹^Fintype.card (I j) *
      (n j * allocatedLayerCommonLip (G := G) B R σ L j * (allocatedLayerCommonCap (G := G) B R σ L j)^(n j)) +
    (allocatedLayerCommonCap (G := G) B R σ L j)^(n j) *
      affineProductProfileLip (I j) (allocatedLayerWidthFloor (G := G) B R σ L j)

noncomputable def allocatedAmbientFactorCap (R σ : Fin m → ℝ) (L : ℕ) (V : Fin m → ℝ≥0) : ℝ≥0 :=
  1 + ∑ j, V j * allocatedLayerMixedCap (G := G) B R σ L j

noncomputable def allocatedAmbientLayerLip (R σ : Fin m → ℝ) (L : ℕ) (d : Fin m → ℕ)
    (C V : Fin m → ℝ≥0) (j : Fin m) : ℝ≥0 :=
  V j * (allocatedLayerMixedLip (G := G) B R σ L j * (C j * d j)) +
    (V j * allocatedLayerMixedCap (G := G) B R σ L j) * 8

noncomputable def allocatedAmbientFactorLip (R σ : Fin m → ℝ) (L : ℕ) (d : Fin m → ℕ)
    (C V : Fin m → ℝ≥0) : ℝ≥0 :=
  ∑ j, allocatedAmbientLayerLip (G := G) B R σ L d C V j

theorem allocatedAmbientFactorCap_one_le (R σ : Fin m → ℝ) (L : ℕ) (V : Fin m → ℝ≥0) :
    1 ≤ allocatedAmbientFactorCap (G := G) B R σ L V := le_add_of_nonneg_right (by positivity)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerMixedInterpolation_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (d) :
    (∀ x, 0 ≤ mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d) x ∧
      mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d) x ≤
          allocatedLayerMixedCap (G := G) B R σ S.value j) ∧
    LipschitzWith (allocatedLayerMixedLip (G := G) B R σ S.value j)
      (mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d)) := by
  have h := mixedDensityInterpolation_bounds
    (fun i => allocatedLayerCenters B U b S j i d) (fun i => allocatedLayerWidths B U b S j i d)
    (fun i => allocatedLayerIntegerInterpolation B U b S j i d)
    (allocatedLayerWidthFloor_pos (G := G) B hR hσ S.positive j)
    (fun i => allocatedLayerWidths_floor B U b S hR hσ j i d)
    (allocatedLayerCommonCap_one_le (G := G) B R σ S.value j)
    (fun i => (allocatedLayerInterpolation_common_bounds B U b S hR hσ j i d).2)
    (fun i x => (allocatedLayerInterpolation_common_bounds B U b S hR hσ j i d).1 x)
  simpa only [allocatedLayerMixedCap, allocatedLayerMixedLip, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_inv, Fintype.card_fin] using h

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedAmbientFactor_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) :
    (∀ x, 0 ≤ coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s x ∧
      coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s x ≤
          allocatedAmbientFactorCap (G := G) B R σ S.value V) ∧
    LipschitzWith (allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V)
      (coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s) := by
  obtain ⟨hcap, hlip⟩ := allocatedLayerMixedInterpolation_bounds B U b S hR hσ s.1 s.2
  obtain ⟨ha, hl⟩ := canonicalAmbientTorusDensity_bounds (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    _ _ _ hcap hlip (hC s.1) (hV s.1)
  have hcaple : V s.1 * allocatedLayerMixedCap (G := G) B R σ S.value s.1 ≤
      allocatedAmbientFactorCap (G := G) B R σ S.value V := by
    apply le_trans (Finset.single_le_sum
      (f := fun j => V j * allocatedLayerMixedCap (G := G) B R σ S.value j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1))
    exact le_add_of_nonneg_left (by norm_num)
  have hliple : allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V s.1 ≤
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V := by
    unfold allocatedAmbientFactorLip
    exact Finset.single_le_sum
      (f := fun j => allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1)
  refine ⟨fun x => ⟨(ha x).1, (ha x).2.trans ?_⟩, hl.weaken hliple⟩
  exact_mod_cast hcaple

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

def allocatedMixedLog (m : ℕ) (P : ℝ) : ℝ :=
  (2*P+1)*(allocatedWidthLog m P + allocatedCommonLog m P)+3*P+1

theorem allocatedMixedLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedMixedLog m P := by
  have hw := allocatedWidthLog_nonneg m hP
  have hc := allocatedCommonLog_nonneg m hP
  unfold allocatedMixedLog
  positivity

namespace VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerMixed_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : (Fintype.card (I j) : ℝ) ≤ P) (hn : (n j : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedLayerMixedCap (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedMixedLog m P) ∧
      (allocatedLayerMixedLip (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedMixedLog m P) := by
  obtain ⟨hc, hl⟩ := allocatedLayerCommonInterpolation_exp_bounds B R σ L j
    hP hR hσ hRP hσP hcount hn hAP hLP
  have hw := allocatedLayerWidthFloor_inv_exp B R σ L hL j hP hR hσ hRP hσP hcount hLP
  have h := mixedInterpolation_constants_exp_bounds (I := I j) (n j)
    hP (allocatedWidthLog_nonneg m hP) (allocatedCommonLog_nonneg m hP) hI hn hw hc hl hAP
  refine ⟨h.1.trans (Real.exp_le_exp.mpr ?_), h.2⟩
  have hw0 := allocatedWidthLog_nonneg m hP
  have hc0 := allocatedCommonLog_nonneg m hP
  have hp := mul_nonneg hP (add_nonneg hw0 hc0)
  unfold allocatedMixedLog
  nlinarith

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem ambientInterpolation_constants_exp_bounds (n : ℕ) {M J C V : ℝ≥0} {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hn : (n : ℝ) ≤ P)
    (hM : (M : ℝ) ≤ Real.exp Q) (hJ : (J : ℝ) ≤ Real.exp Q)
    (hC : (C : ℝ) ≤ Real.exp P) (hV : (V : ℝ) ≤ Real.exp P) :
    ((V*M : ℝ≥0) : ℝ) ≤ Real.exp (Q+P) ∧
      ((V*(J*(C*n))+(V*M)*8 : ℝ≥0) : ℝ) ≤ Real.exp (2*Q+4*P+9) := by
  have hnE : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  constructor
  · simp only [NNReal.coe_mul]
    calc
      _ ≤ Real.exp P * Real.exp Q := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  · simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
    have hfirst : (V : ℝ) * (J * (C * n)) ≤ Real.exp (Q+3*P) := by
      calc
        _ ≤ Real.exp P * (Real.exp Q * (Real.exp P * Real.exp P)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : ((V : ℝ)*M)*8 ≤ Real.exp (Q+P+8) := by
      calc
        _ ≤ (Real.exp P * Real.exp Q) * Real.exp 8 := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    exact (add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond).trans_eq
      (congrArg Real.exp (by ring))

def allocatedAmbientLog (m : ℕ) (P : ℝ) : ℝ :=
  P + P*(2*allocatedMixedLog m P+4*P+9)+1

theorem allocatedAmbientLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedAmbientLog m P := by
  have h := allocatedMixedLog_nonneg m hP
  unfold allocatedAmbientLog
  positivity

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAmbientConstants_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L)
    (d : Fin m → ℕ) (C V : Fin m → ℝ≥0) {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hd : ∀ j, (d j : ℝ) ≤ P) (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (L : ℝ) ≤ Real.exp P) (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    (allocatedAmbientFactorCap (G := G) B R σ L V : ℝ) ≤ Real.exp (allocatedAmbientLog m P) ∧
      (allocatedAmbientFactorLip (G := G) B R σ L d C V : ℝ) ≤ Real.exp (allocatedAmbientLog m P) := by
  have hmix (j : Fin m) := allocatedLayerMixed_exp_bounds (G := G) B R σ L hL j hP (hR j) (hσ j)
    (hRP j) (hσP j) (hcount j) (hI j) (hn j) hAP hLP
  have hlocal (j : Fin m) := ambientInterpolation_constants_exp_bounds (d j) hP
    (allocatedMixedLog_nonneg m hP) (hd j) (hmix j).1 (hmix j).2 (hCP j) (hVP j)
  have hcard : (Fintype.card (Fin m) : ℝ) ≤ P := by simpa only [Fintype.card_fin] using hm
  have hQ := allocatedMixedLog_nonneg m hP
  have hcap := sum_le_exp_of_card_and_uniform_bound
    (fun j => ((V j * allocatedLayerMixedCap (G := G) B R σ L j : ℝ≥0) : ℝ))
    (by positivity : 0 ≤ allocatedMixedLog m P+P) hcard (fun j => (hlocal j).1)
  have hlip := sum_le_exp_of_card_and_uniform_bound
    (fun j => (allocatedAmbientLayerLip (G := G) B R σ L d C V j : ℝ))
    (by positivity : 0 ≤ 2*allocatedMixedLog m P+4*P+9) hcard (fun j => (hlocal j).2)
  constructor
  · simp only [allocatedAmbientFactorCap, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
    apply (one_add_le_exp_succ (by positivity) hcap).trans
    apply Real.exp_le_exp.mpr
    unfold allocatedAmbientLog
    nlinarith
  · simp only [allocatedAmbientFactorLip, NNReal.coe_sum]
    exact hlip.trans (Real.exp_le_exp.mpr (by unfold allocatedAmbientLog; linarith))

end VectorPolynomial
end Erdos3

end

end OAI
