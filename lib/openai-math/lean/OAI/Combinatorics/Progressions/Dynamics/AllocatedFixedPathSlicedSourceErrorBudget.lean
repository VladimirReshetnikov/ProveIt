import OAI.Combinatorics.Progressions.Dynamics.FixedPathSlicedSourceErrorScalar
import OAI.Combinatorics.Progressions.Estimates.SlicedUniformTailTolerance

namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

noncomputable def fixedPathSlicedPerturbationLog (D P Pslice E : ℝ) (m : ℕ) : ℝ :=
  fixedPathPerturbationLog D (P + Pslice) E m

theorem fixedPathSlicedPerturbationLog_nonneg {D P Pslice E : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E) (m : ℕ) :
    0 ≤ fixedPathSlicedPerturbationLog D P Pslice E m :=
  fixedPathPerturbationLog_nonneg hD (add_nonneg hP hPslice) hE m

theorem fixedPathSlicedPerturbation_tail
    (N O m : ℕ) {D P Pslice E a δ A η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hO : (O : ℝ) ≤ D)
    (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp Pslice)
    (hAP : A ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {N' O' : ℕ} (hNN : N' ≤ N) (hOO : O' ≤ O) {t : ℝ}
    (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m)) :
    |t| * polynomialMassC2Budget N' m 1 ≤
      slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  let Q := D + (P + Pslice) + E + m + 2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hDQ : D ≤ Q := by dsimp only [Q]; linarith
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith
  have hsQ : Pslice ≤ Q := by dsimp only [Q]; linarith
  have hEQ : E ≤ Q := by dsimp only [Q]; linarith
  have hmQ : (m : ℝ) ≤ Q := by dsimp only [Q]; linarith
  have hNQ : (N : ℝ) + 1 ≤ Real.exp Q :=
    ((show (N : ℝ) + 1 ≤ D + 1 by linarith).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDQ)
  have hOQ : (O : ℝ) ≤ Real.exp Q :=
    hO.trans ((by linarith [Real.add_one_le_exp D] : D ≤ Real.exp D).trans
      (Real.exp_le_exp.mpr hDQ))
  have hmexp : (m : ℝ) ≤ Real.exp Q :=
    (by linarith [Real.add_one_le_exp (m : ℝ)] : (m : ℝ) ≤ Real.exp m).trans
      (Real.exp_le_exp.mpr hmQ)
  have he := slicedEndpointUniformScale_exp_tail_tolerance N O m ha hδ hA hη hQ
    hNQ hOQ hmexp (haP.trans (Real.exp_le_exp.mpr hPQ))
    (hδP.trans (Real.exp_le_exp.mpr hsQ)) (hAP.trans (Real.exp_le_exp.mpr hPQ))
    (hηE.trans (Real.exp_le_exp.mpr hEQ)) N' O' hNN hOO
  have hmass : 0 ≤ polynomialMassC2Budget N' m 1 := by unfold polynomialMassC2Budget; positivity
  exact (mul_le_mul_of_nonneg_right ht hmass).trans
    (by simpa only [fixedPathSlicedPerturbationLog, fixedPathPerturbationLog, Q] using he)

theorem fixedPathSlicedPerturbation_ratio_lower
    (N O m : ℕ) {D P Pslice E a δ A η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hO : (O : ℝ) ≤ D)
    (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp Pslice)
    (hAP : A ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {N' O' : ℕ} (hNN : N' ≤ N) (hOO : O' ≤ O) :
    Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m) ≤
      slicedPrincipalC2Tolerance N' O' m 1 a δ A η / polynomialMassC2Budget N' m 1 := by
  apply (le_div_iff₀ (by unfold polynomialMassC2Budget; positivity)).mpr
  simpa only [abs_of_pos (Real.exp_pos _)] using
    fixedPathSlicedPerturbation_tail N O m hD hP hPslice hE hN hO ha hδ hA hη
      haP hδP hAP hηE hNN hOO
      (t := Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m))
      (by rw [abs_of_pos (Real.exp_pos _)])

theorem fixedPathSliceWidth_budget {cost : ℝ} (hcost : 0 ≤ cost) :
    0 < Real.exp (-cost) / 2 ∧ Real.exp (-cost) / 2 ≤ 1 ∧
      (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp (cost + 1) := by
  have he : Real.exp (-cost) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcost)
  refine ⟨by positivity, by linarith, ?_⟩
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, Real.exp_add]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg cost)).trans_eq (mul_comm _ _)

theorem fixedPathSliceWidth_lower {cost : ℝ} {S step H : ℕ}
    (hS : 0 < S) (hstep : 0 < step) (hH : 2 ≤ H)
    (hdense : Real.exp (-cost) * S ≤ (H : ℝ)) :
    Real.exp (-cost) / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / S := by
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hstepr : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  apply (le_div_iff₀ hSr).mpr
  calc
    Real.exp (-cost) / 2 * S = (Real.exp (-cost) * S) / 2 := by ring
    _ ≤ (H : ℝ) / 2 := div_le_div_of_nonneg_right hdense (by norm_num)
    _ ≤ (H : ℝ) - 1 := by linarith
    _ ≤ (step : ℝ) * ((H : ℝ) - 1) :=
      le_mul_of_one_le_left (by linarith) hstepr

theorem fixedPathSlice_step_le {cost : ℝ} {S step H : ℕ} (c : ℤ)
    (hS : 0 < S) (hstep : 0 < step) (hH : 2 ≤ H)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (S : ℤ))
    (hdense : Real.exp (-cost) * S ≤ (H : ℝ)) :
    (step : ℝ) ≤ 2 * Real.exp cost := by
  have hbase := hsubset (integerProgressionSupport_point c step H hstep 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c step H hstep (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have hh : 0 ≤ c := by simpa using (Finset.mem_Ico.mp hbase).1
    exact_mod_cast hh
  have hh : (c : ℝ) + (step : ℝ) * ((H : ℝ) - 1) < S := by
    have he : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < S := by
      exact_mod_cast (Finset.mem_Ico.mp hlast).2
    simpa only [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] using he
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hstep0 : (0 : ℝ) ≤ step := Nat.cast_nonneg _
  have hd := mul_le_mul_of_nonneg_left hdense hstep0
  have hb := mul_le_mul_of_nonneg_left
    (show (H : ℝ) ≤ 2 * ((H : ℝ) - 1) by linarith) hstep0
  have hi : (step : ℝ) * Real.exp (-cost) ≤ 2 := by
    apply (mul_le_mul_iff_right₀ hSr).mp
    nlinarith only [hh, hc, hd, hb]
  calc
    (step : ℝ) ≤ 2 / Real.exp (-cost) := (le_div_iff₀ (Real.exp_pos _)).mpr hi
    _ = 2 * Real.exp cost := by rw [Real.exp_neg]; field_simp

theorem fixedPathSlice_mesh_le {cost : ℝ} {S step H : ℕ} (c : ℤ)
    (hS : 0 < S) (hstep : 0 < step) (hH : 2 ≤ H)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (S : ℤ))
    (hdense : Real.exp (-cost) * S ≤ (H : ℝ)) :
    (step : ℝ) / S ≤ 2 * Real.exp cost / S :=
  div_le_div_of_nonneg_right (fixedPathSlice_step_le c hS hstep hH hsubset hdense)
    (Nat.cast_nonneg _)

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedFixedPathSlicedPerturbation_tail_uniform
    {D P Pslice E δ η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hδ : 0 < δ) (hη : 0 < η)
    (haP : (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp Pslice) (hAP : (A : ℝ) ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ} (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m))
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) δ A η := by
  intro active inputs
  exact fixedPathSlicedPerturbation_tail
    (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
    (Fintype.card (LayerSamplerAxis I n)) m hD hP hPslice hE hInput hAxis
    (unitProfilePrincipalLowerBound_pos B) hδ A.coe_nonneg hη haP hδP hAP hηE
    (allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S)
    (Fintype.card_subtype_le _) ht

theorem allocatedFixedPathSlicedPerturbation_tail_of_inputCount
    {D P cost E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ}
    (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) E m))
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η := by
  exact allocatedFixedPathSlicedPerturbation_tail_uniform B U basis hD (by positivity)
    (by positivity) hE hInput hAxis A (fixedPathSliceWidth_budget hcost).1 hη
    ((allocatedUnitProfilePrincipalLowerBound_inv_le_exp B hInput).trans
      (Real.exp_le_exp.mpr (by linarith)))
    (fixedPathSliceWidth_budget hcost).2.2
    (hAP.trans (Real.exp_le_exp.mpr (by linarith))) hηE ht S

theorem allocatedFixedPathSlicedPerturbation_chosen_tail
    {D P cost E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    let Qσ := fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) E m
    let t := Real.exp (-Qσ)
    0 < t ∧ t ≤ 1 ∧ ∀ {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η := by
  intro Qσ t
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (fixedPathSlicedPerturbationLog_nonneg hD (by positivity) (by positivity) hE m)), ?_⟩
  intro R σ S
  exact allocatedFixedPathSlicedPerturbation_tail_of_inputCount B U basis hD hP hcost hE
    hInput hAxis A hη hAP hηE (by rw [abs_of_pos (Real.exp_pos _)]) S

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem fixedPathSlicedGridMesh_scalar_of_floor {D C V cost E : ℝ} {q S : ℕ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S) :
    2 * Real.exp cost / S ≤ Real.exp (-E) := by
  have hS := (fixedPathSlicedGridMeshFloor_pos D C V cost E).trans_le hfloor
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hr : 0 ≤ Real.exp cost * ((q : ℝ) / S) := by positivity
  calc
    _ ≤ 2 * (Real.exp cost * ((q : ℝ) / S)) := by
      rw [mul_div_assoc, ← mul_div_assoc (Real.exp cost)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hq1) (Nat.cast_nonneg _)
    _ ≤ (D + C + 8) * (Real.exp cost * ((q : ℝ) / S)) :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    _ ≤ Real.exp (-(E + 2)) := fixedPathSlicedGridMesh_prefactor hD hC hq hfloor
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem fixedPathSlicedSourceErrorBudget_of_floor
    {D P V cost E : ℝ} (hD : 0 ≤ D) (hP : 2 ≤ P) (hE : 0 ≤ E)
    {Input Kernel : Type*} [Fintype Input] [Fintype Kernel]
    (HP : Input → ℕ) (HG : Kernel → ℕ)
    (hInput : (Fintype.card Input : ℝ) ≤ D) (hKernel : (Fintype.card Kernel : ℝ) ≤ D)
    {q S : ℕ} (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D 4 V cost (P + E + 12) ≤ S)
    (hHP : ∀ i, Real.exp (-cost) * S ≤ (HP i : ℝ))
    (hHG : ∀ i, Real.exp (-cost) * S ≤ (HG i : ℝ))
    {K Kφ ξ : ℝ} (hK0 : 0 ≤ K) (hKφ0 : 0 ≤ Kφ) (hξ0 : 0 ≤ ξ)
    (hK : K ≤ Real.exp P) (hKφ : Kφ ≤ Real.exp P)
    (hξ : ξ ≤ Real.exp (-(P + E + 12))) :
    (∀ i, 2 ≤ HP i ∧ q ≤ HP i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HP i) < 1) ∧
    (∀ i, 2 ≤ HG i ∧ q ≤ HG i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG i) < 1) ∧
    fixedPathSlicedSourceError (∑ i, (q : ℝ) / HP i) (∑ i, (q : ℝ) / HG i)
      (scalarCubeGridBoundaryConstant Empty) K Kφ (2 * Real.exp cost / S)
      (Real.exp (-(P + E + 12))) ξ ≤ Real.exp (-E) := by
  have hP0 : 0 ≤ P := by linarith
  have hF : 0 ≤ P + E + 12 := by positivity
  have hPmesh := fixedPathSlicedGridMesh_of_floor hD (by norm_num : (0 : ℝ) ≤ 4) hF
    HP hInput hq0 hq hfloor hHP (fun _ => 2 * Real.exp cost / S) (fun _ => le_rfl)
  have hGmesh := fixedPathSlicedGridMesh_of_floor hD (by norm_num : (0 : ℝ) ≤ 4) hF
    HG hKernel hq0 hq hfloor hHG (fun _ => 2 * Real.exp cost / S) (fun _ => le_rfl)
  have hC : scalarCubeGridBoundaryConstant Empty = 4 := by
    norm_num [scalarCubeGridBoundaryConstant]
  have hCP : scalarCubeGridBoundaryConstant Empty ≤ Real.exp P := by
    rw [hC]
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at he
    exact (by linarith : (4 : ℝ) ≤ Real.exp 2).trans (Real.exp_le_exp.mpr hP)
  refine ⟨hPmesh.2.2.2, hGmesh.2.2.2, ?_⟩
  apply fixedPathSlicedSourceError_absorb hP0 hE
    (by rw [hC]; norm_num) hK0 hKφ0 hCP hK hKφ
    (by positivity) (by positivity) (by positivity) (Real.exp_nonneg _) hξ0
    hPmesh.1 hGmesh.1
    (fixedPathSlicedGridMesh_scalar_of_floor hD (by norm_num) hq0 hq hfloor)
    le_rfl hξ

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedFixedPathSlicedSourceErrorBudget
    {D P V cost E : ℝ} (hD : 0 ≤ D) (hP : 2 ≤ P)
    (hV : 0 ≤ V) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hG : (Fintype.card G : ℝ) ≤ D)
    (hLift : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) * m ≤ P)
    (A : ℝ≥0) (hAP : (A : ℝ) ≤ Real.exp P) :
    let F := 2 * P + E + 14
    let η := Real.exp (-F)
    let Qσ := fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) F m
    let t := Real.exp (-Qσ)
    let Lmin := fixedPathSlicedGridMeshFloor D 4 V cost F
    0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (D + 2 * P + V + cost + E + 28) ∧
    0 < t ∧ t ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧
    ∀ {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let Input := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η ∧
    ∀ (HP : Input → ℕ) (HG : G → ℕ) (Kφ : ℝ≥0),
    (Kφ : ℝ) ≤ Real.exp P → ∀ {q : ℕ}, 0 < q → (q : ℝ) ≤ Real.exp V →
    Lmin ≤ S.value →
    (∀ i, Real.exp (-cost) * S.value ≤ (HP i : ℝ)) →
    (∀ i, Real.exp (-cost) * S.value ≤ (HG i : ℝ)) →
    ∀ {ξ : ℝ}, 0 ≤ ξ → ξ ≤ η →
    (∀ i, 2 ≤ HP i ∧ q ≤ HP i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HP i) < 1) ∧
    (∀ i, 2 ≤ HG i ∧ q ≤ HG i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG i) < 1) ∧
    fixedPathSlicedSourceError (∑ i, (q : ℝ) / HP i) (∑ i, (q : ℝ) / HG i)
      (scalarCubeGridBoundaryConstant Empty)
      ((Kφ : ℝ) * allocatedOriginalSampleFullSliceLip B U basis S t) Kφ
      (2 * Real.exp cost / S.value) η ξ ≤ Real.exp (-E) := by
  intro F η Qσ t Lmin
  have hP0 : 0 ≤ P := by linarith
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hη : 0 < η := Real.exp_pos _
  have hηF : η⁻¹ ≤ Real.exp F := by
    dsimp only [η]
    rw [Real.exp_neg, inv_inv]
  have htdata := allocatedFixedPathSlicedPerturbation_chosen_tail (G := G) B U basis hD hP0 hcost hF
    hInput hAxis A hη hAP hηF
  change 0 < t ∧ t ≤ 1 ∧ _ at htdata
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at he
    linarith
  refine ⟨fixedPathSlicedGridMeshFloor_pos _ _ _ _ _, ?_, htdata.1, htdata.2.1,
    hη, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hF), ?_⟩
  · apply (fixedPathSlicedGridMeshFloor_le_exp_of_prefactor hD (by norm_num)
      (by norm_num) hfour hV hcost hF).trans
    apply Real.exp_le_exp.mpr
    dsimp only [F]
    linarith
  intro R σ S active Input
  refine ⟨htdata.2.2 S, ?_⟩
  intro HP HG Kφ hKφ q hq0 hq hfloor hHP hHG ξ hξ0 hξ
  have hInput' : (Fintype.card Input : ℝ) ≤ D := by
    apply le_trans _ hInput
    exact_mod_cast allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S
  have hL := allocatedOriginalSampleFullSliceLip_le_two_exp_of_allAxis B U basis S
    htdata.1.le htdata.2.1 hLift
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith
  have hKK : (Kφ : ℝ) * allocatedOriginalSampleFullSliceLip B U basis S t ≤
      Real.exp (2 * P + 2) := by
    calc
      _ ≤ Real.exp P * (2 * Real.exp P) :=
        mul_le_mul hKφ hL (NNReal.coe_nonneg _) (Real.exp_nonneg _)
      _ = 2 * Real.exp (2 * P) := by rw [two_mul P, Real.exp_add]; ring
      _ ≤ Real.exp 2 * Real.exp (2 * P) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hKφ' : (Kφ : ℝ) ≤ Real.exp (2 * P + 2) :=
    hKφ.trans (Real.exp_le_exp.mpr (by linarith))
  have hprec : 2 * P + E + 14 = (2 * P + 2) + E + 12 := by ring
  have hfloor' : fixedPathSlicedGridMeshFloor D 4 V cost ((2 * P + 2) + E + 12) ≤ S.value := by
    simpa only [Lmin, F, hprec] using hfloor
  have hξ' : ξ ≤ Real.exp (-((2 * P + 2) + E + 12)) := by
    simpa only [η, F, hprec] using hξ
  simpa only [η, F, hprec] using
    fixedPathSlicedSourceErrorBudget_of_floor hD (by linarith : 2 ≤ 2 * P + 2) hE
      HP HG hInput' hG hq0 hq hfloor' hHP hHG (by positivity) Kφ.coe_nonneg hξ0 hKK hKφ' hξ'

end Erdos3.VectorPolynomial

end

end OAI
