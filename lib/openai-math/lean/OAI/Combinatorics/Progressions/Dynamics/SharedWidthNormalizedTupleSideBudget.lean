import OAI.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def normalizedTupleLateBudget (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l : ℝ) : ℝ :=
  let j := Fintype.card (Unit ⊕ Fin q)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  spatialDiscretizationLog j d p l + anisotropicSpatialMeshLog j d p l +
    (p ^ 3 + anisotropicSpatialCapLog p +
      2 * spatialProfileLog j (Fintype.card (UnselectedColumn s)) p + l + 1) +
    spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3)) + E + 3 + 2 * l +
    Fintype.card (Option (G ⊕ N)) + Fintype.card (Option (G ⊕ N) × X) + Fintype.card N + 40

theorem normalizedTupleLateParameters_bound (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q M : ℕ} (s : Fin q ↪ G)
    {p E l C₀ W Cg Centry : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hM : 0 < M) (hMp : (M : ℝ) ≤ Real.exp p)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hC₀ : 0 ≤ C₀) (hW : 0 ≤ W) (hCentry : 0 ≤ Centry)
    (hC₀l : C₀ ≤ Real.exp l) (hWl : W ≤ Real.exp l) (hCgl : Cg ≤ Real.exp l)
    (hCentryl : Centry ≤ Real.exp l) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp l) :
    let P := normalizedTupleLateBudget X N s p E l
    let δ := normalizedTupleRadius X s M p E W
    let mesh := δ / 4
    let ρ := normalizedTupleResolution X N s M p E C₀ W Cg Centry
    δ⁻¹ ≤ Real.exp (3 * P + 8) ∧ mesh⁻¹ ≤ Real.exp (3 * P + 8) ∧
      ρ ≤ Real.exp (3 * P + 8) := by
  intro P δ mesh ρ
  let j := Fintype.card (Unit ⊕ Fin q)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let Alog := spatialDiscretizationLog j d p l
  let Tlog := anisotropicSpatialMeshLog j d p l
  let Klog := p ^ 3 + anisotropicSpatialCapLog p +
    2 * spatialProfileLog j (Fintype.card (UnselectedColumn s)) p + l + 1
  let tlog := spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3))
  let n₁ : ℝ := Fintype.card (Option (G ⊕ N))
  let n₂ : ℝ := Fintype.card (Option (G ⊕ N) × X)
  let n₃ : ℝ := Fintype.card N
  have hearly := anisotropicTupleEarlyBudget_bounds N s hp (by linarith : 0 ≤ E + 3)
  have hAlog : 0 ≤ Alog := by
    have := spatialProfileLog_nonneg j d hp
    dsimp [Alog, spatialDiscretizationLog]
    positivity
  have hTlog : 0 ≤ Tlog := by
    have := spatialProfileLog_nonneg j d hp
    dsimp [Tlog, anisotropicSpatialMeshLog]
    positivity
  have hKlog : 0 ≤ Klog := by
    have := anisotropicSpatialCapLog_nonneg hp
    have := spatialProfileLog_nonneg j (Fintype.card (UnselectedColumn s)) hp
    dsimp [Klog]
    positivity
  have htlog : 0 ≤ tlog := spatialTupleToleranceLog_nonneg hearly.1
  have hn₁ : 0 ≤ n₁ := Nat.cast_nonneg _
  have hn₂ : 0 ≤ n₂ := Nat.cast_nonneg _
  have hn₃ : 0 ≤ n₃ := Nat.cast_nonneg _
  have hPeq : P = Alog + Tlog + Klog + tlog + E + 3 + 2 * l + n₁ + n₂ + n₃ + 40 := rfl
  have hP : 0 ≤ P := by rw [hPeq]; positivity
  have hAP : Alog ≤ P := by linarith
  have hKP : Klog ≤ P := by linarith
  have htP : tlog ≤ P := by linarith
  have hEP : E + 3 ≤ P := by linarith
  have hTP : Tlog + l + n₁ + 10 ≤ P := by linarith
  have hQP : 2 * l + n₂ + 24 ≤ P := by linarith
  have hDP : l + n₃ + 2 ≤ P := by linarith
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεE : (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
    unfold normalizedSpatialShare
    rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    calc
      _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have ht : 0 < normalizedTupleTolerance X p E :=
    (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _) hε).1
  have hit : (normalizedTupleTolerance X p E)⁻¹ ≤ Real.exp P := by
    have h := spatialTupleTolerance_inv_bound (Fintype.card X) (Real.exp_nonneg _)
      (Real.exp_nonneg _) hε hearly.1 (hX.trans hearly.2.1)
      (Real.exp_le_exp.mpr hearly.2.2.1) (Real.exp_le_exp.mpr hearly.2.2.2.1)
      (hεE.trans (Real.exp_le_exp.mpr hearly.2.2.2.2.2))
    exact h.trans (Real.exp_le_exp.mpr htP)
  have hA := (anisotropicSpatialDiscretizationCost_le_exp N s hp hMp hC₀ hC₀l).trans
    (Real.exp_le_exp.mpr hAP)
  have hκ : 0 ≤ 1 / (M : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hM)).le
  have hlip0 := anisotropicSpatialDensityLip_nonneg s hκ
  have hK : Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)) ≤ Real.exp P := by
    calc
      _ ≤ Real.exp (p ^ 3) *
          (Real.exp (anisotropicSpatialCapLog p + 2 * spatialProfileLog j (Fintype.card (UnselectedColumn s)) p) *
            Real.exp (l + 1)) := by
        gcongr
        · exact anisotropicSpatialDensityLip_le_exp s hp hM hMp hq hG
        · exact one_add_le_exp_succ hl hWl
      _ = Real.exp Klog := by simp only [← Real.exp_add]; congr 1; dsimp [Klog]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hKP
  have hn₁exp : n₁ ≤ Real.exp n₁ := by linarith [Real.add_one_le_exp n₁]
  have hn₂exp : n₂ ≤ Real.exp n₂ := by linarith [Real.add_one_le_exp n₂]
  have hn₃exp : n₃ ≤ Real.exp n₃ := by linarith [Real.add_one_le_exp n₃]
  have hprof : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp (l + 8) := by
    calc
      _ ≤ Real.exp 8 * Real.exp l := by gcongr; linarith [Real.add_one_le_exp (8 : ℝ)]
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hshift : 2 * n₁ * (2 * Centry) ≤ Real.exp (l + n₁ + 4) := by
    calc
      _ = 4 * n₁ * Centry := by ring
      _ ≤ Real.exp 4 * Real.exp n₁ * Real.exp l := by gcongr; linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hT : anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
      2 * n₁ * (2 * Centry) ≤ Real.exp P := by
    have h₁ := (anisotropicSpatialMeshThreshold_le_exp N s hp hC₀ hC₀l).trans
      (Real.exp_le_exp.mpr (show Tlog ≤ Tlog + l + n₁ + 8 by linarith))
    have h₂ := hprof.trans (Real.exp_le_exp.mpr (show l + 8 ≤ Tlog + l + n₁ + 8 by linarith))
    have h₃ := hshift.trans (Real.exp_le_exp.mpr (show l + n₁ + 4 ≤ Tlog + l + n₁ + 8 by linarith))
    calc
      _ ≤ 3 * Real.exp (Tlog + l + n₁ + 8) := by linarith
      _ ≤ Real.exp 2 * Real.exp (Tlog + l + n₁ + 8) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (Tlog + l + n₁ + 10) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hTP
  have hQ : Cg * (24 * probabilityProfileLipschitz * n₂) ≤ Real.exp P := by
    calc
      _ ≤ Real.exp l * (Real.exp 24 * Real.exp l * Real.exp n₂) := by
        gcongr
        linarith [Real.add_one_le_exp (24 : ℝ)]
      _ = Real.exp (2 * l + n₂ + 24) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hQP
  have hD : n₃ * (2 * Centry) ≤ Real.exp P := by
    calc
      _ ≤ Real.exp n₃ * (Real.exp 2 * Real.exp l) := by gcongr; linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = Real.exp (l + n₃ + 2) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hDP
  exact spatialTupleLateParameters_bound (anisotropicSpatialDiscretizationCost_nonneg N s M hC₀)
    (by positivity) ht hε hP hA hK hT hQ hD hit (hεE.trans (Real.exp_le_exp.mpr hEP))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def normalizedTupleWidthLog (N : Type*) [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E : ℝ) : ℝ :=
  let Q := anisotropicTupleEarlyBudget N s p (E + 3)
  2 * (Q + spatialTupleToleranceLog Q) + 4

noncomputable def normalizedTupleSideLog (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l : ℝ) : ℝ :=
  3 * normalizedTupleLateBudget X N s p E l + normalizedTupleWidthLog N s p E + 3 * l + 17

theorem spatialSize_of_log_bounds {W q ρ ξ τ N R B l : ℝ}
    (hW : 0 ≤ W) (hq : 0 ≤ q) (hρ : 0 ≤ ρ) (hξ : 0 < ξ) (hτ : 0 < τ) (hl : 0 ≤ l)
    (hWl : W ≤ Real.exp l) (hql : q ≤ Real.exp l) (hρR : ρ ≤ Real.exp R)
    (hξB : ξ⁻¹ ≤ Real.exp B) (hτl : τ⁻¹ ≤ Real.exp l)
    (hN : Real.exp (R + B + 3 * l + 9) ≤ N) :
    8 * (1 + W) * q * ρ ≤ (ξ * τ) * N := by
  have hs : 8 * (1 + W) * q * ρ * ξ⁻¹ * τ⁻¹ ≤ N := by
    calc
      _ ≤ Real.exp 8 * Real.exp (l + 1) * Real.exp l * Real.exp R * Real.exp B * Real.exp l := by
        gcongr
        · linarith [Real.add_one_le_exp (8 : ℝ)]
        · exact one_add_le_exp_succ hl hWl
      _ = Real.exp (R + B + 3 * l + 9) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hN
  have hs' : (8 * (1 + W) * q * ρ) / (ξ * τ) ≤ N := by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hs
  simpa only [mul_comm N] using (div_le_iff₀ (mul_pos hξ hτ)).mp hs'

theorem normalizedTupleSpatialSize (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q m M : ℕ} (s : Fin q ↪ G)
    {p E l C₀ W Cg Centry stride τ side : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hM : 0 < M)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hC₀ : 0 ≤ C₀) (hW : 0 ≤ W) (hCg : 0 ≤ Cg) (hCentry : 0 ≤ Centry)
    (hC₀l : C₀ ≤ Real.exp l) (hWl : W ≤ Real.exp l) (hCgl : Cg ≤ Real.exp l)
    (hCentryl : Centry ≤ Real.exp l) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp l)
    (hstride : 0 ≤ stride) (hstridel : stride ≤ Real.exp l) (hτ : 0 < τ) (hτl : τ⁻¹ ≤ Real.exp l)
    (hside : Real.exp (normalizedTupleSideLog X N s p E l) ≤ side) :
    8 * (1 + W) * stride * normalizedTupleResolution X N s M p E C₀ W Cg Centry ≤
      (normalizedTupleNarrowWidth X N s M p E * τ) * side := by
  obtain ⟨hξ, _, hξlog, hc⟩ := normalizedTupleSpatialChoices (N := N) (X := X)
    (m := m) s hM hp hE hm hq hG hX hMp
  have hρ := (hc (C₀ := C₀) (W := W) (L := 1 + W) (Cg := Cg) (Centry := Centry)
    (growth := 1) hC₀ hW (by linarith) hCg hCentry (Real.one_le_exp hp) (by linarith)).2.2.2.1
  have hq' : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hlate := normalizedTupleLateParameters_bound X N s hp hE hl hM hMp hq' hG hX
    hC₀ hW hCentry hC₀l hWl hCgl hCentryl hprofile
  apply spatialSize_of_log_bounds hW hstride hρ.le hξ hτ hl hWl hstridel hlate.2.2 hξlog hτl
  convert hside using 1
  unfold normalizedTupleSideLog normalizedTupleWidthLog
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def sharedWidthNormalizedTupleSideLog (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l Bξ : ℝ) : ℝ :=
  3 * normalizedTupleLateBudget X N s p E l + Bξ + 3 * l + 17

theorem sharedWidthNormalizedTupleSpatialSize (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q m M : ℕ} (s : Fin q ↪ G)
    {p E l C₀ W Cg Centry stride ξ Bξ τ side : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hM : 0 < M)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hC₀ : 0 ≤ C₀) (hW : 0 ≤ W) (hCg : 0 ≤ Cg) (hCentry : 0 ≤ Centry)
    (hC₀l : C₀ ≤ Real.exp l) (hWl : W ≤ Real.exp l) (hCgl : Cg ≤ Real.exp l)
    (hCentryl : Centry ≤ Real.exp l) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp l)
    (hstride : 0 ≤ stride) (hstridel : stride ≤ Real.exp l) (hτ : 0 < τ) (hτl : τ⁻¹ ≤ Real.exp l)
    (hξ : 0 < ξ) (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (hside : Real.exp (sharedWidthNormalizedTupleSideLog X N s p E l Bξ) ≤ side) :
    8 * (1 + W) * stride * normalizedTupleResolution X N s M p E C₀ W Cg Centry ≤
      (ξ * τ) * side := by
  obtain ⟨_, _, _, hc⟩ := normalizedTupleSpatialChoices (N := N) (X := X)
    (m := m) s hM hp hE hm hq hG hX hMp
  have hρ := (hc (C₀ := C₀) (W := W) (L := 1 + W) (Cg := Cg) (Centry := Centry)
    (growth := 1) hC₀ hW (by linarith) hCg hCentry (Real.one_le_exp hp) (by linarith)).2.2.2.1
  have hq' : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hlate := normalizedTupleLateParameters_bound X N s hp hE hl hM hMp hq' hG hX
    hC₀ hW hCentry hC₀l hWl hCgl hCentryl hprofile
  apply spatialSize_of_log_bounds hW hstride hρ.le hξ hτ hl hWl hstridel hlate.2.2 hξB hτl
  convert hside using 1
  unfold sharedWidthNormalizedTupleSideLog
  congr 1
  ring

end Erdos3

end

end OAI
