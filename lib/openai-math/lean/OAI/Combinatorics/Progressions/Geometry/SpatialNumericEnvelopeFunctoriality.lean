import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource
import OAI.Combinatorics.Progressions.Estimates.BoundedAnisotropicTupleChoices

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicSpatialMeshLog (j d : ℕ) (p l : ℝ) : ℝ :=
  (j : ℝ) ^ 2 + j * l + 4 * (j + d) + spatialProfileLog j d p + 3

theorem anisotropicSpatialMeshThreshold_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {C p l : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hCl : C ≤ Real.exp l) :
    anisotropicSpatialMeshThreshold s N C ≤
      Real.exp (anisotropicSpatialMeshLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p l) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let P := spatialProfileLog j d p
  let Q := ((j + d : ℕ) : ℝ) * 4 + P
  have hP : 0 ≤ P := spatialProfileLog_nonneg j d hp
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hK : ((d + j : ℝ) * probabilityProfileLipschitz) ≤ Real.exp P :=
    (spatialProfileLog_bounds N s (M := 0) hp (by simpa using Real.exp_nonneg p)).2.2.2
  have hfour : (4 : ℝ) ^ (j + d) ≤ Real.exp (((j + d : ℕ) : ℝ) * 4) :=
    pow_le_exp_mul_of_le_exp (by norm_num) (by linarith [Real.add_one_le_exp (4 : ℝ)])
      (by norm_num) (j + d) le_rfl
  have hprod : 4 ^ (j + d) * ((d + j : ℝ) * probabilityProfileLipschitz) ≤ Real.exp Q := by
    calc
      _ ≤ Real.exp (((j + d : ℕ) : ℝ) * 4) * Real.exp P := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hsum := one_add_le_exp_succ hQ hprod
  have hdet : (j.factorial : ℝ) * C ^ j ≤ Real.exp ((j : ℝ) ^ 2 + j * l) := by
    calc
      _ ≤ Real.exp ((j : ℝ) ^ 2) * (Real.exp l) ^ j := by
        gcongr
        exact factorial_le_exp_sq j
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  change 2 * (1 + 4 ^ (j + d) * ((d + j : ℝ) * probabilityProfileLipschitz)) *
    (j.factorial * C ^ j) ≤ _
  calc
    _ ≤ Real.exp 2 * Real.exp (Q + 1) * Real.exp ((j : ℝ) ^ 2 + j * l) := by
      gcongr
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [anisotropicSpatialMeshLog, Q, P]
      push_cast
      ring

theorem anisotropicSpatialDensityLip_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {M : ℕ} {p : ℝ} (hp : 0 ≤ p) (hM : 0 < M)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hI : (Fintype.card (Unit ⊕ I) : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p) :
    anisotropicSpatialDensityLip s (1 / (M : ℝ)) ≤
      Real.exp (anisotropicSpatialCapLog p +
        2 * spatialProfileLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p) := by
  let P := spatialProfileLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p
  have hdata := spatialProfileLog_bounds Empty s hp hMp
  have hinv : physicalSpatialInverseBound I (1 / (M : ℝ)) ≤ Real.exp P := by
    rw [physicalSpatialInverseBound_eq_scalar]
    simpa only [P, Fintype.card_sum, Fintype.card_empty, add_zero] using hdata.2.1
  have hK : ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) *
      probabilityProfileLipschitz) ≤ Real.exp P := by
    simpa only [P, Fintype.card_sum, Fintype.card_empty, add_zero] using hdata.2.2.2
  have hcap := anisotropicSpatialDensityCap_exp_bound s hp hM hMp hI hJ
  have hcap0 := anisotropicSpatialDensityCap_nonneg s
    (show 0 ≤ 1 / (M : ℝ) by positivity)
  have hinv0 : 0 ≤ physicalSpatialInverseBound I (1 / (M : ℝ)) := by
    unfold physicalSpatialInverseBound
    positivity
  unfold anisotropicSpatialDensityLip
  calc
    _ ≤ Real.exp (anisotropicSpatialCapLog p) * Real.exp P * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem probabilityProfileLipschitz_le_comparisonProfileBound :
    (probabilityProfileLipschitz : ℝ) ≤ VectorPolynomial.comparisonProfileBound :=
  (Nat.le_ceil _).trans (by unfold VectorPolynomial.comparisonProfileBound; push_cast; linarith)

noncomputable def spatialFixedProfileEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  (p + 1) * p + p ^ 2 + 4 * p + (VectorPolynomial.comparisonProfileBound : ℕ) + 1

noncomputable def spatialDisplacementEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  p ^ 2 + (p + 3) * spatialFixedProfileEnvelope p + 2 * p + p

noncomputable def spatialDiscretizationEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  2 * p ^ 2 + (2 * p + 4) * spatialFixedProfileEnvelope p +
    (p + 2 * (2 * p)) * (spatialFixedProfileEnvelope p + 4) + 4 + p * l

noncomputable def spatialMeshEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  p ^ 2 + p * l + 4 * (p + 2 * p) + spatialFixedProfileEnvelope p + 3

noncomputable def spatialLipschitzEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  anisotropicSpatialCapLog p + 2 * spatialFixedProfileEnvelope p

theorem spatialCostEnvelopes_nonneg {p l : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) :
    0 ≤ spatialFixedProfileEnvelope p ∧ 0 ≤ spatialDisplacementEnvelope p ∧
      0 ≤ spatialDiscretizationEnvelope p l ∧ 0 ≤ spatialMeshEnvelope p l ∧
      0 ≤ spatialLipschitzEnvelope p := by
  dsimp only [spatialDisplacementEnvelope, spatialDiscretizationEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope, anisotropicSpatialCapLog]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> positivity

theorem spatialProfileLog_le_fixedEnvelope (j d : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    spatialProfileLog j d p ≤ spatialFixedProfileEnvelope p := by
  have hprofile := probabilityProfileLipschitz_le_comparisonProfileBound
  calc
    _ ≤ (p + 1) * p + p ^ 2 + 2 * p + 2 * p +
        (VectorPolynomial.comparisonProfileBound : ℝ) + 1 := by
      unfold spatialProfileLog
      gcongr
    _ = _ := by unfold spatialFixedProfileEnvelope; ring

theorem spatialDisplacementLog_le_envelope (j d e n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p)
    (he : (e : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) :
    spatialDisplacementLog j d e n p ≤ spatialDisplacementEnvelope p := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  have hprofile0 := spatialProfileLog_nonneg j d hp
  unfold spatialDisplacementLog spatialDisplacementEnvelope
  gcongr

theorem spatialDiscretizationLog_le_envelope (j d : ℕ) {p l : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    spatialDiscretizationLog j d p l ≤ spatialDiscretizationEnvelope p l := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  have hprofile0 := spatialProfileLog_nonneg j d hp
  dsimp only [spatialDiscretizationLog, spatialDiscretizationEnvelope]
  gcongr

theorem anisotropicSpatialMeshLog_le_envelope (j d : ℕ) {p l : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    anisotropicSpatialMeshLog j d p l ≤ spatialMeshEnvelope p l := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  unfold anisotropicSpatialMeshLog spatialMeshEnvelope
  gcongr

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def spatialLipschitzCostEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  p ^ 3 + spatialLipschitzEnvelope p + l + 1

noncomputable def spatialThresholdEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  spatialMeshEnvelope p l + (VectorPolynomial.comparisonProfileBound : ℕ) + 2 * p + l + 16

noncomputable def spatialBoundaryEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  l + (VectorPolynomial.comparisonProfileBound : ℕ) + 3 * p + 25

def spatialMovementEnvelope {A : Type*} [Semiring A] (p l : A) : A := p + l + 2

theorem spatialAuxiliaryDimensions {I G N : Type*} [Fintype I] [Fintype G] [Fintype N]
    (s : I ↪ G) {p : ℝ} (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p) :
    (Fintype.card (UnselectedColumn s) : ℝ) ≤ p ∧
      (Fintype.card (UnselectedColumn s ⊕ N) : ℝ) ≤ 2 * p ∧
      (Fintype.card (Option (G ⊕ N)) : ℝ) ≤ 1 + 2 * p := by
  have he : (Fintype.card (UnselectedColumn s) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hG
  refine ⟨he, ?_, ?_⟩
  · simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  · simp only [Fintype.card_option, Fintype.card_sum, Nat.cast_add, Nat.cast_one]
    linarith

theorem spatialPrimitiveCost_bounds {I G N X : Type*}
    [Fintype I] [Fintype G] [Fintype N] [Fintype X] (s : I ↪ G)
    {M : ℕ} {p l C₀ W Cg Centry : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l)
    (hM : 0 < M) (hMp : (M : ℝ) ≤ Real.exp p)
    (hI : (Fintype.card (Unit ⊕ I) : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    (hN : (Fintype.card N : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hC₀ : 0 ≤ C₀) (hC₀l : C₀ ≤ Real.exp l) (hW : 0 ≤ W) (hWl : W ≤ Real.exp l)
    (_hCg : 0 ≤ Cg) (hCgl : Cg ≤ Real.exp l)
    (hCentry : 0 ≤ Centry) (hCentryl : Centry ≤ Real.exp l) :
    anisotropicSpatialDiscretizationCost N s M C₀ ≤ Real.exp (spatialDiscretizationEnvelope p l) ∧
      Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)) ≤
        Real.exp (spatialLipschitzCostEnvelope p l) ∧
      anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ Real.exp (spatialThresholdEnvelope p l) ∧
      Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X)) ≤
        Real.exp (spatialBoundaryEnvelope p l) ∧
      Fintype.card N * (2 * Centry) ≤ Real.exp (spatialMovementEnvelope p l) ∧
      smoothSpatialDisplacementCost N s M ≤ Real.exp (spatialDisplacementEnvelope p) := by
  obtain ⟨he, hd, hcoords⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hprofile := spatialProfileLog_le_fixedEnvelope (Fintype.card (Unit ⊕ I))
    (Fintype.card (UnselectedColumn s)) hp hI (by linarith)
  have hA := (anisotropicSpatialDiscretizationCost_le_exp N s hp hMp hC₀ hC₀l).trans
    (Real.exp_le_exp.mpr (spatialDiscretizationLog_le_envelope _ _ hp hl hI hd))
  have hB := (smoothSpatialDisplacementCost_le_exp N s hp hMp).trans
    (Real.exp_le_exp.mpr (spatialDisplacementLog_le_envelope _ _ _ _ hp hI hd he hN))
  have hLip : anisotropicSpatialDensityLip s (1 / (M : ℝ)) ≤
      Real.exp (spatialLipschitzEnvelope p) :=
    (anisotropicSpatialDensityLip_le_exp s hp hM hMp hI hG).trans
      (Real.exp_le_exp.mpr (by unfold spatialLipschitzEnvelope; linarith))
  have hLip0 := anisotropicSpatialDensityLip_nonneg s
    (show 0 ≤ 1 / (M : ℝ) by positivity)
  have hK : Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)) ≤
      Real.exp (spatialLipschitzCostEnvelope p l) := by
    have hW1 := one_add_le_exp_succ hl hWl
    calc
      _ ≤ Real.exp (p ^ 3) * (Real.exp (spatialLipschitzEnvelope p) * Real.exp (l + 1)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold spatialLipschitzCostEnvelope; ring
  have hmesh := (anisotropicSpatialMeshThreshold_le_exp N s hp hC₀ hC₀l).trans
    (Real.exp_le_exp.mpr (anisotropicSpatialMeshLog_le_envelope _ _ hp hl hI hd))
  have hP0 : (0 : ℝ) ≤ VectorPolynomial.comparisonProfileBound := Nat.cast_nonneg _
  have hLP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp VectorPolynomial.comparisonProfileBound :=
    probabilityProfileLipschitz_le_comparisonProfileBound.trans
      (by linarith [Real.add_one_le_exp (VectorPolynomial.comparisonProfileBound : ℝ)])
  have hprofileCost : 8 * (probabilityProfileLipschitz : ℝ) ≤
      Real.exp ((VectorPolynomial.comparisonProfileBound : ℝ) + 8) := by
    calc
      _ ≤ Real.exp 8 * Real.exp VectorPolynomial.comparisonProfileBound :=
        mul_le_mul (by linarith [Real.add_one_le_exp (8 : ℝ)]) hLP (NNReal.coe_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hcoordsExp : (Fintype.card (Option (G ⊕ N)) : ℝ) ≤ Real.exp (1 + 2 * p) :=
    hcoords.trans (by linarith [Real.add_one_le_exp (1 + 2 * p)])
  have hXexp : (Fintype.card X : ℝ) ≤ Real.exp p := hX.trans (by linarith [Real.add_one_le_exp p])
  have hNexp : (Fintype.card N : ℝ) ≤ Real.exp p := hN.trans (by linarith [Real.add_one_le_exp p])
  have hshift : 2 * (Fintype.card (Option (G ⊕ N)) : ℝ) * (2 * Centry) ≤
      Real.exp (2 * p + l + 5) := by
    calc
      _ = 4 * Fintype.card (Option (G ⊕ N)) * Centry := by ring
      _ ≤ Real.exp 4 * Real.exp (1 + 2 * p) * Real.exp l := by
        gcongr
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hT : anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
      2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ Real.exp (spatialThresholdEnvelope p l) := by
    let R := spatialMeshEnvelope p l + (VectorPolynomial.comparisonProfileBound : ℝ) + 2 * p + l + 13
    have hm0 := (spatialCostEnvelopes_nonneg hp hl).2.2.2.1
    have h1 := hmesh.trans (Real.exp_le_exp.mpr (show spatialMeshEnvelope p l ≤ R by dsimp [R]; linarith))
    have h2 := hprofileCost.trans (Real.exp_le_exp.mpr
      (show (VectorPolynomial.comparisonProfileBound : ℝ) + 8 ≤ R by dsimp [R]; linarith))
    have h3 := hshift.trans (Real.exp_le_exp.mpr (show 2 * p + l + 5 ≤ R by dsimp [R]; linarith))
    calc
      _ ≤ 3 * Real.exp R := by linarith
      _ ≤ Real.exp 3 * Real.exp R := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (3 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold spatialThresholdEnvelope; dsimp [R]; ring
  have hQ : Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X)) ≤
      Real.exp (spatialBoundaryEnvelope p l) := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp l * (Real.exp 24 * Real.exp VectorPolynomial.comparisonProfileBound *
          (Real.exp (1 + 2 * p) * Real.exp p)) := by
        gcongr
        linarith [Real.add_one_le_exp (24 : ℝ)]
      _ = _ := by simp only [← Real.exp_add]; congr 1; unfold spatialBoundaryEnvelope; ring
  have hD : (Fintype.card N : ℝ) * (2 * Centry) ≤ Real.exp (spatialMovementEnvelope p l) := by
    calc
      _ ≤ Real.exp p * (Real.exp 2 * Real.exp l) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold spatialMovementEnvelope; ring
  exact ⟨hA, hK, hT, hQ, hD, hB⟩

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

noncomputable def normalizedTupleTolerance (X : Type*) [Fintype X] (p E : ℝ) : ℝ :=
  spatialTupleTolerance (Fintype.card X) (Real.exp (p ^ 3 + anisotropicSpatialCapLog p))
    (Real.exp (coefficientErrorVolumeLog p + 4)) (normalizedSpatialShare E / 2)

noncomputable def normalizedTupleNarrowWidth (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ) : ℝ :=
  twoTermErrorWidth (smoothSpatialDisplacementCost N s M) (normalizedTupleTolerance X p E)

noncomputable def normalizedTupleRadius (X : Type*) [Fintype X]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E W : ℝ) : ℝ :=
  twoTermErrorWidth (Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)))
    (normalizedTupleTolerance X p E)

noncomputable def normalizedTupleResolution (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ)
    (p E C₀ W Cg Centry : ℝ) : ℝ :=
  twoTermErrorResolution
    (anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
      2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry))
    (anisotropicSpatialDiscretizationCost N s M C₀) (normalizedTupleTolerance X p E) +
    (Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X))) /
      (normalizedSpatialShare E / 2) +
    (Fintype.card N * (2 * Centry)) / normalizedTupleRadius X s M p E W

theorem normalizedTupleNarrowWidth_pos (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ) :
    0 < normalizedTupleNarrowWidth X N s M p E := by
  have ht : 0 < normalizedTupleTolerance X p E := (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
    (Real.exp_nonneg _) (half_pos (Real.exp_pos (-(E + 2))))).1
  exact (twoTermErrorWidth_spec (smoothSpatialDisplacementCost_nonneg N s M) ht).1

theorem normalizedTupleSpatialChoices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q m M : ℕ} (s : Fin q ↪ G)
    (hM : 0 < M) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) :
    let ξ := normalizedTupleNarrowWidth X N s M p E
    let Qearly := anisotropicTupleEarlyBudget N s p (E + 3)
    0 < ξ ∧ ξ ≤ 1 ∧ ξ⁻¹ ≤ Real.exp (2 * (Qearly + spatialTupleToleranceLog Qearly) + 4) ∧
    ∀ {C₀ W L Cg Centry growth : ℝ}, 0 ≤ C₀ → 0 ≤ W → 1 ≤ L →
      0 ≤ Cg → 0 ≤ Centry → growth ≤ Real.exp p → W ≤ growth * L →
      let δ := normalizedTupleRadius X s M p E W
      let mesh := δ / 4
      let ρ := normalizedTupleResolution X N s M p E C₀ W Cg Centry
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧
        anisotropicSpatialMeshThreshold s N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤
          normalizedSpatialShare E / 2 ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          allocatedTupleSpatialError (Fintype.card X) s N M period C₀ ρ ξ W δ mesh *
            coarseReferenceMassConstant q X W L ≤ normalizedSpatialShare E / 2 := by
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεE : (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
    unfold normalizedSpatialShare
    rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    calc
      _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h := boundedAnisotropicSpatialTuple_error_choices (N := N) (X := X) q s hM hp
    (by linarith : 0 ≤ E + 3) hm hq hG hX hMp hε hεE
  simpa only [normalizedTupleNarrowWidth, normalizedTupleTolerance, normalizedTupleRadius,
    normalizedTupleResolution, allocatedTupleSpatialError, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem canonicalSlicedSpatialChoices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q m M : ℕ} (selection : Fin q ↪ G)
    (hM : 0 < M) {p target : ℝ} (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) :
    let ξ := normalizedTupleNarrowWidth X N selection M p target
    let Qearly := anisotropicTupleEarlyBudget N selection p (target + 3)
    0 < ξ ∧ ξ ≤ 1 ∧ ξ⁻¹ ≤ Real.exp (2 * (Qearly + spatialTupleToleranceLog Qearly) + 4) ∧
    ∀ {C₀ W L Cg Centry growth earlyMesh : ℝ},
      0 ≤ C₀ → 0 ≤ W → 1 ≤ L → 0 ≤ Cg → 0 ≤ Centry →
      growth ≤ Real.exp p → W ≤ growth * L → 0 < earlyMesh →
      let δ := normalizedTupleRadius X selection M p target W
      let ρ := normalizedTupleResolution X N selection M p target C₀ W Cg Centry
      let mesh := min (δ / 4) earlyMesh
      0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧ 0 < mesh ∧
        mesh ≤ earlyMesh ∧ mesh ≤ δ / 4 ∧
        anisotropicSpatialMeshThreshold selection N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤
          normalizedSpatialShare target / 2 ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          allocatedTupleSpatialError (Fintype.card X) selection N M period C₀ ρ ξ W δ mesh *
            coarseReferenceMassConstant q X W L ≤ normalizedSpatialShare target / 2 := by
  intro ξ Qearly
  obtain ⟨hξ, hξ1, hξlog, hchoices⟩ :=
    normalizedTupleSpatialChoices (N := N) (X := X) (m := m) selection hM hp htarget
      hm hq hG hX hMp
  refine ⟨hξ, hξ1, hξlog, ?_⟩
  intro C₀ W L Cg Centry growth earlyMesh hC₀ hW hL hCg hCentry hgrowth hWscale hearlyMesh
    δ ρ mesh
  obtain ⟨hδ, hδ1, hmesh₀, hρ, hthreshold, hρ8, hshift, hmove, hboundary, hsite⟩ :=
    hchoices hC₀ hW hL hCg hCentry hgrowth hWscale
  have hfine : mesh ≤ δ / 4 := min_le_left _ _
  refine ⟨hδ, hδ1, hρ, lt_min hmesh₀ hearlyMesh, min_le_right _ _, hfine,
    hthreshold, hρ8, hshift, hmove, hboundary, ?_⟩
  intro period hperiod
  have hmass : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  exact (mul_le_mul_of_nonneg_right
    (allocatedTupleSpatialError_mono_mesh (Fintype.card X) selection N M period
      hC₀ hρ.le hξ.le hW hδ.le hfine) hmass).trans (hsite period hperiod)

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial

noncomputable def spatialTupleCoarseMesh (n : ℕ) (G V K ε : ℝ) : ℝ :=
  twoTermErrorWidth K (spatialTupleTolerance n G V ε) / 4

theorem spatialTupleCoarseMesh_spec (n : ℕ) {G V K ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hε : 0 < ε) :
    0 < spatialTupleCoarseMesh n G V K ε ∧ spatialTupleCoarseMesh n G V K ε ≤ 1 / 4 ∧
      ∀ {g k v : ℝ}, 0 ≤ g → g ≤ G → 0 ≤ k → k ≤ K → 0 ≤ v → v ≤ V →
        n * (8 * k * spatialTupleCoarseMesh n G V K ε) * (1 + g)^n * v ≤ ε := by
  let t := spatialTupleTolerance n G V ε
  let δ := twoTermErrorWidth K t
  have ht := spatialTupleTolerance_spec n hG hV hε
  have hδ := twoTermErrorWidth_spec hK ht.1
  have ht0 : 0 < t := ht.1
  have hδ0 : 0 < δ := hδ.1
  have hr : 0 < spatialTupleCoarseMesh n G V K ε := div_pos hδ.1 (by norm_num)
  refine ⟨hr, div_le_div_of_nonneg_right hδ.2.1 (by norm_num), ?_⟩
  intro g k v hg hgG hk hkK hv hvV
  have hinner : 8 * k * spatialTupleCoarseMesh n G V K ε ≤ t := by
    have hkδ : k * δ ≤ K * δ := mul_le_mul_of_nonneg_right hkK hδ0.le
    change 8 * k * (δ / 4) ≤ t
    linarith [hδ.2.2]
  have hp : (1 + g)^n ≤ (2 + G)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ n * t * (2 + G)^n * V := by gcongr
    _ = t * (2 + G)^n * (n * V) := by ring
    _ ≤ t * (2 + G)^n * (2 * (n + 1) * (1 + V)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    _ = t * (2 * (n + 1) * (2 + G)^n * (1 + V)) := by ring
    _ ≤ ε := ht.2.2

theorem twoTermErrorWidth_budget_antitone {B C ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 ≤ ε) (hBC : B ≤ C) :
    twoTermErrorWidth C ε ≤ twoTermErrorWidth B ε := by
  unfold twoTermErrorWidth
  apply min_le_min_left
  exact div_le_div_of_nonneg_left hε (by positivity) (by linarith)

theorem normalizedTupleRadius_le_coarse (X : Type*) [Fintype X]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ)
    {growth W : ℝ} (hgrowth : 0 ≤ growth) (hW : growth ≤ W) :
    normalizedTupleRadius X s M p E W / 4 ≤ normalizedTupleRadius X s M p E growth / 4 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  unfold normalizedTupleRadius
  have hlip := anisotropicSpatialDensityLip_nonneg s (show 0 ≤ 1 / (M : ℝ) by positivity)
  apply twoTermErrorWidth_budget_antitone (by positivity)
  · exact (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
      (Real.exp_nonneg _) (half_pos (Real.exp_pos _))).1.le
  · gcongr

theorem normalizedTupleCoarseMesh_budget (X : Type*) [Fintype X]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ)
    {growth : ℝ} (hgrowth : 0 ≤ growth) :
    let coarse := normalizedTupleRadius X s M p E growth / 4
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ {g k v : ℝ}, 0 ≤ g → g ≤ Real.exp (p^3 + anisotropicSpatialCapLog p) →
        0 ≤ k → k ≤ Real.exp (p^3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + growth)) →
        0 ≤ v → v ≤ Real.exp (coefficientErrorVolumeLog p + 4) →
        Fintype.card X * (8 * k * coarse) * (1 + g)^Fintype.card X * v ≤ normalizedSpatialShare E / 2 := by
  have hlip := anisotropicSpatialDensityLip_nonneg s (show 0 ≤ 1 / (M : ℝ) by positivity)
  exact spatialTupleCoarseMesh_spec (Fintype.card X) (Real.exp_nonneg _)
    (Real.exp_nonneg _) (by positivity) (half_pos (Real.exp_pos _))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

theorem allocatedTupleSpatialError_mono_width {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (selection : I ↪ J) (N : Type*) [Fintype N] (M period : ℕ)
    {Czero rho xi small W delta mesh : ℝ}
    (hC : 0 ≤ Czero) (hρ : 0 ≤ rho) (hsmall : 0 ≤ small)
    (hwidth : small ≤ xi) (hW : 0 ≤ W) (hδ : 0 ≤ delta) (hmesh : 0 ≤ mesh) :
    allocatedTupleSpatialError n selection N M period Czero rho small W delta mesh ≤
      allocatedTupleSpatialError n selection N M period Czero rho xi W delta mesh := by
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hE := anisotropicSpatialError_nonneg selection N M hκ hC hρ hsmall
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ
  have hmono : anisotropicSpatialError selection N M (1 / (M : ℝ)) Czero rho small ≤
      anisotropicSpatialError selection N M (1 / (M : ℝ)) Czero rho xi := by
    rw [anisotropicSpatialError_decomposition, anisotropicSpatialError_decomposition]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hwidth (smoothSpatialDisplacementCost_nonneg N selection M))
  have hE' := hE.trans hmono
  unfold allocatedTupleSpatialError
  dsimp only
  gcongr

end Erdos3.VectorPolynomial

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem sharedWidthNormalizedTupleSpatialChoices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q m M : ℕ} (s : Fin q ↪ G)
    (hM : 0 < M) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) {ξ : ℝ}
    (hξ : 0 < ξ) (hξle : ξ ≤ normalizedTupleNarrowWidth X N s M p E) :
    ξ ≤ 1 ∧
    ∀ {C₀ W L Cg Centry growth : ℝ}, 0 ≤ C₀ → 0 ≤ W → 1 ≤ L →
      0 ≤ Cg → 0 ≤ Centry → growth ≤ Real.exp p → W ≤ growth * L →
      let δ := normalizedTupleRadius X s M p E W
      let mesh := δ / 4
      let ρ := normalizedTupleResolution X N s M p E C₀ W Cg Centry
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧
        anisotropicSpatialMeshThreshold s N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤
          normalizedSpatialShare E / 2 ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          allocatedTupleSpatialError (Fintype.card X) s N M period C₀ ρ ξ W δ mesh *
            coarseReferenceMassConstant q X W L ≤ normalizedSpatialShare E / 2 := by
  obtain ⟨_, hcanonical, _, hchoices⟩ := normalizedTupleSpatialChoices
    (N := N) (X := X) (m := m) s hM hp hE hm hq hG hX hMp
  refine ⟨hξle.trans hcanonical, ?_⟩
  intro C₀ W L Cg Centry growth hC₀ hW hL hCg hCentry hgrowth hWscale δ mesh ρ
  obtain ⟨hδ, hδ1, hmesh, hρ, hthreshold, hprofile, hshift, hmove, hboundary, hsite⟩ :=
    hchoices hC₀ hW hL hCg hCentry hgrowth hWscale
  refine ⟨hδ, hδ1, hmesh, hρ, hthreshold, hprofile, hshift, hmove, hboundary, ?_⟩
  intro period hperiod
  have hmass : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile0 := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  exact (mul_le_mul_of_nonneg_right
    (allocatedTupleSpatialError_mono_width (Fintype.card X) s N M period hC₀ hρ.le
      hξ.le hξle hW hδ.le hmesh.le) hmass).trans (hsite period hperiod)

end Erdos3

end

section

namespace Erdos3

noncomputable def spatialPrimitiveEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  p + E + l + 3 + (p ^ 3 + anisotropicSpatialCapLog p) +
    (coefficientErrorVolumeLog p + 4) + spatialDisplacementEnvelope p +
    spatialDiscretizationEnvelope p l + spatialLipschitzCostEnvelope p l +
    spatialThresholdEnvelope p l + spatialBoundaryEnvelope p l + spatialMovementEnvelope p l

noncomputable def spatialParameterBudget {A : Type*} [Semiring A] (p E l : A) : A :=
  let R := spatialPrimitiveEnvelope p E l
  3 * (2 * (R + spatialTupleToleranceLog R) + 4) + 8

theorem spatialPrimitiveEnvelope_bounds {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) :
    let R := spatialPrimitiveEnvelope p E l
    0 ≤ R ∧ p ≤ R ∧ E + 3 ≤ R ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ R ∧
      coefficientErrorVolumeLog p + 4 ≤ R ∧ spatialDisplacementEnvelope p ≤ R ∧
      spatialDiscretizationEnvelope p l ≤ R ∧ spatialLipschitzCostEnvelope p l ≤ R ∧
      spatialThresholdEnvelope p l ≤ R ∧ spatialBoundaryEnvelope p l ≤ R ∧
      spatialMovementEnvelope p l ≤ R := by
  obtain ⟨_, hd, ha, hm, hk⟩ := spatialCostEnvelopes_nonneg hp hl
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hK : 0 ≤ spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope
    positivity
  have hT : 0 ≤ spatialThresholdEnvelope p l := by
    unfold spatialThresholdEnvelope
    positivity
  have hQ : 0 ≤ spatialBoundaryEnvelope p l := by
    unfold spatialBoundaryEnvelope
    positivity
  have hD : 0 ≤ spatialMovementEnvelope p l := by
    unfold spatialMovementEnvelope
    positivity
  dsimp only [spatialPrimitiveEnvelope]
  repeat' constructor
  all_goals linarith

theorem spatialParameterBudget_bounds {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) :
    let R := spatialPrimitiveEnvelope p E l
    let B := 2 * (R + spatialTupleToleranceLog R) + 4
    0 ≤ spatialParameterBudget p E l ∧ B ≤ spatialParameterBudget p E l ∧
      R ≤ B ∧ spatialTupleToleranceLog R ≤ B := by
  have hR := (spatialPrimitiveEnvelope_bounds hp hE hl).1
  have ht := spatialTupleToleranceLog_nonneg hR
  dsimp only [spatialParameterBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_spatialParameterBudget_bound :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p E l : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ l →
      spatialParameterBudget p E l ≤ (p + E + l + a) ^ a := by
  let poly : Polynomial ℕ := spatialParameterBudget Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p E l hp hE hl
  have hpq : p ≤ p + E + l := by linarith
  have hEq : E ≤ p + E + l := by linarith
  have hlq : l ≤ p + E + l := by linarith
  have hmono : spatialParameterBudget p E l ≤
      spatialParameterBudget (p + E + l) (p + E + l) (p + E + l) := by
    dsimp only [spatialParameterBudget, spatialPrimitiveEnvelope, spatialTupleToleranceLog,
      spatialDisplacementEnvelope, spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
      spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
      spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
      coefficientErrorVolumeLog, anisotropicSpatialCapLog]
    gcongr
  apply hmono.trans
  simpa [poly, spatialParameterBudget, spatialPrimitiveEnvelope, spatialTupleToleranceLog,
    spatialDisplacementEnvelope, spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
    spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, Polynomial.eval₂_pow]
    using hbound (p + E + l) (by positivity)

end Erdos3

end

section

namespace Erdos3

section Maps

variable {α β : Type*} [Semiring α] [Semiring β] (f : α →+* β)

@[simp] theorem map_coefficientErrorSpatialLog (p : α) :
    f (coefficientErrorSpatialLog p) = coefficientErrorSpatialLog (f p) := by
  simp [coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
    map_ofNat]

@[simp] theorem map_spatialPrimitiveEnvelope (p E l : α) :
    f (spatialPrimitiveEnvelope p E l) = spatialPrimitiveEnvelope (f p) (f E) (f l) := by
  simp [spatialPrimitiveEnvelope, spatialDisplacementEnvelope,
    spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
    spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, map_ofNat]

@[simp] theorem map_spatialTupleToleranceLog (p : α) :
    f (spatialTupleToleranceLog p) = spatialTupleToleranceLog (f p) := by
  simp [spatialTupleToleranceLog, map_ofNat]

@[simp] theorem map_spatialParameterBudget (p E l : α) :
    f (spatialParameterBudget p E l) = spatialParameterBudget (f p) (f E) (f l) := by
  simp only [spatialParameterBudget, map_add, map_mul, map_ofNat,
    map_spatialPrimitiveEnvelope, map_spatialTupleToleranceLog]

end Maps

theorem coefficientErrorSpatialLog_mono {p p' : ℝ}
    (hp : 0 ≤ p) (hpp : p ≤ p') :
    coefficientErrorSpatialLog p ≤ coefficientErrorSpatialLog p' := by
  have hp' : 0 ≤ p' := hp.trans hpp
  dsimp only [coefficientErrorSpatialLog, coefficientErrorVolumeLog,
    anisotropicSpatialCapLog]
  gcongr

theorem spatialPrimitiveEnvelope_mono {p E l p' E' l' : ℝ}
    (hp : 0 ≤ p) (_hE : 0 ≤ E) (hl : 0 ≤ l)
    (hpp : p ≤ p') (hEE : E ≤ E') (hll : l ≤ l') :
    spatialPrimitiveEnvelope p E l ≤ spatialPrimitiveEnvelope p' E' l' := by
  have hp' : 0 ≤ p' := hp.trans hpp
  dsimp only [spatialPrimitiveEnvelope, spatialDisplacementEnvelope,
    spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
    spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog]
  gcongr

theorem spatialTupleToleranceLog_mono {p p' : ℝ}
    (hp : 0 ≤ p) (hpp : p ≤ p') :
    spatialTupleToleranceLog p ≤ spatialTupleToleranceLog p' := by
  dsimp only [spatialTupleToleranceLog]
  gcongr

theorem spatialParameterBudget_mono {p E l p' E' l' : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hpp : p ≤ p') (hEE : E ≤ E') (hll : l ≤ l') :
    spatialParameterBudget p E l ≤ spatialParameterBudget p' E' l' := by
  have hR := (spatialPrimitiveEnvelope_bounds hp hE hl).1
  have hRR := spatialPrimitiveEnvelope_mono hp hE hl hpp hEE hll
  have hT := spatialTupleToleranceLog_mono hR hRR
  dsimp only [spatialParameterBudget]
  linarith

end Erdos3

end

end OAI
