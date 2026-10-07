import OAI.Combinatorics.Progressions.Geometry.SpatialTupleErrorBudget
import OAI.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem physicalSpatialInverseBound_eq_scalar (I : Type*) [Fintype I] (M : ℕ) :
    physicalSpatialInverseBound I (1 / (M : ℝ)) = scalarSpatialInverseAllowance I M := by
  simp [physicalSpatialInverseBound, scalarSpatialInverseAllowance, div_eq_mul_inv,
    Fintype.card_sum, Nat.add_comm]

noncomputable def anisotropicSpatialDiscretizationCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) (C : ℝ) : ℝ :=
  smoothSpatialDiscretizationCost N s M 1 * C ^ Fintype.card (Unit ⊕ I)

theorem anisotropicSpatialDiscretizationCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ anisotropicSpatialDiscretizationCost N s M C :=
  mul_nonneg (smoothSpatialDiscretizationCost_nonneg N s M 1) (pow_nonneg hC _)

theorem anisotropicSpatialError_decomposition {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) (C ρ ξ : ℝ) :
    anisotropicSpatialError s N M (1 / (M : ℝ)) C ρ ξ =
      anisotropicSpatialDiscretizationCost N s M C / ρ +
        smoothSpatialDisplacementCost N s M * ξ := by
  unfold anisotropicSpatialError
  rw [physicalSpatialInverseBound_eq_scalar]
  unfold anisotropicSpatialDiscretizationCost smoothSpatialDiscretizationCost
    smoothSpatialDisplacementCost anisotropicSpatialDetAllowance scalarSpatialIndexAllowance
  simp only [Nat.cast_one, one_pow, mul_one]
  ring

theorem anisotropicSpatialDiscretizationCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {C p l : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) (hC : 0 ≤ C) (hCl : C ≤ Real.exp l) :
    anisotropicSpatialDiscretizationCost N s M C ≤
      Real.exp (spatialDiscretizationLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p l) := by
  have hb := smoothSpatialDiscretizationCost_le_exp N s hp hM
    (show ((1 : ℕ) : ℝ) ≤ Real.exp 0 by simp)
  unfold anisotropicSpatialDiscretizationCost
  calc
    _ ≤ Real.exp (spatialDiscretizationLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p 0) *
        (Real.exp l) ^ Fintype.card (Unit ⊕ I) :=
      mul_le_mul hb (pow_le_pow_left₀ hC hCl _) (pow_nonneg hC _) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold spatialDiscretizationLog
      ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem anisotropicSpatialTuple_error_choices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] (q : ℕ) (s : Fin q ↪ G)
    {M : ℕ} (hM : 0 < M) {Csp Vsp ε : ℝ}
    (hCsp : 0 ≤ Csp) (hVsp : 0 ≤ Vsp) (hε : 0 < ε) :
    let B := smoothSpatialDisplacementCost N s M
    let t := spatialTupleTolerance (Fintype.card X) Csp Vsp ε
    let ξ := twoTermErrorWidth B t
    0 < ξ ∧ ξ ≤ 1 ∧
    ∀ (period : ℕ) {C₀ W L Cg Centry : ℝ}, 0 ≤ C₀ → 0 ≤ W → 0 < L →
      0 ≤ Cg → 0 ≤ Centry →
      (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
        anisotropicSpatialDensityCap s (1 / (M : ℝ)) ≤ Csp →
      coarseReferenceMassConstant q X W L ≤ Vsp →
      let Γ := (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q)
      let K := Γ * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W))
      let A := anisotropicSpatialDiscretizationCost N s M C₀
      let T := anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry)
      let Q := Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X))
      let D := Fintype.card N * (2 * Centry)
      let δ := twoTermErrorWidth K t
      let mesh := δ / 4
      let ρ := twoTermErrorResolution T A t + Q / ε + D / δ
      let E₁ := anisotropicSpatialError s N M (1 / (M : ℝ)) C₀ ρ ξ + K * δ
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧
        anisotropicSpatialMeshThreshold s N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤ ε ∧
        Fintype.card X * (E₁ + 4 * K * mesh) *
          (1 + Γ * anisotropicSpatialDensityCap s (1 / (M : ℝ)) + E₁) ^ Fintype.card X *
            coarseReferenceMassConstant q X W L ≤ ε := by
  intro B t ξ
  have hc := spatialTupleErrorChoices (Fintype.card X) hCsp hVsp
    (smoothSpatialDisplacementCost_nonneg N s M) hε
  refine ⟨hc.1, hc.2.1, ?_⟩
  intro period C₀ W L Cg Centry hC₀ hW hL hCg hCentry hcap hmass
    Γ K A T Q D δ mesh ρ E₁
  have hκ : 0 ≤ 1 / (M : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hM)).le
  have hcap0 := anisotropicSpatialDensityCap_nonneg s hκ
  have hlip0 := anisotropicSpatialDensityLip_nonneg s hκ
  have hA : 0 ≤ A := anisotropicSpatialDiscretizationCost_nonneg N s M hC₀
  have hK : 0 ≤ K := by dsimp [K, Γ]; positivity
  have hmesh0 : 0 ≤ anisotropicSpatialMeshThreshold s N C₀ := by
    unfold anisotropicSpatialMeshThreshold anisotropicSpatialDetAllowance
    positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hδ, hδ1, hmesh, hρ, hTρ, hmove, hquad, hsite⟩ :=
    hc.2.2 (A := A) (K := K) (T := T) (Q := Q) (D := D) hA hK hT hQ hD
  have hshift0 : 0 ≤ 2 * (Fintype.card (Option (G ⊕ N)) : ℝ) * (2 * Centry) := by positivity
  have hprofile0 : 0 ≤ (probabilityProfileLipschitz : ℝ) := NNReal.coe_nonneg _
  have hthreshold : anisotropicSpatialMeshThreshold s N C₀ ≤ T := by dsimp [T]; linarith
  have hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ T := by dsimp [T]; linarith
  have hshift : 2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ T := by
    dsimp [T]
    linarith [show 0 ≤ (probabilityProfileLipschitz : ℝ) from NNReal.coe_nonneg _]
  have hquad' : Cg *
      (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤ ε := by
    calc
      _ = Q / ρ := by dsimp only [Q]; ring
      _ ≤ ε := hquad
  refine ⟨hδ, hδ1, hmesh, hρ, hthreshold.trans hTρ, hprofile.trans hTρ,
    hshift.trans hTρ, hmove, hquad', ?_⟩
  have hmass0 : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile0 := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  have hactualCap0 : 0 ≤ Γ * anisotropicSpatialDensityCap s (1 / (M : ℝ)) := by
    dsimp [Γ]
    positivity
  have hresult := hsite hactualCap0 hcap hmass0 hmass
  dsimp only at hresult
  simpa only [E₁, anisotropicSpatialError_decomposition] using hresult

end Erdos3

end

end OAI
