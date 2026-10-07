import OAI.Combinatorics.Progressions.Estimates.RightCosetEDistance

namespace OAI

section

namespace Erdos3

open Set
open scoped ENNReal Topology

variable {G : Type*} [Group G] [PseudoEMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]

theorem quotientRightEDist_image_eball (Γ : Subgroup G) (x : G) (r : ℝ≥0∞) :
    (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball x r =
      {y | quotientRightEDist Γ (QuotientGroup.mk x) y < r} := by
  ext y
  induction y using Quotient.inductionOn with
  | h y =>
    constructor
    · rintro ⟨w, hw, hwq⟩
      change (QuotientGroup.mk w : G ⧸ Γ) = QuotientGroup.mk y at hwq
      change quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) < r
      rw [← hwq]
      apply (quotientRightEDist_mk_le Γ x w).trans_lt
      simpa only [Metric.mem_eball, edist_comm] using hw
    · intro hy
      change (⨅ γ : Γ, edist x (y * γ)) < r at hy
      obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hy
      refine ⟨y * γ, ?_, quotient_mk_mul_mem Γ y γ⟩
      simpa only [Metric.mem_eball, edist_comm] using hγ

variable [IsTopologicalGroup G]

theorem quotientRightEDist_nhds_basis (Γ : Subgroup G) (x : G ⧸ Γ) :
    (𝓝 x).HasBasis (fun r : ℝ≥0∞ => 0 < r) (fun r => {y | quotientRightEDist Γ x y < r}) := by
  induction x using Quotient.inductionOn with
  | h x =>
    rw [QuotientGroup.nhds_eq]
    simpa only [quotientRightEDist_image_eball] using
      (Metric.nhds_basis_eball (x := x)).map (QuotientGroup.mk : G → G ⧸ Γ)

@[instance_reducible]
noncomputable def rightCosetPseudoEMetricSpace (Γ : Subgroup G) : PseudoEMetricSpace (G ⧸ Γ) :=
  PseudoEMetricSpace.ofEDistOfTopology (quotientRightEDist Γ)
    (quotientRightEDist_self Γ) (quotientRightEDist_comm Γ) (quotientRightEDist_triangle Γ)
    (quotientRightEDist_nhds_basis Γ)

theorem rightCosetPseudoEMetricSpace_topology (Γ : Subgroup G) :
    (rightCosetPseudoEMetricSpace Γ).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (G ⧸ Γ)) := rfl

@[instance_reducible]
noncomputable def rightCosetEMetricSpace (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    EMetricSpace (G ⧸ Γ) := by
  letI := rightCosetPseudoEMetricSpace Γ
  letI := hΓ
  exact EMetricSpace.ofT0PseudoEMetricSpace (G ⧸ Γ)

theorem rightCosetEMetricSpace_topology (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    (rightCosetEMetricSpace Γ hΓ).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (G ⧸ Γ)) := rfl

end Erdos3

namespace Erdos3

open Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

@[instance_reducible]
noncomputable def rightCosetMetricSpace (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    MetricSpace (G ⧸ Γ) := by
  letI := rightCosetEMetricSpace Γ hΓ
  apply EMetricSpace.toMetricSpace
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact ne_top_of_le_ne_top (edist_ne_top x y) (quotientRightEDist_mk_le Γ x y)

theorem rightCosetMetricSpace_topology (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    (rightCosetMetricSpace Γ hΓ).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (G ⧸ Γ)) := rfl

theorem rightCosetMetricSpace_edist_mk (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (x y : G) :
    letI := rightCosetMetricSpace Γ hΓ
    edist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = ⨅ γ : Γ, edist x (y * γ) := rfl

theorem rightCosetMetricSpace_lipschitz_mk (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith 1 (QuotientGroup.mk : G → G ⧸ Γ) := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  change quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) ≤ 1 * edist x y
  simpa only [one_mul] using quotientRightEDist_mk_le Γ x y

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G H : Type*} [Group G] [Group H]

def cosetMap (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (hφ : Γ ≤ Λ.comap φ) :
    (G ⧸ Γ) → (H ⧸ Λ) :=
  Quotient.map φ (fun {a b} h => by
    apply QuotientGroup.leftRel_apply.mpr
    have hm := hφ (QuotientGroup.leftRel_apply.mp h)
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hm)

@[simp] theorem cosetMap_mk (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (x : G) :
    cosetMap Γ Λ φ hφ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

theorem cosetMap_surjective (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (hsurj : Function.Surjective φ) :
    Function.Surjective (cosetMap Γ Λ φ hφ) := by
  intro y
  induction y using Quotient.inductionOn with
  | h y =>
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨QuotientGroup.mk x, rfl⟩

variable [PseudoEMetricSpace G] [PseudoEMetricSpace H]

theorem rightCosetEDist_map_le (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) (x y : G) :
    rightCosetEDist Λ (φ x) (φ y) ≤ C * rightCosetEDist Γ x y := by
  unfold rightCosetEDist
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro γ
  let δ : Λ := ⟨φ γ, hφ γ.property⟩
  calc
    (⨅ a : Λ, edist (φ x) (φ y * a)) ≤ edist (φ x) (φ y * δ) := iInf_le _ δ
    _ = edist (φ x) (φ (y * γ)) := by simp only [δ, map_mul]
    _ ≤ C * edist x (y * γ) := hLip x (y * γ)

variable [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]

theorem quotientRightEDist_map_le (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) (x y : G ⧸ Γ) :
    quotientRightEDist Λ (cosetMap Γ Λ φ hφ x) (cosetMap Γ Λ φ hφ y) ≤
      C * quotientRightEDist Γ x y :=
  Quotient.inductionOn₂ x y (rightCosetEDist_map_le Γ Λ φ hφ hLip)

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem lipschitz_cosetMap (Γ : Subgroup G) (Λ : Subgroup H)
    (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
    (φ : G →* H) (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    LipschitzWith C (cosetMap Γ Λ φ hφ) := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  intro x y
  exact quotientRightEDist_map_le Γ Λ φ hφ hLip x y

end Erdos3

end

end OAI
