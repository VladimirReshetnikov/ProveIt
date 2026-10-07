import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Geometry.RightCosetMetricMap

namespace OAI

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

theorem rightCosetEDist_left_mul_le (Γ : Subgroup G) (a : G) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x => a * x)) (x y : G) :
    rightCosetEDist Γ (a * x) (a * y) ≤ C * rightCosetEDist Γ x y := by
  unfold rightCosetEDist
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro γ
  apply (iInf_le (fun δ : Γ => edist (a * x) (a * y * δ)) γ).trans
  simpa only [mul_assoc] using hLip x (y * γ)

variable [IsIsometricSMul Gᵐᵒᵖ G]

theorem quotientRightEDist_left_smul_le (Γ : Subgroup G) (a : G) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x => a * x)) (x y : G ⧸ Γ) :
    quotientRightEDist Γ (a • x) (a • y) ≤ C * quotientRightEDist Γ x y :=
  Quotient.inductionOn₂ x y (rightCosetEDist_left_mul_le Γ a hLip)

theorem quotientRightEDist_orbit_le (Γ : Subgroup G) (x : G ⧸ Γ) (a b : G) :
    quotientRightEDist Γ (a • x) (b • x) ≤ edist a b := by
  induction x using Quotient.inductionOn with
  | h x =>
    exact (quotientRightEDist_mk_le Γ (a * x) (b * x)).trans_eq (edist_mul_right a b x)

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem lipschitz_quotient_left_smul (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (a : G) {C : ℝ≥0} (hLip : LipschitzWith C (fun x => a * x)) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith C (fun x : G ⧸ Γ => a • x) := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  exact quotientRightEDist_left_smul_le Γ a hLip x y

theorem lipschitz_quotient_orbit (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (x : G ⧸ Γ) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith 1 (fun a : G => a • x) := by
  let := rightCosetMetricSpace Γ hΓ
  intro a b
  change quotientRightEDist Γ (a • x) (b • x) ≤ 1 * edist a b
  simpa only [one_mul] using quotientRightEDist_orbit_le Γ x a b

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G X : Type*} [Group G] [MetricSpace G]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] [PseudoEMetricSpace X]

theorem rightCosetMetricSpace_lipschitz_lift (Γ : Subgroup G)
    (hΓ : IsClosed (Γ : Set G)) (f : G ⧸ Γ → X) {C : ℝ≥0}
    (hf : LipschitzWith C (fun x : G => f (QuotientGroup.mk x))) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith C f := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      rw [rightCosetMetricSpace_edist_mk, ENNReal.mul_iInf (by simp)]
      apply le_iInf
      intro γ
      simpa only [quotient_mk_mul_mem] using hf x (y * γ)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G]

theorem central_smul_eq_self_of_mem (Γ : Subgroup G) {g : G}
    (hg : g ∈ Γ) (hc : ∀ a : G, Commute g a) (x : G ⧸ Γ) : g • x = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change (QuotientGroup.mk (g * a) : G ⧸ Γ) = QuotientGroup.mk a
    rw [(hc a).eq]
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using Γ.inv_mem hg

variable [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem isometry_quotient_central_smul (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (hc : ∀ a : G, Commute g a) :
    letI := rightCosetMetricSpace Γ hΓ
    Isometry (fun x : G ⧸ Γ => g • x) := by
  let := rightCosetMetricSpace Γ hΓ
  have hgroup : LipschitzWith 1 (fun a : G => g * a) := by
    have heq : (fun a : G => g * a) = (fun a : G => a * g) := funext (fun a => (hc a).eq)
    rw [heq]
    exact (isometry_mul_right g).lipschitzWith
  have hinv : LipschitzWith 1 (fun a : G => g⁻¹ * a) := by
    have heq : (fun a : G => g⁻¹ * a) = (fun a : G => a * g⁻¹) :=
      funext (fun a => (hc a).inv_left.eq)
    rw [heq]
    exact (isometry_mul_right g⁻¹).lipschitzWith
  have hforward := lipschitz_quotient_left_smul Γ hΓ g hgroup
  have hback := lipschitz_quotient_left_smul Γ hΓ g⁻¹ hinv
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using hforward.dist_le_mul x y
  · simpa only [inv_smul_smul, NNReal.coe_one, one_mul] using hback.dist_le_mul (g • x) (g • y)

end Erdos3

end

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

def frozenCosetMap (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (a r : H)
    (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ) : (G ⧸ Γ) → (H ⧸ Λ) :=
  Quotient.map (fun x => a * φ x * r) (fun {x y} hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    have heq : (a * φ x * r)⁻¹ * (a * φ y * r) = r⁻¹ * φ (x⁻¹ * y) * r := by
      rw [map_mul, map_inv]
      group
    rw [heq]
    exact h (x⁻¹ * y) (QuotientGroup.leftRel_apply.mp hxy))

@[simp] theorem frozenCosetMap_mk (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (a r : H)
    (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ) (x : G) :
    frozenCosetMap Γ Λ φ a r h (QuotientGroup.mk x) = QuotientGroup.mk (a * φ x * r) := rfl

open scoped NNReal

variable [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem lipschitz_frozenCosetMap (Γ : Subgroup G) (Λ : Subgroup H)
    (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
    (φ : G →* H) (a r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)
    {A C : ℝ≥0} (hφ : LipschitzWith C φ) (ha : LipschitzWith A (fun x => a * x)) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    LipschitzWith (A * C) (frozenCosetMap Γ Λ φ a r h) := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  apply rightCosetMetricSpace_lipschitz_lift Γ hΓ
  have hf : LipschitzWith (A * C) (fun x : G => a * φ x * r) := by
    simpa only [one_mul, Function.comp_def] using
      (isometry_mul_right r).lipschitzWith.comp (ha.comp hφ)
  simpa only [one_mul, Function.comp_def, frozenCosetMap_mk] using
    (rightCosetMetricSpace_lipschitz_mk Λ hΛ).comp hf

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (Γ : Subgroup G) (Λ : Subgroup H)
  (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
  (φ : G →* H) (r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)

omit [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] in
theorem frozenCosetMap_dist_left (a b : H) (x : G ⧸ Γ) :
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h x) ≤ dist a b := by
  let := rightCosetMetricSpace Λ hΛ
  induction x using Quotient.inductionOn with
  | h x =>
    have hLip := lipschitz_quotient_orbit Λ hΛ (QuotientGroup.mk (φ x * r))
    simpa only [NNReal.coe_one, one_mul, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_assoc, frozenCosetMap_mk] using hLip.dist_le_mul a b

theorem frozenCosetMap_dist_le (a b : H) {A C : ℝ≥0}
    (hφ : LipschitzWith C φ) (ha : LipschitzWith A (fun x => a * x)) (x y : G ⧸ Γ) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h y) ≤
      (A * C : ℝ≥0) * dist x y + dist a b := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  exact (dist_triangle _ (frozenCosetMap Γ Λ φ a r h y) _).trans
    (add_le_add ((lipschitz_frozenCosetMap Γ Λ hΓ hΛ φ a r h hφ ha).dist_le_mul x y)
      (frozenCosetMap_dist_left Γ Λ hΛ φ r h a b y))

end Erdos3

end

end OAI
