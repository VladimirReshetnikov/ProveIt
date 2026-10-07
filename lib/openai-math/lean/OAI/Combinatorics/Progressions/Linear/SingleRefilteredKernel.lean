import OAI.Combinatorics.Progressions.Estimates.RefilteredReconstructionDiagram

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

noncomputable def refilteredComponentMap (b : ι) :
    ((pi D).filtration.gradedRefiltrationSubalgebra W) →ₗ⁅ℚ⁆ L b :=
  (liePiEval b).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl

noncomputable def nativeRefilteredTarget
    (Q : RationalFilteredNilmanifold
      (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n) :=
  optionProduct (Q.raiseStep (Nat.le_succ s)) (fun i : {i : ι // i ≠ a} => D i.val)

noncomputable def nativeRefilteredMap :=
  optionProductMap (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
    (fun i : {i : ι // i ≠ a} => refilteredComponentMap D W i.val)

theorem nativeRefilteredMap_real_kernel
    (Q : RationalFilteredNilmanifold
      (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
    (hEF : E.filtration = (pi D).filtration.gradedRefiltration W)
    (x : ℝ ⊗[ℚ] ((pi D).filtration.gradedRefiltrationSubalgebra W)) :
    realificationLieHom (nativeRefilteredMap D a W E) x = 0 ↔
      realificationLieHom (refilteredReconstructionMap D a W) x = 0 := by
  rw [refilteredReconstructionMap_real_kernel]
  dsimp only [nativeRefilteredMap]
  rw [topQuotientOtherMap_real_kernel E Q (fun i : {i : ι // i ≠ a} => D i.val)]
  have htop : x ∈ E.filtration.realification.layer (s + 1) ↔
      realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x ∈
        (pi D).filtration.realGradedRefiltrationLayer W (s + 1) := by
    rw [hEF]
    exact (pi D).filtration.mem_native_refiltration_layer W (s + 1) x
  have hcomp (i : ι) : realificationLieHom (refilteredComponentMap D W i) x =
      realificationLieHom (liePiEval i)
        (realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x) := by
    change (((liePiEval i).toLinearMap.comp
      ((pi D).filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ) x = _
    rw [LinearMap.baseChange_comp]
    rfl
  apply and_congr htop
  constructor
  · intro h i hi
    exact (hcomp i) ▸ h ⟨i, hi⟩
  · intro h i
    exact (hcomp i.val).symm ▸ h i.val i.property

theorem native_refiltered_frozen_invariant {J : Type*}
    (Q : RationalFilteredNilmanifold
      (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
    (hEF : E.filtration = (pi D).filtration.gradedRefiltration W)
    (eta : J → ∀ i, L i →ₗ[ℚ] ℚ) (S : (D a).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
      (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x)
    (hfrequency : ∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
      realifyFunctional (piFrequency (eta j)) x = 0)
    (l r : (D a).RealGroup) (z x : E.RealGroup)
    (hz : realificationLieHom (nativeRefilteredMap D a W E) z.coord = 0) :
    let φ := NilpotentLieBCHGroup.realificationMap
      (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
    S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r)) := by
  let φ := NilpotentLieBCHGroup.realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
  let z' : (pi D).RealGroup := NilpotentLieBCHGroup.realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi D).filtration.lowerCentralSeries_eq_bot)
    ((pi D).filtration.gradedRefiltrationSubalgebra W).incl z
  obtain ⟨htop, hother⟩ := (refilteredReconstructionMap_real_kernel D a W z.coord).mp
    ((nativeRefilteredMap_real_kernel D a W E Q hEF z.coord).mp hz)
  have hproj : φ z = productProjectionHom D a z' := by
    apply NilpotentLieBCHGroup.ext
    change (((liePiEval a).toLinearMap.comp
      ((pi D).filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ) z.coord = _
    rw [LinearMap.baseChange_comp]
    rfl
  have hzlayer : φ z ∈ (D a).filtration.realification.subgroup (s + 1) := by
    rw [hproj]
    exact productProjectionHom_mem_layer D a (s + 1) z'
      ((pi D).filtration.realGradedRefiltrationLayer_le W (s + 1) htop)
  have hinv : ∀ y, S (φ z • y) = S y := by
    rw [hproj]
    apply refiltered_product_kernel_invariant D a W eta S hinvariant hfrequency z' htop
    intro i hi
    apply NilpotentLieBCHGroup.ext
    exact hother i hi
  have hcomm := (D a).filtration.realification.top_commutes (φ z) hzlayer l
  change S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r))
  rw [map_mul]
  have heq : l * (φ z * φ x) * r = φ z * (l * φ x * r) := by
    calc
      l * (φ z * φ x) * r = (l * φ z) * φ x * r := by simp only [mul_assoc]
      _ = (φ z * l) * φ x * r := by rw [hcomm.eq]
      _ = φ z * (l * φ x * r) := by simp only [mul_assoc]
  rw [heq]
  exact hinv (QuotientGroup.mk (l * φ x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

theorem singleRefilteredQuotient_real_kernel
    (hEF : E.filtration = D.filtration.gradedRefiltration W)
    (x : ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra W) :
    realificationLieHom (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x = 0 ↔
      realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl x ∈
        D.filtration.realGradedRefiltrationLayer W (s + 1) := by
  change (E.filtration.layerIdeal (s + 1)).toSubmodule.mkQ.baseChange ℝ x = 0 ↔ _
  rw [realification_mkQ_eq_zero_iff]
  change x ∈ E.filtration.realification.layer (s + 1) ↔ _
  rw [hEF]
  exact D.filtration.mem_native_refiltration_layer W (s + 1) x

theorem single_refiltered_frozen_invariant
    (hEF : E.filtration = D.filtration.gradedRefiltration W)
    (S : D.Space → ℂ)
    (hinvariant : ∀ z : D.RealGroup,
      z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
        ∀ x, S (z • x) = S x)
    (l r : D.RealGroup) (z x : E.RealGroup)
    (hz : realificationLieHom (lieQuotientMap (E.filtration.layerIdeal (s + 1))) z.coord = 0) :
    let φ := NilpotentLieBCHGroup.realificationMap
      (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra W).incl
    S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r)) := by
  let φ := NilpotentLieBCHGroup.realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra W).incl
  have htop : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) :=
    (singleRefilteredQuotient_real_kernel D W E hEF z.coord).mp hz
  have hzlayer : φ z ∈ D.filtration.realification.subgroup (s + 1) :=
    D.filtration.realGradedRefiltrationLayer_le W (s + 1) htop
  have hcomm := D.filtration.realification.top_commutes (φ z) hzlayer l
  change S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r))
  rw [map_mul]
  have heq : l * (φ z * φ x) * r = φ z * (l * φ x * r) := by
    calc
      l * (φ z * φ x) * r = (l * φ z) * φ x * r := by simp only [mul_assoc]
      _ = (φ z * l) * φ x * r := by rw [hcomm.eq]
      _ = φ z * (l * φ x * r) := by simp only [mul_assoc]
  rw [heq]
  exact hinvariant (φ z) htop (QuotientGroup.mk (l * φ x * r))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
