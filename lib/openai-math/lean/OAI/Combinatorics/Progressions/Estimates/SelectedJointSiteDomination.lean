import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

theorem selectedJointFiniteLaw_site_excess
    {K I X T : Type*} [Fintype K] [Fintype I]
    [Fintype X] [Nonempty X] [Fintype T] [Nonempty T]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (D : (I → ℤ) → (Option K × I → ℤ) → ℝ) (hD : ∀ a z, 0 ≤ D a z)
    (htotal : 0 < selectedJointDensityMass A modulus cells W D)
    (hlower : 1 / 2 ≤ selectedJointDensityMass A modulus cells W D)
    (e : X → I → ℝ) (he : Function.Injective e)
    (root : T → K → ℤ)
    (F : (A × rectangularWeightIndices 0 W 1) → T → X)
    (hF : ∀ z t, e (F z t) = (fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val)
    (hcard : (Fintype.card X : ℝ) / A.card ≤ 2)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ (a : I → ℤ) (t : T) (φ : (I → ℝ) → ℝ),
      (∀ u, φ u ∈ Set.Icc (0 : ℝ) 1) →
      (∑' z, (selectedResidueSmoothPMF modulus cells W hW hZ z).toReal *
        (φ ((fun i => (a i : ℝ)) + physicalAffineSite (root t) z) * D a z)) ≤
      M * (∑' z, (selectedResidueSmoothPMF modulus cells W hW hZ z).toReal *
        φ ((fun i => (a i : ℝ)) + physicalAffineSite (root t) z)) + ε) :
    (FiniteProbabilityWeights.uniform X).excessMass
      ((selectedJointFiniteLaw A hA modulus cells W hW hZ D hD htotal).siteLaw F)
      (4 * M) ≤ 2 * ε := by
  let : Nonempty A := hA.to_subtype
  let q := selectedResidueFiniteLaw modulus cells W hW hZ
  apply FiniteProbabilityWeights.siteLaw_excessMass_le_of_test_bound
  intro φ hφ t
  let ψ : (I → ℝ) → ℝ := fun u => φ (Function.invFun e u)
  have hψ (u) : ψ u ∈ Set.Icc (0 : ℝ) 1 := hφ _
  have hvalue (z : A × rectangularWeightIndices 0 W 1) :
      ψ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val) = φ (F z t) := by
    rw [← hF z t]
    exact congrArg φ (Function.leftInverse_invFun he (F z t))
  have hinj (z : rectangularWeightIndices 0 W 1) :
      Function.Injective (fun a : A => F (a, z) t) := by
    intro a b hab
    have hc := congrArg e hab
    rw [hF, hF] at hc
    have hd := add_right_cancel hc
    apply Subtype.ext
    funext i
    exact_mod_cast congrFun hd i
  have hlocal' (a : A) :
      q.mean (fun z => D a.val z.val * φ (F (a, z) t)) ≤
        M * q.mean (fun z => φ (F (a, z) t)) + ε := by
    have h := hlocal a.val t ψ hψ
    rw [← selectedResidueFiniteLaw_mean, ← selectedResidueFiniteLaw_mean] at h
    have hv (z : rectangularWeightIndices 0 W 1) :
        ψ ((fun i => (a.val i : ℝ)) + physicalAffineSite (root t) z.val) = φ (F (a, z) t) :=
      hvalue (a, z)
    simpa only [hv, mul_comm] using h
  have hz : 0 < ((FiniteProbabilityWeights.uniform A).prod q).mean
      (fun z => D z.1.val z.2.val) := by
    change 0 < (selectedJointReference A hA modulus cells W hW hZ).mean _
    rw [selectedJointReference_densityMass]
    exact htotal
  have hl : 1 / 2 ≤ ((FiniteProbabilityWeights.uniform A).prod q).mean
      (fun z => D z.1.val z.2.val) := by
    change 1 / 2 ≤ (selectedJointReference A hA modulus cells W hW hZ).mean _
    rw [selectedJointReference_densityMass]
    exact hlower
  have h := FiniteProbabilityWeights.uniform_base_reweight_test_le q
    (fun z => D z.1.val z.2.val) (fun z => hD z.1.val z.2.val) hz
    (fun z => F z t) hinj φ (fun x => (hφ x).1) hM (by norm_num : (0 : ℝ) < 1 / 2)
    hl hlocal'
  change (selectedJointFiniteLaw A hA modulus cells W hW hZ D hD htotal).mean
    (fun z => φ (F z t)) ≤ _ at h
  apply h.trans
  have hn := (FiniteProbabilityWeights.uniform X).mean_nonneg (fun x => (hφ x).1)
  have hr : (Fintype.card X : ℝ) / Fintype.card A ≤ 2 := by simpa using hcard
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hM) hn
  nlinarith

end Erdos3

end

end OAI
