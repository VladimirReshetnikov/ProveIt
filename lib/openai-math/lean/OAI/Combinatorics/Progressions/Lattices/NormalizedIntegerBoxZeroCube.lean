import OAI.Combinatorics.Progressions.Estimates.SampledCommonSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def integerBoxCubeProductEquiv {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ) (q : ℕ) :
    SupportedCube q (integerBox N : Set (I → ℤ)) ≃
      (∀ i, SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))) where
  toFun c i := ⟨(fun j => c.val.1 j i, c.val.2 i), by
    intro ω
    have h := (mem_integerBox N _).mp (c.property ω) i
    simpa only [Set.mem_Ico, Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply] using h⟩
  invFun c := ⟨(fun j i => (c i).val.1 j, fun i => (c i).val.2), by
    intro ω
    apply (mem_integerBox N _).mpr
    intro i
    have h := (c i).property ω
    simpa only [Set.mem_Ico, Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply] using h⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by funext i; apply Subtype.ext; rfl

theorem integerBoxCubeCount_eq_product {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ) (q : ℕ) :
    integerBoxCubeCount N q = ∏ i, Nat.card (SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))) := by
  classical
  rw [integerBoxCubeCount, Nat.card_congr (integerBoxCubeProductEquiv N q)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi]

theorem integerScalarCubeWeights_supported_complexMean (q L : ℕ) (hL : 0 < L)
    (f : ((Fin q → ℤ) × ℤ) → ℂ) :
    (integerScalarCubeWeights (Fin q) L hL).complexMean
        (fun x => f (fun i => (x (some i) : ℤ), (x none : ℤ))) =
      𝔼 p : SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)), f p.val := by
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re, expect_re] using
      integerScalarCubeWeights_supported_mean q L hL (fun p => (f p).re)
  · have h := integerScalarCubeWeights_supported_mean q L hL (fun p => (f p).im)
    simpa only [FiniteProbabilityWeights.complexMean, FiniteProbabilityWeights.mean,
      Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, expect_im] using h

theorem FiniteProbabilityWeights.pi_uniform_complexMean
    {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (f : (∀ i, A i) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (A i))).complexMean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, A i, ((∏ i, (Fintype.card (A i) : ℝ)⁻¹ : ℝ) : ℂ) * f x) = _
  have hcard : (∏ i, (Fintype.card (A i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, A i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

theorem integerScalarCubeProduct_complexMean {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ)
    (hN : ∀ i, 0 < N i) (q : ℕ)
    (f : ((Fin q → I → ℤ) × (I → ℤ)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights (Fin q) (N i) (hN i))).complexMean
      (fun c => f (fun j i => (c i (some j) : ℤ), fun i => (c i none : ℤ))) =
      𝔼 c : SupportedCube q (integerBox N : Set (I → ℤ)), f c.val := by
  let : ∀ i, Nonempty (SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))) := fun i =>
    ⟨⟨(0, 0), by
      intro ω
      simpa [cubeShift] using (show (0 : ℤ) < N i by exact_mod_cast hN i)⟩⟩
  let law := fun i => FiniteProbabilityWeights.uniform
    (SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ)))
  have hcoordinate (i : I) (g : ((Fin q → ℤ) × ℤ) → ℂ) :
      (integerScalarCubeWeights (Fin q) (N i) (hN i)).complexMean
        (fun c => g (fun j => (c (some j) : ℤ), (c none : ℤ))) =
      (law i).complexMean (fun c => g c.val) := by
    rw [FiniteProbabilityWeights.uniform_complexMean]
    exact integerScalarCubeWeights_supported_complexMean q (N i) (hN i) g
  calc
    _ = (FiniteProbabilityWeights.pi law).complexMean
        (fun c => f (fun j i => (c i).val.1 j, fun i => (c i).val.2)) :=
      FiniteProbabilityWeights.complexMean_pi_transport_fintype
        (fun i => integerScalarCubeWeights (Fin q) (N i) (hN i)) law
        (fun _ c => (fun j => (c (some j) : ℤ), (c none : ℤ)))
        (fun _ c => c.val) hcoordinate
        (fun c => f (fun j i => (c i).1 j, fun i => (c i).2))
    _ = 𝔼 c : (∀ i, SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))),
        f (fun j i => (c i).val.1 j, fun i => (c i).val.2) :=
      FiniteProbabilityWeights.pi_uniform_complexMean _
    _ = (𝔼 c : SupportedCube q (integerBox N : Set (I → ℤ)), f c.val) := by
      exact (Fintype.expect_equiv (integerBoxCubeProductEquiv N q)
        (fun c => f c.val)
        (fun c => f (fun j i => (c i).val.1 j, fun i => (c i).val.2))
        (fun _ => rfl)).symm

theorem normalizedSupportedCubeSum_eq_scalarProduct {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ)
    (hN : ∀ i, 0 < N i) (q : ℕ) (F : (Fin q → Bool) → (I → ℤ) → ℂ) :
    normalizedSupportedCubeSum q (integerBox N) F =
      (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights (Fin q) (N i) (hN i))).complexMean
        (fun c => mixedCubeProduct F (fun j i => (c i (some j) : ℤ)) (fun i => (c i none : ℤ))) := by
  rw [integerScalarCubeProduct_complexMean N hN q (fun c => mixedCubeProduct F c.1 c.2)]
  simp only [normalizedSupportedCubeSum, supportedCubeSum,
    Fintype.expect_eq_sum_div_card, Nat.card_eq_fintype_card]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCubeWeights_zero_product_complexMean
    {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (f : (X → ℤ) → ℂ) :
    (FiniteProbabilityWeights.pi
      (fun i => integerScalarCubeWeights Empty (N i) (hN i))).complexMean
        (fun z => f (fun i => (z i none : ℤ))) =
      𝔼 u ∈ integerBox N, f u := by
  let : ∀ i, Nonempty (Finset.Ico (0 : ℤ) (N i : ℤ)) := fun i =>
    ⟨⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hN i⟩⟩⟩
  calc
    _ = (FiniteProbabilityWeights.pi
        (fun i => intervalUniformWeights 0 (N i : ℤ)
          (by exact_mod_cast hN i))).complexMean
            (fun z => f (fun i => (z i : ℤ))) :=
      FiniteProbabilityWeights.complexMean_pi_transport_fintype
        (fun i => integerScalarCubeWeights Empty (N i) (hN i))
        (fun i => intervalUniformWeights 0 (N i : ℤ) (by exact_mod_cast hN i))
        (fun _ z => (z none : ℤ)) (fun _ z => (z : ℤ))
        (fun i g => integerScalarCubeWeights_zero_complexMean Empty (N i) (hN i) g) f
    _ = 𝔼 z : (∀ i, Finset.Ico (0 : ℤ) (N i : ℤ)),
        f (fun i => (z i : ℤ)) := by
      exact FiniteProbabilityWeights.pi_uniform_complexMean _
    _ = 𝔼 z : integerBox N, f z.val :=
      Fintype.expect_equiv (finiteBoxPointsEquiv (fun i => Finset.Ico (0 : ℤ) (N i : ℤ)))
        _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
        Fintype.card_coe, Finset.sum_coe_sort]

end Erdos3

end

end OAI
