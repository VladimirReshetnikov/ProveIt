import GowersSzemeredi.Proofs13FejerRelations

/-! Selection uses each physical vertex once. The labelled Fourier expansion
is a lower bound for repeated vertices and is exact for injective labels. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem labelled_probability_le_carrier_probability {I X : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq X]
    (vertex : I → X) (p : X → Real) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) :
    ∏ i, p (vertex i) ≤ ∏ x ∈ Finset.univ.image vertex, p x := by
  rw [Finset.prod_comp p vertex]
  apply Finset.prod_le_prod
  · intro x hx
    exact pow_nonneg (hp0 x) _
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have hc : 1 ≤ (Finset.univ.filter fun i => vertex i = x).card := by
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simpa only [pow_one] using pow_le_pow_of_le_one (hp0 x) (hp1 x) hc

theorem fejer_kernel_mean_carrier_lower {N L : Nat} [NeZero N]
    {I X : Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
    (hL : 0 < L) (vertex : I → X) (phi feature : X → ZMod N) :
    (((L : Real) ^ 2)⁻¹) ^ Fintype.card I *
      (countWhere (fun v : I → Fin L × Fin L =>
        fejerPairRelation v (phi ∘ vertex) = 0 ∧
          fejerPairRelation v (feature ∘ vertex) = 0) : Real) ≤
      𝔼 c : ZMod N × ZMod N,
        ∏ x ∈ Finset.univ.image vertex,
          finiteFejerKernel L (c.1 * phi x + c.2 * feature x) := by
  calc
    _ = 𝔼 c : ZMod N × ZMod N,
        ∏ i, finiteFejerKernel L (c.1 * phi (vertex i) + c.2 * feature (vertex i)) :=
      (finiteFejerKernel_mean_product_real (phi ∘ vertex) (feature ∘ vertex)).symm
    _ ≤ _ := by
      apply Finset.expect_le_expect
      intro c _
      exact labelled_probability_le_carrier_probability vertex
        (fun x => finiteFejerKernel L (c.1 * phi x + c.2 * feature x))
        (fun x => finiteFejerKernel_nonneg _) (fun x => finiteFejerKernel_le_one hL _)

theorem fejer_kernel_mean_carrier_of_injective {N L : Nat} [NeZero N]
    {I X : Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
    (vertex : I → X) (hinj : Function.Injective vertex) (phi feature : X → ZMod N) :
    (𝔼 c : ZMod N × ZMod N,
      ∏ x ∈ Finset.univ.image vertex,
        finiteFejerKernel L (c.1 * phi x + c.2 * feature x)) =
      (((L : Real) ^ 2)⁻¹) ^ Fintype.card I *
        (countWhere (fun v : I → Fin L × Fin L =>
          fejerPairRelation v (phi ∘ vertex) = 0 ∧
            fejerPairRelation v (feature ∘ vertex) = 0) : Real) := by
  simp_rw [Finset.prod_image hinj.injOn]
  exact finiteFejerKernel_mean_product_real (phi ∘ vertex) (feature ∘ vertex)

end LeanProofs.GowersSzemeredi
