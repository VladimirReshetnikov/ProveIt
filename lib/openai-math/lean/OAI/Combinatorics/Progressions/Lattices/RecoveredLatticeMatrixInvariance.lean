import OAI.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer
import OAI.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I E : Type*} [Fintype D] [Fintype I] [Fintype E] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def recoveredIntegerTransverse : (D → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun β i := standardLatticeCoordinates W bW b hb β (Sum.inl i)
  map_add' β γ := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' q β := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

noncomputable def recoveredIntegerDeck : (D → ℤ) →ₗ[ℤ] (E → ℤ) where
  toFun β i := standardLatticeCoordinates W bW b hb β (Sum.inr i)
  map_add' β γ := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' q β := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem recoveredIntegerTransverse_projection (β : D → ℤ) :
    Wᗮ.orthogonalProjectionOnto (standardEuclideanPoint D β).val =
      -b.equivFun.symm (fun i => (recoveredIntegerTransverse W bW b hb β i : ℝ)) :=
  standardLatticeCoordinates_projection W bW b hb β

theorem recoveredIntegerTransverse_normalized (β : D → ℤ) (i : Fin n) :
    (normalizedOrthogonalChart W b (standardEuclideanPoint D β).val).2 i =
      -(recoveredIntegerTransverse W bW b hb β i : ℝ) / basisAxisScale b i := by
  rw [normalizedOrthogonalChart_apply, recoveredIntegerTransverse_projection W bW b hb β,
    map_neg, LinearEquiv.apply_symm_apply]
  rfl

theorem recoveredIntegerDeck_reconstruction (β : D → ℤ) :
    (standardEuclideanPoint D β).val +
        (standardLatticeIntegerLift W b hb (recoveredIntegerTransverse W bW b hb β)).val =
      (bW.equivFun.symm (recoveredIntegerDeck W bW b hb β)).val.val :=
  standardLatticeCoordinates_reconstruction W bW b hb β

theorem recoveredIntegerTransverse_of_mem (ℓ : D → ℤ)
    (hℓ : (standardEuclideanPoint D ℓ).val ∈ W) :
    recoveredIntegerTransverse W bW b hb ℓ = 0 := by
  have hp := recoveredIntegerTransverse_projection W bW b hb ℓ
  rw [W.orthogonalProjectionOnto_orthogonal_apply_eq_zero hℓ] at hp
  have hz : (fun i => (recoveredIntegerTransverse W bW b hb ℓ i : ℝ)) = 0 := by
    apply b.equivFun.symm.injective
    simpa only [map_zero] using neg_eq_zero.mp hp.symm
  funext i
  have hi := congrFun hz i
  simp only [Pi.zero_apply] at hi ⊢
  exact_mod_cast hi

theorem recoveredIntegerDeck_of_mem (ℓ : D → ℤ)
    (hℓ : (standardEuclideanPoint D ℓ).val ∈ W) :
    recoveredIntegerDeck W bW b hb ℓ =
      bW.equivFun ⟨⟨(standardEuclideanPoint D ℓ).val, hℓ⟩,
        (standardEuclideanPoint D ℓ).property⟩ := by
  have hr := recoveredIntegerDeck_reconstruction W bW b hb ℓ
  rw [recoveredIntegerTransverse_of_mem W bW b hb ℓ hℓ, map_zero,
    Submodule.coe_zero, add_zero] at hr
  apply bW.equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  exact hr.symm

theorem recoveredIntegerTransverse_add_retained (β ℓ : D → ℤ) (q : ℤ)
    (hℓ : (standardEuclideanPoint D ℓ).val ∈ W) :
    recoveredIntegerTransverse W bW b hb (β + q • ℓ) =
      recoveredIntegerTransverse W bW b hb β := by
  rw [map_add, map_zsmul, recoveredIntegerTransverse_of_mem W bW b hb ℓ hℓ,
    smul_zero, add_zero]

theorem recoveredIntegerDeck_add_retained (β ℓ : D → ℤ) (q : ℤ)
    (hℓ : (standardEuclideanPoint D ℓ).val ∈ W) :
    recoveredIntegerDeck W bW b hb (β + q • ℓ) =
      recoveredIntegerDeck W bW b hb β +
        q • bW.equivFun ⟨⟨(standardEuclideanPoint D ℓ).val, hℓ⟩,
          (standardEuclideanPoint D ℓ).property⟩ := by
  rw [map_add, map_zsmul, recoveredIntegerDeck_of_mem W bW b hb ℓ hℓ]

variable (o : OrthonormalBasis I ℝ W)

noncomputable def recoveredMixedCoordinates (y : EuclideanSpace ℝ D) (β : D → ℤ) :
    (I → ℝ) × (Fin n → ℤ) :=
  ((mixedRealCoordinates W b o y).1, recoveredIntegerTransverse W bW b hb β)

theorem recoveredMixedCoordinates_add (y y' : EuclideanSpace ℝ D) (β β' : D → ℤ) :
    recoveredMixedCoordinates W bW b hb o (y + y') (β + β') =
      recoveredMixedCoordinates W bW b hb o y β +
        recoveredMixedCoordinates W bW b hb o y' β' := by
  simp only [recoveredMixedCoordinates, map_add, Prod.fst_add, Prod.mk_add_mk]

theorem recoveredMixedCoordinates_zsmul (q : ℤ) (y : EuclideanSpace ℝ D) (β : D → ℤ) :
    recoveredMixedCoordinates W bW b hb o (q • y) (q • β) =
      q • recoveredMixedCoordinates W bW b hb o y β := by
  simp only [recoveredMixedCoordinates, map_zsmul, Prod.smul_fst, Prod.smul_mk]

theorem recoveredMixedCoordinates_add_retained (y : EuclideanSpace ℝ D)
    (β ℓ : D → ℤ) (q : ℤ) (hℓ : (standardEuclideanPoint D ℓ).val ∈ W) :
    recoveredMixedCoordinates W bW b hb o y (β + q • ℓ) =
      recoveredMixedCoordinates W bW b hb o y β := by
  unfold recoveredMixedCoordinates
  rw [recoveredIntegerTransverse_add_retained W bW b hb β ℓ q hℓ]

theorem recoveredMixedCoordinates_real (y : EuclideanSpace ℝ D) (β : D → ℤ)
    (hy : y + (standardEuclideanPoint D β).val ∈ W) :
    mixedRealCoordinates W b o y =
      ((recoveredMixedCoordinates W bW b hb o y β).1,
        fun i => ((recoveredMixedCoordinates W bW b hb o y β).2 i : ℝ) /
          basisAxisScale b i) := by
  refine Prod.ext (by rfl) ?_
  have hp := W.orthogonalProjectionOnto_orthogonal_apply_eq_zero hy
  rw [map_add, recoveredIntegerTransverse_projection W bW b hb β] at hp
  have hp' := eq_of_sub_eq_zero (show Wᗮ.orthogonalProjectionOnto y -
      b.equivFun.symm (fun i => (recoveredIntegerTransverse W bW b hb β i : ℝ)) = 0 by
    simpa only [sub_eq_add_neg] using hp)
  funext i
  change (normalizedOrthogonalChart W b y).2 i = _
  rw [normalizedOrthogonalChart_apply, hp', LinearEquiv.apply_symm_apply]
  rfl

theorem recoveredMixedCoordinates_point (y : EuclideanSpace ℝ D) (β : D → ℤ)
    (hy : y + (standardEuclideanPoint D β).val ∈ W) :
    normalizedLatticePoint W b
      (orthonormalMixedChart o (recoveredMixedCoordinates W bW b hb o y β)) = y := by
  rw [← mixedRealPoint_integer]
  rw [← recoveredMixedCoordinates_real W bW b hb o y β hy]
  exact mixedRealPoint_coordinates W b o y

theorem recoveredMixedCoordinates_deck (y : EuclideanSpace ℝ D) (β : D → ℤ)
    (hy : y + (standardEuclideanPoint D β).val ∈ W) :
    normalizedLatticeRepresentative W b hb
        (orthonormalMixedChart o (recoveredMixedCoordinates W bW b hb o y β)) +
        (bW.equivFun.symm (recoveredIntegerDeck W bW b hb β)).val =
      ⟨y + (standardEuclideanPoint D β).val, hy⟩ := by
  apply Subtype.ext
  rw [normalizedDeckPoint_identity,
    recoveredMixedCoordinates_point W bW b hb o y β hy]
  congr 3
  apply (standardLatticeCoordinates W bW b hb).injective
  rw [latticeDeckInteger_coordinates]
  funext i
  cases i <;> rfl

end Erdos3

end

section

namespace Erdos3

open Module Submodule

theorem recoveredIntegerLift_linear_residue {T : Type*} {d a : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] (T → ℤ))
    (M : Fin d → Fin a → ℤ) (N : ℕ) [NeZero N]
    (hM : ∀ i j, (N : ℤ) ∣ M i j) (β : Fin d → ℤ) (k : Fin a → ℤ) :
    integerResidueMap T N (f (recoveredIntegerLift M β k)) =
      integerResidueMap T N (f β) := by
  obtain ⟨A, _, hA⟩ := exists_bounded_integerMap_residue_matrix f N
  rw [hA, hA]
  congr 1
  exact recoveredIntegerLift_residue M N hM β k

variable {m d a : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def layerIntegerRestriction (e : Fin d ≃ Sigma J) (j : Fin m) :
    (Fin d → ℤ) →ₗ[ℤ] (J j → ℤ) where
  toFun β i := β (e.symm ⟨j, i⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def recoveredLayeredIntegerLift (e : Fin d ≃ Sigma J)
    (M : Fin d → Fin a → ℤ) (β : Sigma J → ℤ) (k : Fin a → ℤ) : Sigma J → ℤ :=
  fun i => recoveredIntegerLift M (fun i => β (e i)) k (e.symm i)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

theorem recoveredIntegerTransverse_layer_matrix
    (e : Fin d ≃ Sigma J) (M : Fin d → Fin a → ℤ)
    (hcol : ∀ j t, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j, i⟩) t)).val ∈ euclideanSubspace (U j))
    (β : Sigma J → ℤ) (k : Fin a → ℤ) (j : Fin m) :
    recoveredIntegerTransverse (euclideanSubspace (U j)) (bW j) (b j) (hb j)
        (fun i => recoveredLayeredIntegerLift e M β k ⟨j, i⟩) =
      recoveredIntegerTransverse (euclideanSubspace (U j)) (bW j) (b j) (hb j)
        (fun i => β ⟨j, i⟩) := by
  let π : (Fin d → ℤ) →+ (Fin (n j) → ℤ) :=
    (recoveredIntegerTransverse (euclideanSubspace (U j)) (bW j) (b j) (hb j)).toAddMonoidHom.comp
      (layerIntegerRestriction e j).toAddMonoidHom
  have hπ (t : Fin a) : π (fun i => M i t) = 0 :=
    recoveredIntegerTransverse_of_mem (euclideanSubspace (U j)) (bW j) (b j) (hb j)
      (fun i => M (e.symm ⟨j, i⟩) t) (hcol j t)
  have h := recoveredIntegerLift_projection M π hπ (fun i => β (e i)) k
  simpa only [π, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    layerIntegerRestriction, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply,
    recoveredLayeredIntegerLift] using h

theorem standardLatticeCoordinates_layer_matrix_residue
    (e : Fin d ≃ Sigma J) (M : Fin d → Fin a → ℤ) (N : ℕ) [NeZero N]
    (hdiv : ∀ i t, (N : ℤ) ∣ M i t)
    (β : Sigma J → ℤ) (k : Fin a → ℤ) (j : Fin m) :
    integerResidueMap (Fin (n j) ⊕ E j) N
        (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)
          (fun i => recoveredLayeredIntegerLift e M β k ⟨j, i⟩)) =
      integerResidueMap (Fin (n j) ⊕ E j) N
        (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)
          (fun i => β ⟨j, i⟩)) := by
  let f := (standardLatticeCoordinates (euclideanSubspace (U j))
    (bW j) (b j) (hb j)).toLinearMap.comp (layerIntegerRestriction e j)
  have h := recoveredIntegerLift_linear_residue f M N hdiv (fun i => β (e i)) k
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    layerIntegerRestriction, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply,
    recoveredLayeredIntegerLift] using h

end Erdos3

end

end OAI
