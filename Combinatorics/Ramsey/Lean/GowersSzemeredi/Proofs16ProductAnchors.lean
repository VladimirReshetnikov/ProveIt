import GowersSzemeredi.Proofs16AnchoredFibres

/-! # Transporting the anchored good set to product cells -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem appendCoordinate_pair_injective {N k : Nat} :
    Function.Injective (fun z : Point N k × ZMod N => appendCoordinate z.1 z.2) := by
  intro a b hab
  apply Prod.ext
  · simpa only [section16Init_appendCoordinate] using congrArg section16Init hab
  · simpa only [section16Last_appendCoordinate] using congrArg section16Last hab

theorem mem_lastProductSet_append {N k : Nat} [NeZero N]
    (A : Finset (Point N k)) (J : Finset (ZMod N)) (h : Point N k) (x : ZMod N) :
    appendCoordinate h x ∈ lastProductSet A J ↔ h ∈ A ∧ x ∈ J := by
  simp [lastProductSet]

/-- The finite-space sampling construction on an actual product of a
base set and a column set. Both anchors remain in the partial domain and
in the new good subset of the product. -/
theorem section16_product_anchored_good_set {N k q r : Nat} [Fact N.Prime]
    (A : Finset (Point N k)) (J : Finset (ZMod N))
    (D : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h ∈ A, ∀ t, LinearOn Finset.univ (ell h t))
    (hcover : ∀ h ∈ A, ∀ x ∈ J, appendCoordinate h x ∈ D →
      ∃ t, phi (appendCoordinate h x) = ell h t x)
    (σ : ℝ) (hq : 0 < q) (hσ : 0 < σ)
    (hlong : 2 * (q : ℝ) ≤ σ * J.card)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ) :
    ∃ (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))),
      (∀ i, sample i ∈ J) ∧ F ⊆ lastProductSet A J ∧
      (1 - 2 * σ) * ((lastProductSet A J).card : ℝ) ≤ F.card ∧
      ∀ h x, appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
        ∃ i j, appendCoordinate h (sample i) ∈ D ∧ appendCoordinate h (sample j) ∈ D ∧
          appendCoordinate h (sample i) ∈ F ∧ appendCoordinate h (sample j) ∈ F ∧
          sample i ≠ sample j ∧
          phi (appendCoordinate h x) = (sample i - sample j)⁻¹ *
            ((phi (appendCoordinate h (sample i)) + (-1) * phi (appendCoordinate h (sample j))) * x +
              ((-sample j) * phi (appendCoordinate h (sample i)) +
                sample i * phi (appendCoordinate h (sample j)))) := by
  have hJ : J.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.cast_zero, mul_zero] at hlong; linarith [(Nat.cast_pos.mpr hq : (0 : ℝ) < q)])
  letI : Nonempty J := hJ.to_subtype
  let B : A → Finset J := fun h => Finset.univ.filter
    (fun x => appendCoordinate h.val x.val ∈ D)
  obtain ⟨sample, G, hmass, hanchors⟩ := section16_affine_cover_anchored_good_set
    (fun x : J => x.val) Subtype.val_injective B (fun h x => phi (appendCoordinate h.val x.val))
    (fun h => ell h.val) (fun h t => hell h.val h.property t)
    (fun h x hx => hcover h.val h.property x.val x.property (Finset.mem_filter.mp hx).2)
    σ hq hσ (by simpa using hlong) hr
  let embed : A × J → Point N (k + 1) := fun z => appendCoordinate z.1.val z.2.val
  have hinj : Function.Injective embed :=
    appendCoordinate_pair_injective.comp (Subtype.val_injective.prodMap Subtype.val_injective)
  have hsub : G.image embed ⊆ lastProductSet A J := Finset.image_subset_iff.mpr fun z _ =>
    (mem_lastProductSet_append A J _ _).mpr ⟨z.1.property, z.2.property⟩
  refine ⟨fun i => (sample i).val, G.image embed, fun i => (sample i).property, hsub, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, lastProductSet_card]
    simpa only [Fintype.card_coe, Nat.cast_mul, mul_assoc] using hmass
  · intro h x hxD hxF
    obtain ⟨hh, hx⟩ := (mem_lastProductSet_append A J h x).mp (hsub hxF)
    obtain ⟨i, j, hiB, hjB, hiG, hjG, hij, heq⟩ := hanchors ⟨h, hh⟩ ⟨x, hx⟩
      (hinj.mem_finset_image.mp hxF) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxD⟩)
    exact ⟨i, j, (Finset.mem_filter.mp hiB).2, (Finset.mem_filter.mp hjB).2,
      Finset.mem_image_of_mem embed hiG, Finset.mem_image_of_mem embed hjG, hij, heq⟩

end LeanProofs.GowersSzemeredi
