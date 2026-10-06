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
  classical
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
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ ^ 2) :
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
  classical
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hz
    have hz' : J.card = 0 := by omega
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [hz', Nat.cast_zero, mul_zero] at hlong
    linarith
  letI : Nonempty J := hJ.to_subtype
  let B : A → Finset J := fun h => Finset.univ.filter
    (fun x => appendCoordinate h.val x.val ∈ D)
  let f : A → J → ZMod N := fun h x => phi (appendCoordinate h.val x.val)
  have hcov : ∀ h x, x ∈ B h → ∃ t, f h x = ell h.val t x.val := by
    intro h x hx
    exact hcover h.val h.property x.val x.property (Finset.mem_filter.mp hx).2
  obtain ⟨sample, G, hmass, hanchors⟩ := section16_affine_cover_anchored_good_set
    (fun x : J => x.val) Subtype.val_injective B f (fun h => ell h.val)
    (fun h t => hell h.val h.property t) hcov σ hq hσ (by simpa using hlong) hr
  let embed : A × J → Point N (k + 1) := fun z => appendCoordinate z.1.val z.2.val
  have hinj : Function.Injective embed := by
    intro a b hab
    have hp : (a.1.val, a.2.val) = (b.1.val, b.2.val) := appendCoordinate_pair_injective hab
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hp)
    · exact Subtype.ext (congrArg Prod.snd hp)
  have hsub : G.image embed ⊆ lastProductSet A J := by
    intro z hz
    obtain ⟨⟨h, x⟩, _, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_lastProductSet_append A J h.val x.val).mpr ⟨h.property, x.property⟩
  refine ⟨fun i => (sample i).val, G.image embed, fun i => (sample i).property, hsub, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, lastProductSet_card]
    simpa only [Fintype.card_coe, Nat.cast_mul, mul_assoc] using hmass
  · intro h x hxD hxF
    obtain ⟨hh, hx⟩ := (mem_lastProductSet_append A J h x).mp (hsub hxF)
    let hp : A := ⟨h, hh⟩
    let xp : J := ⟨x, hx⟩
    have hG : (hp, xp) ∈ G := by
      obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hxF
      have hz' : z = (hp, xp) := hinj heq
      exact hz' ▸ hz
    have hB : xp ∈ B hp := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxD⟩
    obtain ⟨i, j, hiB, hjB, hiG, hjG, hij, heq⟩ := hanchors hp xp hG hB
    refine ⟨i, j, (Finset.mem_filter.mp hiB).2, (Finset.mem_filter.mp hjB).2,
      ?_, ?_, hij, heq⟩
    · exact Finset.mem_image.mpr ⟨(hp, sample i), hiG, rfl⟩
    · exact Finset.mem_image.mpr ⟨(hp, sample j), hjG, rfl⟩

end LeanProofs.GowersSzemeredi
