import GowersSzemeredi.Proofs16BohrDenseDifference

/-! Weak regularity of Bohr sets in `ℤ/N`, `N` prime.

Milićević's Lemmas 2.7 and 2.8 (arXiv:2601.01682) perturb the radius to
make `|B(Γ,ρ′+η) ∖ B(Γ,ρ′−η)| ≤ ε|G|`. The perturbation exists only for
characters with a small image. In `ℤ/N` with `N` prime there is none to
worry about:
* each nonzero frequency `γ` makes `x ↦ γx` a bijection;
* the zero frequency never leaves the band around `0`.

So no perturbation is needed. `bohr_annulus_card_le` proves
`|B(K;ρ+η) ∖ B(K;ρ−η)| ≤ |K|·(4ηN + 2)` for `0 ≤ ρ − η`. The band count
`band_card_le` maps each `y` to the sign and absolute value of its
centered representative; that map is injective. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **Band count.** At most `2(b − a + 1)` residues have centered absolute
value in `(a, b]`, for `0 ≤ a ≤ b`. -/
theorem band_card_le {N : Nat} [NeZero N] {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Finset.univ.filter fun y : ZMod N =>
      a < (centeredAbs y : Real) ∧ (centeredAbs y : Real) ≤ b).card : Real) ≤ 2 * (b - a + 1) := by
  set S := Finset.univ.filter fun y : ZMod N => a < (centeredAbs y : Real) ∧ (centeredAbs y : Real) ≤ b
  let f : ZMod N → Nat × Bool := fun y => (y.valMinAbs.natAbs, decide (0 ≤ y.valMinAbs))
  have hinj : Set.InjOn f S := by
    intro y hy z hz hyz
    simp only [f, Prod.mk.injEq] at hyz
    obtain ⟨habs, hsign⟩ := hyz
    have hv : y.valMinAbs = z.valMinAbs := by
      rcases Int.natAbs_eq y.valMinAbs with h1 | h1 <;> rcases Int.natAbs_eq z.valMinAbs with h2 | h2
      · rw [h1, h2, habs]
      · by_cases hy0 : 0 ≤ y.valMinAbs
        · have hz0 : 0 ≤ z.valMinAbs := by simpa [hy0] using hsign
          omega
        · have hz0 : ¬ 0 ≤ z.valMinAbs := by simpa [hy0] using hsign
          omega
      · by_cases hy0 : 0 ≤ y.valMinAbs
        · have hz0 : 0 ≤ z.valMinAbs := by simpa [hy0] using hsign
          omega
        · have hz0 : ¬ 0 ≤ z.valMinAbs := by simpa [hy0] using hsign
          omega
      · rw [h1, h2, habs]
    have := congrArg (fun v : Int => (v : ZMod N)) hv
    simpa only [ZMod.coe_valMinAbs] using this
  have hmaps : ∀ y ∈ S, f y ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) ×ˢ (Finset.univ : Finset Bool) := by
    intro y hy
    obtain ⟨hlo, hhi⟩ := (Finset.mem_filter.mp hy).2
    refine Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · exact (Nat.floor_lt ha).mpr hlo
    · exact Nat.le_floor hhi
  have hcard : S.card ≤ 2 * (⌊b⌋₊ - ⌊a⌋₊) := by
    calc S.card ≤ ((Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) ×ˢ (Finset.univ : Finset Bool)).card :=
          Finset.card_le_card_of_injOn f hmaps hinj
      _ = 2 * (⌊b⌋₊ - ⌊a⌋₊) := by
          rw [Finset.card_product, Nat.card_Ioc, Finset.card_univ, Fintype.card_bool]; ring
  have hfl : ((⌊b⌋₊ - ⌊a⌋₊ : Nat) : Real) ≤ b - a + 1 := by
    have h1 : (⌊b⌋₊ : Real) ≤ b := Nat.floor_le (ha.trans hab)
    have h2 : a < (⌊a⌋₊ : Real) + 1 := Nat.lt_floor_add_one a
    have h3 : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
    rw [Nat.cast_sub h3]
    linarith
  calc (S.card : Real) ≤ ((2 * (⌊b⌋₊ - ⌊a⌋₊) : Nat) : Real) := by exact_mod_cast hcard
    _ = 2 * ((⌊b⌋₊ - ⌊a⌋₊ : Nat) : Real) := by push_cast; ring
    _ ≤ 2 * (b - a + 1) := by linarith

/-- **Weak regularity in `ℤ/N`.** -/
theorem bohr_annulus_card_le {N : Nat} [NeZero N] [Fact N.Prime] (K : Finset (ZMod N))
    {ρ η : Real} (hη : 0 ≤ η) (hρη : 0 ≤ ρ - η) :
    ((bohr K (ρ + η) \ bohr K (ρ - η)).card : Real) ≤ K.card * (4 * η * N + 2) := by
  have hNR : (0 : Real) ≤ N := Nat.cast_nonneg N
  -- the annulus lies in the union of the bands of the frequencies
  let band : ZMod N → Finset (ZMod N) := fun γ => Finset.univ.filter fun x =>
    (ρ - η) * N < (centeredAbs (γ * x) : Real) ∧ (centeredAbs (γ * x) : Real) ≤ (ρ + η) * N
  have hsub : bohr K (ρ + η) \ bohr K (ρ - η) ⊆ K.biUnion band := by
    intro x hx
    obtain ⟨hxbig, hxsmall⟩ := Finset.mem_sdiff.mp hx
    have hall := (Finset.mem_filter.mp hxbig).2
    have hnot : ¬ ∀ r ∈ K, (centeredAbs (r * x) : Real) ≤ (ρ - η) * N := by
      intro h
      exact hxsmall (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    push Not at hnot
    obtain ⟨γ, hγ, hlo⟩ := hnot
    exact Finset.mem_biUnion.mpr ⟨γ, hγ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo, hall γ hγ⟩⟩
  have hband : ∀ γ ∈ K, ((band γ).card : Real) ≤ 4 * η * N + 2 := by
    intro γ _
    by_cases hγ : γ = 0
    · -- the zero frequency has an empty band
      have : band γ = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro x _ ⟨hlo, _⟩
        rw [hγ, zero_mul] at hlo
        simp only [centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero] at hlo
        have : 0 ≤ (ρ - η) * N := mul_nonneg hρη hNR
        linarith
      rw [this, Finset.card_empty, Nat.cast_zero]
      positivity
    · -- multiplication by a nonzero frequency is a bijection
      have himage : (band γ).image (fun x => γ * x) = Finset.univ.filter fun y : ZMod N =>
          (ρ - η) * N < (centeredAbs y : Real) ∧ (centeredAbs y : Real) ≤ (ρ + η) * N := by
        ext y
        simp only [band, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hx
        · intro hy
          refine ⟨γ⁻¹ * y, ?_, mul_inv_cancel_left₀ hγ y⟩
          rw [mul_inv_cancel_left₀ hγ y]
          exact hy
      have hinj : Function.Injective fun x : ZMod N => γ * x := by
        intro x y hxy
        exact mul_left_cancel₀ hγ hxy
      rw [← Finset.card_image_of_injective _ hinj, himage]
      have h := band_card_le (N := N) (mul_nonneg hρη hNR)
        (by nlinarith : (ρ - η) * N ≤ (ρ + η) * N)
      calc _ ≤ 2 * ((ρ + η) * N - (ρ - η) * N + 1) := h
        _ = 4 * η * N + 2 := by ring
  calc ((bohr K (ρ + η) \ bohr K (ρ - η)).card : Real) ≤ ((K.biUnion band).card : Real) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ γ ∈ K, ((band γ).card : Real) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _γ ∈ K, (4 * η * N + 2) := Finset.sum_le_sum hband
    _ = K.card * (4 * η * N + 2) := by rw [Finset.sum_const, nsmul_eq_mul]

end LeanProofs.GowersSzemeredi
