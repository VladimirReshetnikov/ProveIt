import GowersSzemeredi.Proofs16SplitProfile
import GowersSzemeredi.Proofs16BohrAnnulus

/-! In prime `ℤ/N` every mixed Bohr set is weakly regular, so the radius
selection of [49] Theorem 33 ((10)–(12)) is unnecessary.

* `mixedBohr_band_le`: `|B(γ; a+c)| ≤ |B(γ; a−c)| + |ι|(4c+2)` for `c ≤ aᵢ`.
  A point of the annulus has some frequency in its band
  `aᵢ − c < |γᵢx| ≤ aᵢ + c`. The zero frequency never is. A nonzero
  frequency permutes `ℤ/N`, and at most `4c + 2` residues have centered
  value in a band of width `2c` (`band_card_le`).
* `split_profile_quasirandom_prime`: `split_profile_quasirandom` with all
  three band hypotheses discharged at
  `ε = |ι ⊕ (κ ⊕ κ)|(4c+2)/N`. What remains is relation splitting for
  typical vertices and pairs, the truncation budget, and
  `20εN ≤ |B(γ; a−c)|`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **Mixed Bohr sets are weakly regular in prime `ℤ/N`.** -/
theorem mixedBohr_band_le {N : Nat} [NeZero N] [Fact N.Prime] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) (a : ι → Nat) (c : Nat) (hca : ∀ i, c ≤ a i) :
    ((mixedBohr γ (fun i => a i + c)).card : Real) ≤
      (mixedBohr γ (fun i => a i - c)).card + Fintype.card ι * (4 * c + 2) := by
  let band : ι → Finset (ZMod N) := fun i => Finset.univ.filter fun x =>
    a i - c < centeredAbs (γ i * x) ∧ centeredAbs (γ i * x) ≤ a i + c
  have hsub : mixedBohr γ (fun i => a i + c) \ mixedBohr γ (fun i => a i - c) ⊆
      Finset.univ.biUnion band := by
    intro x hx
    obtain ⟨hbig, hsmall⟩ := Finset.mem_sdiff.mp hx
    rw [mem_mixedBohr] at hbig hsmall
    push Not at hsmall
    obtain ⟨i, hi⟩ := hsmall
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hbig i⟩⟩
  have hband : ∀ i, ((band i).card : Real) ≤ 4 * c + 2 := by
    intro i
    by_cases hγ : γ i = 0
    · have : band i = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro x _ ⟨hlo, _⟩
        rw [hγ, zero_mul] at hlo
        simp only [centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero] at hlo
        omega
      rw [this, Finset.card_empty, Nat.cast_zero]
      positivity
    · have himage : (band i).image (fun x => γ i * x) = Finset.univ.filter fun y : ZMod N =>
          ((a i - c : Nat) : Real) < (centeredAbs y : Real) ∧
            (centeredAbs y : Real) ≤ ((a i + c : Nat) : Real) := by
        ext y
        simp only [band, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩
        · intro hy
          refine ⟨(γ i)⁻¹ * y, ?_, mul_inv_cancel_left₀ hγ y⟩
          rw [mul_inv_cancel_left₀ hγ y]
          exact ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
      have hinj : Function.Injective fun x : ZMod N => γ i * x := by
        intro x y hxy
        exact mul_left_cancel₀ hγ hxy
      rw [← Finset.card_image_of_injective _ hinj, himage]
      have h := band_card_le (N := N) (a := ((a i - c : Nat) : Real))
        (b := ((a i + c : Nat) : Real)) (by positivity) (by exact_mod_cast (by omega))
      have hc := hca i
      calc _ ≤ 2 * (((a i + c : Nat) : Real) - ((a i - c : Nat) : Real) + 1) := h
        _ = 4 * c + 2 := by push_cast [Nat.cast_sub hc]; ring
  have hle : (mixedBohr γ (fun i => a i + c)).card ≤
      (mixedBohr γ (fun i => a i + c) \ mixedBohr γ (fun i => a i - c)).card +
        (mixedBohr γ (fun i => a i - c)).card := Finset.card_le_card_sdiff_add_card
  have hann : ((mixedBohr γ (fun i => a i + c) \ mixedBohr γ (fun i => a i - c)).card : Real)
      ≤ Fintype.card ι * (4 * c + 2) := by
    calc _ ≤ ((Finset.univ.biUnion band).card : Real) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ i, ((band i).card : Real) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, ((4 * c + 2 : Nat) : Real) := Finset.sum_le_sum fun i _ => by
          push_cast; exact hband i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; push_cast; ring
  have hle' : ((mixedBohr γ (fun i => a i + c)).card : Real) ≤
      ((mixedBohr γ (fun i => a i + c) \ mixedBohr γ (fun i => a i - c)).card : Real) +
        (mixedBohr γ (fun i => a i - c)).card := by exact_mod_cast hle
  linarith

/-- The band bound with an error budget covering any tuple of at most `m`
frequencies. -/
theorem mixedBohr_band_le_budget {N : Nat} [NeZero N] [Fact N.Prime] {μ : Type*} [Fintype μ]
    (g : μ → ZMod N) (r : μ → Nat) (c m : Nat) (hr : ∀ q, c ≤ r q)
    (hcard : Fintype.card μ ≤ m) :
    ((mixedBohr g (fun q => r q + c)).card : Real) ≤
      (mixedBohr g (fun q => r q - c)).card + (m : Real) * (4 * c + 2) := by
  have h := mixedBohr_band_le g r c hr
  have : (Fintype.card μ : Real) * (4 * c + 2) ≤ (m : Real) * (4 * c + 2) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  linarith

/-- **Split relations make the bilinear Bohr variety quasirandom, prime `N`.**
No weak-regularity hypothesis remains. -/
theorem split_profile_quasirandom_prime {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ Y : Type*} [Fintype ι] [Fintype κ] [Fintype Y] [DecidableEq Y]
    (γ : ι → ZMod N) (ℓ : Y → κ → ZMod N) (a : ι → Nat) (b : κ → Nat) {c R : Nat}
    (hca : ∀ i, c ≤ a i) (hcb : ∀ j, c ≤ b j) (ha : ∀ i, 2 * a i < N)
    (hb : ∀ j, 2 * b j < N) (hc : 2 * c < N) (Λ : Set (κ → centeredBall N R)) {η : Real}
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ (κ ⊕ κ)) - 1 ≤ Fintype.card (ι ⊕ (κ ⊕ κ)) * (4 * c + 2) / N)
    (hsize : 20 * (Fintype.card (ι ⊕ (κ ⊕ κ)) * (4 * c + 2)) ≤
      ((mixedBohr γ (fun i => a i - c)).card : Real))
    (Ybad : Finset Y) (hYbad : (Ybad.card : Real) ≤ η * Fintype.card Y) {y₀ : Y}
    (hy₀ : y₀ ∉ Ybad)
    (hsplit1 : ∀ y ∉ Ybad, ∀ (ν : ι → centeredBall N R) (μ : κ → centeredBall N R),
      (∑ i, (ν i : ZMod N) * γ i) + (∑ j, (μ j : ZMod N) * ℓ y j) = 0 ↔
        (∑ i, (ν i : ZMod N) * γ i = 0 ∧ μ ∈ Λ))
    (Pbad : Finset (Y × Y)) (hPbad : (Pbad.card : Real) ≤ η * (Fintype.card Y : Real) ^ 2)
    (hsplit2 : ∀ y y', (y, y') ∉ Pbad →
      ∀ (ν : ι → centeredBall N R) (μ : κ ⊕ κ → centeredBall N R),
        (∑ i, (ν i : ZMod N) * γ i) + (∑ j, (μ j : ZMod N) * Sum.elim (ℓ y) (ℓ y') j) = 0 ↔
          (∑ i, (ν i : ZMod N) * γ i = 0 ∧
            ((fun j => μ (Sum.inl j)) ∈ Λ ∧ (fun j => μ (Sum.inr j)) ∈ Λ))) :
    ∃ δ : Real, 0 ≤ δ ∧ δ ≤ 1 ∧
      boxSum (fun (x : ↥(mixedBohr γ (fun i => a i - c))) (y : Y) =>
        (if (x : ZMod N) ∈ mixedBohr (ℓ y) (fun j => b j - c) then (1 : Real) else 0) - δ) ≤
      3 * (80 * (Fintype.card (ι ⊕ (κ ⊕ κ)) * (4 * c + 2)) /
          (mixedBohr γ (fun i => a i - c)).card + η) *
        ((mixedBohr γ (fun i => a i - c)).card : Real) ^ 2 * (Fintype.card Y : Real) ^ 2 := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨m, hm⟩ : ∃ m : Nat, m = Fintype.card (ι ⊕ (κ ⊕ κ)) := ⟨_, rfl⟩
  rw [← hm] at htrunc hsize ⊢
  obtain ⟨ε, hε⟩ : ∃ ε : Real, ε = (m : Real) * (4 * c + 2) / N := ⟨_, rfl⟩
  have hεN : ε * N = (m : Real) * (4 * c + 2) := by rw [hε]; field_simp
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hcardι : Fintype.card ι ≤ m := by rw [hm]; simp [Fintype.card_sum]
  have hcardικ : Fintype.card (ι ⊕ κ) ≤ m := by rw [hm]; simp [Fintype.card_sum]
  have hcardall : Fintype.card (ι ⊕ (κ ⊕ κ)) ≤ m := by rw [hm]
  have hb1 := mixedBohr_band_le_budget γ a c m hca hcardι
  rw [← hεN] at hb1
  obtain ⟨δ, hδ0, hδ1, hbox⟩ := split_profile_quasirandom γ ℓ a b hca hcb ha hb hc Λ
    (ε := ε) (η := η) hε0 (by rw [← hm, hε]; exact htrunc) hb1
    (by rw [mul_assoc, hεN]; exact hsize) Ybad hYbad hy₀ hsplit1
    (fun y _ => by
      have h := mixedBohr_band_le_budget (Sum.elim γ (ℓ y)) (Sum.elim a b) c m
        (fun q => by cases q with | inl i => exact hca i | inr j => exact hcb j) hcardικ
      rw [← hεN] at h; exact h)
    Pbad hPbad hsplit2
    (fun y y' _ => by
      have h := mixedBohr_band_le_budget (Sum.elim γ (Sum.elim (ℓ y) (ℓ y')))
        (Sum.elim a (Sum.elim b b)) c m
        (fun q => by
          rcases q with i | j | j
          · exact hca i
          · exact hcb j
          · exact hcb j) hcardall
      rw [← hεN] at h; exact h)
  refine ⟨δ, hδ0, hδ1, hbox.trans (le_of_eq ?_)⟩
  rw [show 80 * ε * N = 80 * ((m : Real) * (4 * c + 2)) by rw [mul_assoc, hεN]]

end LeanProofs.GowersSzemeredi
