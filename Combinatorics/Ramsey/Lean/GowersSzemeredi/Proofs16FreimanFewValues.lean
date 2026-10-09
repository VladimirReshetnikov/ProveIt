import GowersSzemeredi.Proofs16FreimanKernelBohr

/-! A Freiman-linear map with a dense level set takes few values: [49]/
Milićević's Lemma 2.42 ("many zeroes imply small range"), in `ℤ/N`,
without regular radii.

Let `φ` be Freiman-linear on `B(Γ;ρ)` and constant (`= v`) on `Z ⊆ B(Γ;ρ)`.
* Averaging over translates gives `t` with
  `|Z ∩ (t + B(Γ;ρ/4))| · N ≥ |Z|·|B(Γ;ρ/4)|` (`exists_dense_translate`).
* Fix `z₀` there. The differences `W = (Z ∩ (t + B(ρ/4))) − z₀` lie in
  `B(ρ/2)`, and `φ(w) = φ(0)` on them, by the quadruple
  `z₀ + (z − z₀) = z + 0`.
* For `x ∈ B(ρ/2)` and `w ∈ W`, `φ(x + w) = φ(x)`. So distinct values of
  `φ` on `B(ρ/2)` give disjoint translates `x + W ⊆ B(ρ)`.

Hence `#φ(B(ρ/2)) · |Z| · |B(ρ/4)| ≤ N·|B(ρ)|`
(`freiman_image_card_mul_le`). With `|Z| ≥ c|B(ρ)|` this bounds the number
of values by `N/(c|B(ρ/4)|)`. With a Bohr lower bound that is
`c⁻¹(4/ρ)^{|Γ|}`-type, as in Milićević's `(200dc⁻¹)^{d+1}Πρ(γ)^{−d}`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **A dense translate.** -/
theorem exists_dense_translate {N : Nat} [NeZero N] (Z B : Finset (ZMod N)) :
    ∃ t : ZMod N, Z.card * B.card ≤ N * (Z.filter fun z => z - t ∈ B).card := by
  by_contra hno
  push Not at hno
  have hsum : ∑ t : ZMod N, (Z.filter fun z => z - t ∈ B).card = Z.card * B.card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.card_eq_sum_ones Z, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    rw [one_mul]
    have : ∑ t : ZMod N, (if z - t ∈ B then 1 else 0) = ∑ s : ZMod N, (if s ∈ B then 1 else 0) :=
      Fintype.sum_equiv (Equiv.subLeft z) _ _ (fun t => rfl)
    rw [this, ← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hlt : ∑ t : ZMod N, N * (Z.filter fun z => z - t ∈ B).card <
      ∑ _t : ZMod N, Z.card * B.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun t _ => hno t
  rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hlt
  exact lt_irrefl _ hlt

/-- **Few values from a dense level set** (Lemma 2.42 in `ℤ/N`). -/
theorem freiman_image_card_mul_le {N : Nat} [NeZero N] (Γ : Finset (ZMod N)) {ρ : Real}
    (hρ : 0 ≤ ρ) (φ : ZMod N → ZMod N) (hφ : IsFreimanLinearOn (bohr Γ ρ) φ)
    (Z : Finset (ZMod N)) (hZ : Z ⊆ bohr Γ ρ) {v : ZMod N} (hv : ∀ z ∈ Z, φ z = v) :
    ((bohr Γ (ρ / 2)).image φ).card * (Z.card * (bohr Γ (ρ / 4)).card) ≤
      N * (bohr Γ ρ).card := by
  obtain ⟨t, ht⟩ := exists_dense_translate Z (bohr Γ (ρ / 4))
  set W₀ := Z.filter fun z => z - t ∈ bohr Γ (ρ / 4) with hW₀
  by_cases hW₀e : W₀ = ∅
  · -- then `|Z|·|B(ρ/4)| = 0`
    rw [hW₀e, Finset.card_empty, mul_zero] at ht
    have : Z.card * (bohr Γ (ρ / 4)).card = 0 := Nat.le_zero.mp ht
    rw [this, mul_zero]
    exact Nat.zero_le _
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hW₀e
  have hz₀Z : z₀ ∈ Z := (Finset.mem_filter.mp hz₀).1
  have hz₀t : z₀ - t ∈ bohr Γ (ρ / 4) := (Finset.mem_filter.mp hz₀).2
  have hsub : ∀ {σ : Real}, σ ≤ ρ → bohr Γ σ ⊆ bohr Γ ρ := fun h => bohr_mono_radius Γ h
  have h0 : (0 : ZMod N) ∈ bohr Γ ρ := zero_mem_bohr Γ hρ
  set W := W₀.image fun z => z - z₀ with hW
  have hWcard : W.card = W₀.card := Finset.card_image_of_injective _ (sub_left_injective)
  -- `W ⊆ B(ρ/2)` and `φ = φ 0` on `W`
  have hWhalf : ∀ w ∈ W, w ∈ bohr Γ (ρ / 2) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have hzt : z - t ∈ bohr Γ (ρ / 4) := (Finset.mem_filter.mp hz).2
    have := bohr_add_half (ρ := ρ / 2) (by rw [show ρ / 2 / 2 = ρ / 4 by ring]; exact hzt)
      (by rw [show ρ / 2 / 2 = ρ / 4 by ring]; exact neg_mem_bohr hz₀t)
    have heq : z - t + -(z₀ - t) = z - z₀ := by ring
    rwa [heq] at this
  have hWker : ∀ w ∈ W, φ w = φ 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have hzZ : z ∈ Z := (Finset.mem_filter.mp hz).1
    have hwB : z - z₀ ∈ bohr Γ ρ := hsub (by linarith) (hWhalf _ (Finset.mem_image_of_mem _ hz))
    have h := hφ z₀ (z - z₀) z 0 (hZ hz₀Z) hwB (hZ hzZ) h0 (by ring)
    rw [hv z₀ hz₀Z, hv z hzZ] at h
    linear_combination h
  -- translates of `W` by points of `B(ρ/2)` keep the value
  have htrans : ∀ x ∈ bohr Γ (ρ / 2), ∀ w ∈ W, x + w ∈ bohr Γ ρ ∧ φ (x + w) = φ x := by
    intro x hx w hw
    have hxw : x + w ∈ bohr Γ ρ := bohr_add_half hx (hWhalf w hw)
    refine ⟨hxw, ?_⟩
    have h := hφ x w (x + w) 0 (hsub (by linarith) hx) (hsub (by linarith) (hWhalf w hw)) hxw h0
      (by ring)
    rw [hWker w hw] at h
    linear_combination -h
  -- choose a representative for every value
  set V := (bohr Γ (ρ / 2)).image φ with hV
  have hrep : ∀ u ∈ V, ∃ x ∈ bohr Γ (ρ / 2), φ x = u := fun u hu => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨x, hx, rfl⟩
  choose! r hr hru using hrep
  let T : ZMod N → Finset (ZMod N) := fun u => W.image fun w => r u + w
  have hTcard : ∀ u, (T u).card = W.card := fun u =>
    Finset.card_image_of_injective _ (add_right_injective (r u))
  have hTsub : V.biUnion T ⊆ bohr Γ ρ := by
    intro y hy
    obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hyu
    exact (htrans (r u) (hr u hu) w hw).1
  have hdisj : (V : Set (ZMod N)).PairwiseDisjoint T := by
    intro u hu u' hu' huu'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w', hw', hw'eq⟩ := Finset.mem_image.mp hy'
    have h1 := (htrans (r u) (hr u hu) w hw).2
    have h2 := (htrans (r u') (hr u' hu') w' hw').2
    rw [hru u hu] at h1
    rw [hru u' hu', hw'eq] at h2
    exact huu' (h1.symm.trans h2)
  have hcount : V.card * W.card ≤ (bohr Γ ρ).card := by
    calc V.card * W.card = ∑ u ∈ V, (T u).card := by
          rw [Finset.sum_congr rfl fun u _ => hTcard u, Finset.sum_const, smul_eq_mul]
      _ = (V.biUnion T).card := (Finset.card_biUnion hdisj).symm
      _ ≤ _ := Finset.card_le_card hTsub
  rw [hWcard] at hcount
  calc V.card * (Z.card * (bohr Γ (ρ / 4)).card) ≤ V.card * (N * W₀.card) :=
        Nat.mul_le_mul_left _ ht
    _ = N * (V.card * W₀.card) := by ring
    _ ≤ N * (bohr Γ ρ).card := Nat.mul_le_mul_left _ hcount

end LeanProofs.GowersSzemeredi
