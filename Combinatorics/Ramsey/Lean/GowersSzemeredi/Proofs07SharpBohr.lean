import GowersSzemeredi.Proofs07TranslationAverage

/-! Translated-box averaging improves the Bohr cardinality factor from
(delta/2)^|K| to delta^|K|, avoiding coordinate-grid rounding loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private theorem centered_sub_of_small_values {N L : Nat} [NeZero N]
    {x y : ZMod N} (hx : x.val < L) (hy : y.val < L) :
    centeredAbs (x - y) ≤ L - 1 := by
  have ordered (a b : ZMod N) (ha : a.val < L) (hba : b.val ≤ a.val) :
      centeredAbs (a - b) ≤ L - 1 := by
    have hcast : a - b = ((a.val - b.val : Nat) : ZMod N) := by
      rw [Nat.cast_sub hba, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hlt : a.val - b.val < N := (Nat.sub_le _ _).trans_lt a.val_lt
    rw [centeredAbs, hcast, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast_of_lt hlt]
    exact (Nat.min_le_left _ _).trans (by omega)
  by_cases h : y.val ≤ x.val
  · exact ordered x y hx h
  · have heq : centeredAbs (x - y) = centeredAbs (y - x) := by
      simpa only [centeredAbs, neg_sub] using ZMod.natAbs_valMinAbs_neg (y - x)
    rw [heq]
    exact ordered y x hy (le_of_not_ge h)

/-- The sharper cardinality lower bound is valid on the full standard
radius range and over every nonzero modulus, without primality. -/
theorem bohr_card_lower_bound_sharp {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    delta ^ K.card * (N : Real) ≤ (bohr K delta).card := by
  classical
  let L : Nat := ⌈delta * N⌉₊
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hLpos : 0 < L := Nat.ceil_pos.mpr (mul_pos hd hN)
  have hLN : L ≤ N := by
    apply Nat.ceil_le.mpr
    simpa using mul_le_mul_of_nonneg_right hd1 hN.le
  have hLlower : delta * N ≤ (L : Real) := Nat.le_ceil _
  have hLsmall : ((L - 1 : Nat) : Real) ≤ delta * N := by
    rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    have h := Nat.ceil_lt_add_one (mul_nonneg hd.le hN.le)
    change (L : Real) < delta * N + 1 at h
    linarith
  let I : Finset (ZMod N) := (Finset.range L).image (fun x : Nat ↦ (x : ZMod N))
  have hIcard : I.card = L := by
    have hinj : Set.InjOn (fun x : Nat ↦ (x : ZMod N)) (Finset.range L : Set Nat) := by
      intro x hx y hy hxy
      have hxN : x < N := (Finset.mem_range.mp hx).trans_le hLN
      have hyN : y < N := (Finset.mem_range.mp hy).trans_le hLN
      simpa only [ZMod.val_natCast_of_lt hxN, ZMod.val_natCast_of_lt hyN] using congrArg ZMod.val hxy
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hIval (x : ZMod N) (hx : x ∈ I) : x.val < L := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hiL := Finset.mem_range.mp hi
    simpa only [ZMod.val_natCast_of_lt (hiL.trans_le hLN)] using hiL
  let Q : Finset (↑K → ZMod N) := Finset.univ.filter fun z ↦ ∀ r, z r ∈ I
  let f : ZMod N → (↑K → ZMod N) := fun x r ↦ r.val * x
  have hQcard : Q.card = L ^ K.card := by
    simpa only [hIcard, Fintype.card_coe] using finite_product_subset_card (I := ↑K) I
  obtain ⟨z, hz⟩ := exists_translation_fiber_cross_bound f Q
  let C := translationFiber f Q z
  have hcross : N * L ^ K.card ≤ N ^ K.card * C.card := by
    simpa only [ZMod.card, Fintype.card_fun, Fintype.card_coe, hQcard, C] using hz
  have hCbound : C.card ≤ (bohr K delta).card := by
    by_cases hC : C.Nonempty
    · obtain ⟨a, ha⟩ := hC
      apply Finset.card_le_card_of_injOn (fun x : ZMod N ↦ x - a)
      · intro x hx
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro r hr
        have hxQ := (Finset.mem_filter.mp hx).2
        have haQ := (Finset.mem_filter.mp ha).2
        have hxI : r * x - z ⟨r, hr⟩ ∈ I := (Finset.mem_filter.mp hxQ).2 ⟨r, hr⟩
        have haI : r * a - z ⟨r, hr⟩ ∈ I := (Finset.mem_filter.mp haQ).2 ⟨r, hr⟩
        have hsmall := centered_sub_of_small_values (hIval _ hxI) (hIval _ haI)
        have heq : r * (x - a) = (r * x - z ⟨r, hr⟩) - (r * a - z ⟨r, hr⟩) := by ring
        rw [heq]
        exact (by exact_mod_cast hsmall : (centeredAbs ((r * x - z ⟨r, hr⟩) -
          (r * a - z ⟨r, hr⟩)) : Real) ≤ (L - 1 : Nat)).trans hLsmall
      · intro x _ y _ hxy
        simpa using congrArg (fun v ↦ v + a) hxy
    · rw [Finset.not_nonempty_iff_eq_empty.mp hC]
      exact Nat.zero_le _
  have hcrossB : N * L ^ K.card ≤ N ^ K.card * (bohr K delta).card :=
    hcross.trans (Nat.mul_le_mul_left _ hCbound)
  have hcrossR : (N : Real) * (L : Real) ^ K.card ≤
      (N : Real) ^ K.card * (bohr K delta).card := by exact_mod_cast hcrossB
  apply le_of_mul_le_mul_left (a := (N : Real) ^ K.card) _ (pow_pos hN _)
  calc
    _ = (N : Real) * (delta * N) ^ K.card := by rw [mul_pow]; ring
    _ ≤ (N : Real) * (L : Real) ^ K.card := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hd.le hN.le) hLlower _) hN.le
    _ ≤ _ := hcrossR

/-- The sharp lower bound gives a nonzero Bohr element at the stronger
radius N^(-1/|K|). -/
theorem bohr_nonzero_of_sharp_radius {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (hK : K.Nonempty) (delta : Real)
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hradius : (N : Real) ^ (-(1 / (K.card : Real))) < delta) :
    ∃ d : ZMod N, d ∈ bohr K delta ∧ d ≠ 0 := by
  classical
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hk : 0 < K.card := Finset.card_pos.mpr hK
  have hkR : (0 : Real) < K.card := by exact_mod_cast hk
  have hcancel : ((N : Real) ^ (-(1 / (K.card : Real)))) ^ K.card * N = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    have he : (-(1 / (K.card : Real))) * K.card = -1 := by field_simp
    rw [he, Real.rpow_neg_one, inv_mul_cancel₀ hN.ne']
  have hp : ((N : Real) ^ (-(1 / (K.card : Real)))) ^ K.card < delta ^ K.card :=
    pow_lt_pow_left₀ hradius (Real.rpow_nonneg hN.le _) hk.ne'
  have hlarge : 1 < delta ^ K.card * N := by
    rw [← hcancel]
    exact mul_lt_mul_of_pos_right hp hN
  have hcard := hlarge.trans_le (bohr_card_lower_bound_sharp K delta hd hd1)
  by_contra hnone
  have hsub : bohr K delta ⊆ {0} := by
    intro d hdB
    have he : d = 0 := by
      by_contra hne
      exact hnone ⟨d, hdB, hne⟩
    simpa using he
  have hc : (bohr K delta).card ≤ 1 := by simpa using Finset.card_le_card hsub
  have hcR : ((bohr K delta).card : Real) ≤ 1 := by exact_mod_cast hc
  linarith

/-- The original printed nonzero criterion is recovered from the sharper
bound, even though it does not follow from the coarser grid estimate alone. -/
theorem bohr_nonzero_of_original_radius {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (hK : K.Nonempty) (delta : Real)
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hradius : ((N : Real) / 2) ^ (-(1 / (K.card : Real))) < delta) :
    ∃ d : ZMod N, d ∈ bohr K delta ∧ d ≠ 0 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcomparison : (N : Real) ^ (-(1 / (K.card : Real))) ≤
      ((N : Real) / 2) ^ (-(1 / (K.card : Real))) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr (by positivity))
  exact bohr_nonzero_of_sharp_radius K hK delta hd hd1 (hcomparison.trans_lt hradius)

/-- The original nonzero criterion, with its necessary radius/domain
conventions stated explicitly. -/
def lemma_7_7_original_radius : Prop :=
  ∀ (N : Nat) [NeZero N] (K : Finset (ZMod N)) (delta : Real),
    2 ≤ N → 0 < delta → delta ≤ 1 →
    (delta / 2) ^ K.card * (N : Real) ≤ (bohr K delta).card ∧
      (K.Nonempty → ((N : Real) / 2) ^ (-(1 / (K.card : Real))) < delta →
        ∃ d : ZMod N, d ∈ bohr K delta ∧ d ≠ 0)

theorem lemma_7_7_original_radius_holds : lemma_7_7_original_radius := by
  intro N _ K delta _ hd hd1
  refine ⟨?_, fun hK hr ↦ bohr_nonzero_of_original_radius K hK delta hd hd1 hr⟩
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : Real) ≤ delta / 2) (by linarith : delta / 2 ≤ delta) _)
    (Nat.cast_nonneg N)).trans (bohr_card_lower_bound_sharp K delta hd hd1)

/-- An unrestricted positive-radius reading of the old displayed
cardinality bound is false even at a prime modulus. -/
theorem bohr_unrestricted_radius_counterexample :
    ¬ (∀ (N : Nat) [NeZero N] (K : Finset (ZMod N)) (delta : Real),
      0 < delta → (delta / 2) ^ K.card * (N : Real) ≤ (bohr K delta).card) := by
  intro h
  have hb := h 2 ({0} : Finset (ZMod 2)) 3 (by norm_num)
  norm_num at hb
  have hc : (bohr ({0} : Finset (ZMod 2)) 3).card ≤ 2 := by
    simpa using Finset.card_le_univ (bohr ({0} : Finset (ZMod 2)) 3)
  have hcR : ((bohr ({0} : Finset (ZMod 2)) 3).card : Real) ≤ 2 := by exact_mod_cast hc
  linarith

end LeanProofs.GowersSzemeredi
