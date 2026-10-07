import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem scalarResidue_relative_count_error (a b r v : ℤ) (hab : a < b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1| ≤ (r : ℝ) / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_absolute_error a b r v hab.le hr
  have heq : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1 =
      (((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
        ((b - a : ℤ) : ℝ) / r) * ((r : ℝ) / ((b - a : ℤ) : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (div_pos hrR hL)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (div_nonneg hrR.le hL.le)

end Erdos3

end

section

namespace Erdos3

theorem residue_constraints_iff_lcm {M d : ℕ} {u v c : ℤ}
    (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d : ℤ)] := by
  have hlcm : (M : ℤ).lcm (d : ℤ) = Nat.lcm M d := by simp [Int.lcm_def]
  rw [← hlcm, ← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨fun h => ⟨h.1.trans hM.symm, h.2.trans hd.symm⟩,
    fun h => ⟨h.1.trans hM, h.2.trans hd⟩⟩

theorem exists_integer_coprime_residues {M d : ℕ} (hcop : M.Coprime d) (u v : ℤ) :
    ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] := by
  have hbez : (M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab M d).symm
  let c := u * ((d : ℤ) * Nat.gcdB M d) + v * ((M : ℤ) * Nat.gcdA M d)
  refine ⟨c, Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_⟩
  · refine ⟨(u - v) * Nat.gcdA M d, ?_⟩
    calc
      u - c = u * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by rw [hbez, mul_one]
      _ = (M : ℤ) * ((u - v) * Nat.gcdA M d) := by dsimp [c]; ring
  · refine ⟨(v - u) * Nat.gcdB M d, ?_⟩
    calc
      v - c = v * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by rw [hbez, mul_one]
      _ = (d : ℤ) * ((v - u) * Nat.gcdB M d) := by dsimp [c]; ring

theorem coprime_refinement_preserves_compatibility {M d J : ℕ}
    (hcop : (M * d).Coprime J) (u v w : ℤ) :
    (∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)]) ↔
      ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] ∧ c ≡ w [ZMOD (J : ℤ)] := by
  constructor
  · rintro ⟨c, hM, hd⟩
    have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
    obtain ⟨t, ht, htJ⟩ := exists_integer_coprime_residues hL c w
    obtain ⟨htM, htd⟩ := (residue_constraints_iff_lcm hM hd t).mpr ht
    exact ⟨t, htM, htd, htJ⟩
  · rintro ⟨c, hM, hd, _⟩
    exact ⟨c, hM, hd⟩

theorem refined_residue_constraints_iff {M d J : ℕ} (hcop : (M * d).Coprime J)
    {u v w c : ℤ} (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)])
    (hJ : c ≡ w [ZMOD (J : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)] ∧ x ≡ w [ZMOD (J : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d * J : ℤ)] := by
  have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
  rw [← and_assoc, residue_constraints_iff_lcm hM hd x,
    residue_constraints_iff_lcm (Int.ModEq.refl c) hJ x, hL.lcm_eq_mul]
  simp only [Nat.cast_mul]

theorem compatible_residue_count_error (a b : ℤ) (hab : a ≤ b) {M d : ℕ}
    (hMpos : 0 < M) (hdpos : 0 < d) {u v c : ℤ}
    (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)]) :
    |((Finset.filter (fun x => x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)])
      (Finset.Ico a b)).card : ℝ) - ((b - a : ℤ) : ℝ) / Nat.lcm M d| ≤ 1 := by
  have hp : (0 : ℤ) < Nat.lcm M d := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hMpos.ne' hdpos.ne')
  have heq : Finset.filter (fun x : ℤ => x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)]) (Finset.Ico a b) =
      Finset.filter (fun x : ℤ => x ≡ c [ZMOD (Nat.lcm M d : ℤ)]) (Finset.Ico a b) := by
    ext x
    simp only [Finset.mem_filter, residue_constraints_iff_lcm hM hd x]
  rw [heq]
  exact scalarResidue_card_absolute_error a b (Nat.lcm M d) c hab hp

end Erdos3

end

section

namespace Erdos3

noncomputable def residueIndexLower (a r v : ℤ) : ℤ :=
  ⌈((a : ℚ) - (v : ℚ)) / (r : ℚ)⌉

noncomputable def residueIndexLength (a b r v : ℤ) : ℕ :=
  (residueIndexLower b r v - residueIndexLower a r v).toNat

def residueAffineEmbedding (r v : ℤ) (hr : r ≠ 0) : ℤ ↪ ℤ where
  toFun k := v + r * k
  inj' _ _ h := mul_left_cancel₀ hr (add_left_cancel h)

theorem residueIndexInterval_eq (a b r v : ℤ) :
    Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v) =
      Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v) := by
  ext x
  simp only [Finset.mem_Ico, residueIndexLength]
  omega

theorem residueInterval_eq_map (a b r v : ℤ) (hr : 0 < r) :
    Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b) =
      (Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v)).map
        (residueAffineEmbedding r v hr.ne') := by
  rw [Int.Ico_filter_modEq_eq, Int.Ico_filter_dvd_eq (a - v) (b - v) hr, Finset.map_map]
  simp only [Int.cast_sub]
  change (Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v)).map _ = _
  rw [residueIndexInterval_eq]
  congr 1
  ext k
  change k * r + v = v + r * k
  ring

noncomputable def residueIntervalEquiv (a b r v : ℤ) (hr : 0 < r) :
    ↥(Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v)) ≃
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := by
  let f : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v)) →
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := fun x =>
    ⟨v + r * x.val, by
      rw [residueInterval_eq_map a b r v hr]
      exact Finset.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact (residueAffineEmbedding r v hr.ne').injective (congrArg Subtype.val h)
  · intro y
    let yy : ℤ := y.val
    have hy : yy ∈ Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b) := y.property
    rw [residueInterval_eq_map a b r v hr] at hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp] theorem residueIntervalEquiv_val (a b r v : ℤ) (hr : 0 < r)
    (x : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v))) :
    (residueIntervalEquiv a b r v hr x).val = v + r * x.val := rfl

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

theorem residueIndexLength_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |(residueIndexLength a b r v : ℝ) - ((b - a : ℤ) : ℝ) / (r : ℝ)| ≤ 1 := by
  rw [residueIndexLength_eq_card a b r v hr]
  exact scalarResidue_card_absolute_error a b r v hab hr

end Erdos3

end

section

namespace Erdos3

def integerResidueLabel (d : ℕ) (hd : 0 < d) (x : ℤ) : Fin d :=
  ⟨(x % (d : ℤ)).toNat, by
    have hlo := Int.emod_nonneg x (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')
    have hhi := Int.emod_lt_of_pos x (show (0 : ℤ) < d by exact_mod_cast hd)
    omega⟩

theorem integerResidueLabel_val (d : ℕ) (hd : 0 < d) (x : ℤ) :
    ((integerResidueLabel d hd x).val : ℤ) = x % (d : ℤ) := by
  have hlo := Int.emod_nonneg x (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')
  exact Int.toNat_of_nonneg hlo

theorem integerResidueLabel_eq_iff (d : ℕ) (hd : 0 < d) (x : ℤ) (v : Fin d) :
    integerResidueLabel d hd x = v ↔ x ≡ (v.val : ℤ) [ZMOD (d : ℤ)] := by
  have hv : (v.val : ℤ) % (d : ℤ) = v.val := Int.emod_eq_of_lt
    (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)
  have hx := integerResidueLabel_val d hd x
  rw [Int.ModEq, hv, Fin.ext_iff]
  omega

abbrev CompatibleAuxResidue (M d : ℕ) (u : ℤ) :=
  {v : Fin d // ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ (v.val : ℤ) [ZMOD (d : ℤ)]}

noncomputable instance compatibleAuxResidueFintype (M d : ℕ) (u : ℤ) :
    Fintype (CompatibleAuxResidue M d u) := Fintype.ofFinite _

def compatibleAuxResidueOfPoint (M d : ℕ) (hd : 0 < d) (u x : ℤ)
    (hx : x ≡ u [ZMOD (M : ℤ)]) : CompatibleAuxResidue M d u :=
  ⟨integerResidueLabel d hd x, x, hx, (integerResidueLabel_eq_iff d hd x _).mp rfl⟩

theorem compatibleAuxResidueOfPoint_eq_iff (M d : ℕ) (hd : 0 < d) (u x : ℤ)
    (hx : x ≡ u [ZMOD (M : ℤ)]) (v : CompatibleAuxResidue M d u) :
    compatibleAuxResidueOfPoint M d hd u x hx = v ↔
      x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] := by
  rw [Subtype.ext_iff]
  exact integerResidueLabel_eq_iff d hd x v.val

theorem compatibleAuxResidue_nonempty (M d : ℕ) (hd : 0 < d) (u : ℤ) :
    Nonempty (CompatibleAuxResidue M d u) :=
  ⟨compatibleAuxResidueOfPoint M d hd u u (Int.ModEq.refl u)⟩

noncomputable def CompatibleAuxResidue.baseValue {M d : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) : ℤ := Classical.choose v.property

theorem CompatibleAuxResidue.baseValue_spec {M d : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) :
    v.baseValue ≡ u [ZMOD (M : ℤ)] ∧
      v.baseValue ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] := Classical.choose_spec v.property

noncomputable def CompatibleAuxResidue.refinedValue {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J) (w : ℤ) : ℤ :=
  Classical.choose ((coprime_refinement_preserves_compatibility hcop u v.val.val w).mp v.property)

theorem CompatibleAuxResidue.refinedValue_spec {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J) (w : ℤ) :
    v.refinedValue hcop w ≡ u [ZMOD (M : ℤ)] ∧
      v.refinedValue hcop w ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] ∧
      v.refinedValue hcop w ≡ w [ZMOD (J : ℤ)] :=
  Classical.choose_spec ((coprime_refinement_preserves_compatibility hcop u v.val.val w).mp v.property)

theorem CompatibleAuxResidue.baseConstraint_iff {M d : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)]) ↔
      x ≡ v.baseValue [ZMOD (Nat.lcm M d : ℤ)] :=
  residue_constraints_iff_lcm v.baseValue_spec.1 v.baseValue_spec.2 x

theorem refinement_modEq_iff {M J : ℕ} (hcop : M.Coprime J) {u w : ℤ}
    (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) :
    x ≡ w [ZMOD (M * J : ℕ)] ↔
      (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ w [ZMOD (J : ℤ)]) := by
  simpa only [hcop.lcm_eq_mul] using
    (residue_constraints_iff_lcm hw (show w ≡ w [ZMOD (J : ℤ)] from Int.ModEq.refl w) x).symm

theorem CompatibleAuxResidue.refinedConstraint_iff {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J)
    (w : ℤ) (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) :
    (x ≡ w [ZMOD (M * J : ℕ)] ∧ x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)]) ↔
      x ≡ v.refinedValue hcop w [ZMOD (Nat.lcm M d * J : ℕ)] := by
  have hMJ : M.Coprime J := hcop.of_dvd_left (dvd_mul_right M d)
  rw [refinement_modEq_iff hMJ hw x]
  have hc := v.refinedValue_spec hcop w
  exact (and_assoc.trans (and_congr_right fun _ => and_comm)).trans
    (refined_residue_constraints_iff hcop hc.1 hc.2.1 hc.2.2 x)

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_ge_of_width (a b r v : ℤ) (hr : 0 < r)
    (B : ℝ) (hB : 0 ≤ B) (hwidth : (r : ℝ) * (B + 1) ≤ ((b - a : ℤ) : ℝ)) :
    B ≤ (residueIndexLength a b r v : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hwidthpos : (0 : ℝ) < ((b - a : ℤ) : ℝ) :=
    (mul_pos hr' (by linarith : 0 < B + 1)).trans_le hwidth
  have hab : a ≤ b := by
    have h : (0 : ℤ) ≤ b - a := by exact_mod_cast hwidthpos.le
    omega
  have hlower := (abs_le.mp (residueIndexLength_absolute_error a b r v hab hr)).1
  have hratio : B + 1 ≤ ((b - a : ℤ) : ℝ) / (r : ℝ) :=
    (le_div_iff₀ hr').mpr (by simpa only [mul_comm] using hwidth)
  linarith

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_half_width (a v : ℤ) (N r : ℕ) (hr : 0 < r)
    (hwidth : 2 * (r : ℝ) ≤ (N : ℝ)) :
    0 < residueIndexLength a (a + N) r v ∧
    (N : ℝ) / 2 ≤ (r : ℝ) * (residueIndexLength a (a + N) r v : ℝ) := by
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hlength := residueIndexLength_ge_of_width a (a + N) r v hrz 1 (by norm_num)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using (show (r : ℝ) * (1 + 1) ≤ (N : ℝ) by linarith))
  have herror := residueIndexLength_absolute_error a (a + N) r v (by omega) hrz
  simp only [add_sub_cancel_left, Int.cast_natCast] at herror
  have hlo := (abs_le.mp herror).1
  have hmul := mul_le_mul_of_nonneg_left hlo hrr.le
  have hdiv : (r : ℝ) * ((N : ℝ) / r) = (N : ℝ) := by field_simp
  refine ⟨?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < (residueIndexLength a (a + N) r v : ℝ) by linarith)
  · nlinarith

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_large_of_exp (lo a : ℤ) (N M : ℕ) (P B : ℝ)
    (hM : 0 < M) (hB : 0 ≤ B) (hmodulus : (M : ℝ) ≤ Real.exp P)
    (hside : Real.exp (P + B + 2) ≤ (N : ℝ)) :
    Real.exp B ≤ (residueIndexLength lo (lo + N) M a : ℝ) := by
  have hMreal : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hBexp : 1 ≤ Real.exp B := Real.one_le_exp hB
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hproduct : 2 * (M : ℝ) * Real.exp B ≤ Real.exp (P + B + 2) := by
    rw [Real.exp_add, Real.exp_add]
    calc
      2 * (M : ℝ) * Real.exp B ≤ 2 * Real.exp P * Real.exp B := by
        gcongr
      _ ≤ Real.exp P * Real.exp B * Real.exp 2 := by
        have hm := mul_le_mul_of_nonneg_left htwo
          (mul_nonneg (Real.exp_pos P).le (Real.exp_pos B).le)
        nlinarith
  have hwidth : 2 * (M : ℝ) ≤ (N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hBexp (show 0 ≤ 2 * (M : ℝ) by positivity)
    nlinarith [hproduct.trans hside]
  have hlength := (residueIndexLength_half_width lo a N M hM hwidth).2
  apply le_of_mul_le_mul_left (a := (M : ℝ)) _ hMreal
  nlinarith [hproduct.trans hside]

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_le_width (lo a : ℤ) (N M : ℕ) (hM : 0 < M) :
    residueIndexLength lo (lo + N) M a ≤ N := by
  rw [residueIndexLength_eq_card lo (lo + N) M a (Nat.cast_pos.mpr hM)]
  have h := Finset.card_filter_le (Finset.Ico lo (lo + N)) (fun z => z ≡ a [ZMOD (M : ℤ)])
  simpa only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using h

theorem residue_slice_counting_cost (lo a : ℤ) (H N M : ℕ) (p : ℝ)
    (hM : 0 < M) (hNH : N ≤ H) (hH : Real.exp (p + 2) ≤ (H : ℝ))
    (hcount : Real.exp (-p) * (H : ℝ) ≤ (residueIndexLength lo (lo + N) M a : ℝ)) :
    (M : ℝ) ≤ Real.exp (p + 2) ∧ Real.exp (-p) * (H : ℝ) ≤ (N : ℝ) := by
  have hMreal : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hHreal : (0 : ℝ) < H := (Real.exp_pos (p + 2)).trans_le hH
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hinv : Real.exp (-p) * Real.exp p = 1 := by rw [← Real.exp_add]; simp
  have hsmall : 2 ≤ Real.exp (-p) * (H : ℝ) := by
    calc
      2 ≤ Real.exp 2 := htwo
      _ = Real.exp (-p) * Real.exp (p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-p) * (H : ℝ) := mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
  have herror := (abs_le.mp (residueIndexLength_absolute_error lo (lo + N) M a
    (by omega) (Nat.cast_pos.mpr hM))).2
  simp only [add_sub_cancel_left, Int.cast_natCast] at herror
  have hNHreal : (N : ℝ) ≤ H := by exact_mod_cast hNH
  have hquotient : Real.exp (-p) * (H : ℝ) / 2 ≤ (H : ℝ) / M := by
    have hquot := div_le_div_of_nonneg_right hNHreal hMreal.le
    linarith
  have hmul : Real.exp (-p) * (H : ℝ) / 2 * (M : ℝ) ≤ H :=
    (le_div_iff₀ hMreal).mp hquotient
  have hfactor : Real.exp (-p) * (M : ℝ) ≤ 2 := by
    apply le_of_mul_le_mul_right (a := (H : ℝ)) _ hHreal
    nlinarith [hmul]
  have hbound : (M : ℝ) ≤ 2 * Real.exp p := by
    have h := mul_le_mul_of_nonneg_right hfactor (Real.exp_pos p).le
    calc
      (M : ℝ) = (Real.exp (-p) * (M : ℝ)) * Real.exp p := by nlinarith [hinv]
      _ ≤ 2 * Real.exp p := h
  refine ⟨?_, ?_⟩
  · calc
      (M : ℝ) ≤ 2 * Real.exp p := hbound
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_pos p).le
      _ = Real.exp (p + 2) := by rw [← Real.exp_add, add_comm]
  · exact hcount.trans (by exact_mod_cast residueIndexLength_le_width lo a N M hM)

end Erdos3

end

end OAI
