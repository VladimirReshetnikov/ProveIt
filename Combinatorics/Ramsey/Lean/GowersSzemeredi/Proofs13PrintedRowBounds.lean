import GowersSzemeredi.Proofs13AllScalesStepSpan

/-! Original contextual bounds of Lemma 13.7, under the original printed
Stage 13.6 density hypotheses. This does not assert those stronger upstream
extraction hypotheses follow from the existing weaker companion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def IsStage136DataPrinted {N : Nat} [NeZero N] (S : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) (F : Stage136Data N) : Prop :=
  F.R.step = E.Q.step ∧ F.R.step != 0 ∧ F.R.IsProper ∧
  section13Zeta S.alpha / 2 *
      (N : Real) ^
        ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ F.R.length ∧
  (∀ h, h ∈ criticalHeights S D E →
    F.Y h ⊆ verticalEdgeDomain S.A h ∧
    (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (N : Real) ^ 2 ≤
      (F.Y h).card ∧
    LinearOnDomain (stage136RestrictedEdges F h) (fun z : Pair N => z.1)
      (verticalPhiDifference S.phi h)) ∧
  (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * F.R.length * N *
      (criticalHeights S D E).card ≤
    ∑ h ∈ criticalHeights S D E, (stage136RestrictedEdges F h).card ∧
  (2 : Real) ^ (-(31 : Int)) * S.alpha ^ 160 * E.Q.length * F.R.length * N ≤
    ∑ h ∈ criticalHeights S D E, (stage136RestrictedEdges F h).card

def IsStage137DataPrintedWithoutDomain {N : Nat} [NeZero N] (S0 : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) (F : Stage136Data N)
    (G : Stage137Data N) : Prop :=
  G.S.step != 0 ∧ G.S.IsProper ∧ G.S.carrier ⊆ F.R.carrier ∧
  (F.R.length : Real) ^
      ((2 : Real) ^ (-(66 : Int)) * S0.alpha ^ 256) ≤ G.S.length ∧
  G.B ⊆ G.S.carrier.product (translateFinset (criticalHeights S0 D E) G.y) ∧
  (2 : Real) ^ (-(26 : Int)) * S0.alpha ^ 128 * G.S.length *
      (criticalHeights S0 D E).card ≤ G.B.card ∧
  (2 : Real) ^ (-(31 : Int)) * S0.alpha ^ 160 * E.Q.length * G.S.length ≤
      G.B.card ∧
  ∀ h, h ∈ criticalHeights S0 D E →
    LinearOn (G.S.carrier.filter fun x => (x, G.y + h) ∈ G.B)
      (fun x => S0.phi (x, G.y + h))

/-- The complete Stage 13.7 data, including the domain containment supplied
by the printed construction from edges in `A`. This condition is essential
when the following lemma uses the vertical Freiman relations of `phi`. -/
def IsStage137DataPrinted {N : Nat} [NeZero N] (S0 : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) (F : Stage136Data N)
    (G : Stage137Data N) : Prop :=
  IsStage137DataPrintedWithoutDomain S0 D E F G ∧ G.B ⊆ S0.A


theorem IsStage136DataPrinted.to_encoded {N : Nat} [NeZero N]
    {S : Section13Context N} {D : Stage134Data N} {E : Stage135Data N} {F : Stage136Data N}
    (hF : IsStage136DataPrinted S D E F) : IsStage136Data S D E F := by
  have hb : (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 ≤
      (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 :=
    mul_le_mul (by norm_num) (pow_le_pow_of_le_one S.alpha_pos.le S.alpha_at_most_one (by omega))
      (by positivity) (by positivity)
  have hb2 : (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256 ≤
      (2 : Real) ^ (-(31 : Int)) * S.alpha ^ 160 :=
    mul_le_mul (by norm_num) (pow_le_pow_of_le_one S.alpha_pos.le S.alpha_at_most_one (by omega))
      (by positivity) (by positivity)
  obtain ⟨hstep, hne, hP, hw, hY, hmass1, hmass2⟩ := hF
  refine ⟨hstep, hne, hP, hw, ?_, ?_, ?_⟩
  · intro h hh
    refine ⟨(hY h hh).1, ?_, (hY h hh).2.2⟩
    exact (mul_le_mul_of_nonneg_right hb (by positivity)).trans (hY h hh).2.1
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg F.R.length)) (Nat.cast_nonneg N))
      (Nat.cast_nonneg (criticalHeights S D E).card)).trans hmass1
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb2 (Nat.cast_nonneg E.Q.length))
        (Nat.cast_nonneg F.R.length)) (Nat.cast_nonneg N)).trans hmass2

theorem stage137Printed_partition_exponent (alpha : Real) :
    cor711Exponent ((2 : Real) ^ (-(26 : Int)) * alpha ^ 128) 1 =
      (2 : Real) ^ (-(66 : Int)) * alpha ^ 256 := by
  unfold cor711Exponent
  norm_num [Real.rpow_neg, zpow_neg]
  ring

theorem stage136Printed_exists_base_row {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136DataPrinted S D E F) :
    ∃ y : ZMod N,
      (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * F.R.length *
        (criticalHeights S D E).card ≤
        (stage137UpperEndpoints F.R.carrier (criticalHeights S D E) F.Y y).card ∧
      (2 : Real) ^ (-(31 : Int)) * S.alpha ^ 160 * E.Q.length * F.R.length ≤
        (stage137UpperEndpoints F.R.carrier (criticalHeights S D E) F.Y y).card := by
  obtain ⟨_, _, _, _, _, h₁, h₂⟩ := hF
  apply exists_stage137_base_row_two_bounds
  · simpa only [stage136RestrictedEdges, Nat.cast_sum, mul_assoc, mul_left_comm, mul_comm] using h₁
  · simpa only [stage136RestrictedEdges, Nat.cast_sum] using h₂

theorem lemma_13_7_printed_of_empty_heights_with_step_span {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136DataPrinted S D E F)
    (hI : criticalHeights S D E = ∅) :
    ∃ G : Stage137Data N, IsStage137DataPrinted S D E F G ∧
      ∃ t : Nat, 0 < t ∧ G.S.step = (t : ZMod N) * F.R.step ∧
        t * (G.S.length - 1) < F.R.length := by
  classical
  have hR := stage136_progression_nonempty S D E F hF.to_encoded
  have hcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hn : 0 < F.R.length := by simpa only [hcard] using hR.card_pos
  have hnR : (0 : Real) < F.R.length := by exact_mod_cast hn
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hα := S.alpha_pos
  have hQ : E.Q.length = 0 := by
    by_contra hQ
    have hQpos : (0 : Real) < E.Q.length := by exact_mod_cast Nat.pos_of_ne_zero hQ
    have hb := hF.2.2.2.2.2.2
    rw [hI] at hb
    have hp : 0 < (2 : Real) ^ (-(31 : Int)) * S.alpha ^ 160 *
        E.Q.length * F.R.length * N := by positivity
    exact not_le_of_gt hp (by simpa only [Finset.sum_empty, Nat.cast_zero] using hb)
  have hexp : (2 : Real) ^ (-(66 : Int)) * S.alpha ^ 256 ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(66 : Int)) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  have hwidth : (F.R.length : Real) ^
      ((2 : Real) ^ (-(66 : Int)) * S.alpha ^ 256) ≤ F.R.length :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hn) hexp
  refine ⟨⟨0, F.R, ∅⟩, ⟨?_, Finset.empty_subset _⟩,
    1, by omega, by simp, by simpa using Nat.sub_lt hn (by omega : 0 < 1)⟩
  refine ⟨hF.2.1, hF.2.2.1, Finset.Subset.refl _, hwidth,
    Finset.empty_subset _, ?_, ?_, ?_⟩
  · simp [hI]
  · simp [hQ]
  · intro h hh
    simp only [hI, Finset.notMem_empty] at hh

/-- At every scale, row extraction preserves the integer span
needed for short-parent localization and the common-step square construction. -/
theorem lemma_13_7_printed_all_scales_with_step_span {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136DataPrinted S D E F)
    :
    ∃ G : Stage137Data N, IsStage137DataPrinted S D E F G ∧
      ∃ t : Nat, 0 < t ∧ G.S.step = (t : ZMod N) * F.R.step ∧
        t * (G.S.length - 1) < F.R.length := by
  classical
  by_cases hI : (criticalHeights S D E).Nonempty
  swap
  · exact lemma_13_7_printed_of_empty_heights_with_step_span S D E F hF
      (Finset.not_nonempty_iff_eq_empty.mp hI)
  have hR := stage136_progression_nonempty S D E F hF.to_encoded
  have hRcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hRlen : 0 < F.R.length := by simpa only [hRcard] using hR.card_pos
  have hY := hF.2.2.2.2.1
  obtain ⟨y, hy₁, hy₂⟩ := stage136Printed_exists_base_row S D E F hF
  have hdense : (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * F.R.length ≤
      (F.R.carrier.filter fun x ↦ (x, y) ∈ S.A).card := by
    have h := stage137_base_row_density S.A F.R.carrier (criticalHeights S D E)
      F.Y y hI (fun h hh ↦ (hY h hh).1)
      (δ := (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128)
      (by simpa only [hRcard] using hy₁)
    simpa only [hRcard] using h
  let delta : Real := (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128
  let A := F.R.carrier.filter fun x ↦ (x, y) ∈ S.A
  have hα := S.alpha_pos
  have hδ : 0 < delta := mul_pos (zpow_pos (by norm_num) _) (pow_pos hα _)
  have hδone : delta ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(26 : Int)) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  obtain ⟨q, P, hP, hcell, t, ht, hspan⟩ := corollary_7_11_all_scales_universal_with_step_span
    N F.R A delta hF.2.2.1 hF.2.1 hRlen hδ hδone (Finset.filter_subset _ _) hdense
  obtain ⟨i, hi₁, hi₂⟩ := exists_stage137_partition_cell_two_bounds
    F.R.carrier (criticalHeights S D E) (fun i ↦ (P i).carrier) F.Y y hR hP
    (b₁ := (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (criticalHeights S D E).card)
    (b₂ := (2 : Real) ^ (-(31 : Int)) * S.alpha ^ 160 * E.Q.length)
    (by simpa only [hRcard, mul_assoc, mul_left_comm, mul_comm] using hy₁)
    (by simpa only [hRcard] using hy₂)
  obtain ⟨hstep, hproper, hlength, hlinear⟩ := hcell i
  have hbase : LinearOn ((P i).carrier.filter fun x ↦ (x, y) ∈ S.A)
      (fun x ↦ S.phi (x, y)) := by
    obtain ⟨a, b, hab⟩ := hlinear (fun x ↦ S.phi (x, y))
      (section13_base_row_freiman S F.R.carrier y)
    refine ⟨a, b, fun x hx => ?_⟩
    obtain ⟨hxP, hxA⟩ := Finset.mem_filter.mp hx
    exact hab x (Finset.mem_filter.mpr
      ⟨hxP, Finset.mem_filter.mpr ⟨hP.cell_subset i hxP, hxA⟩⟩)
  have hcard : (P i).carrier.card = (P i).length := hproper
  let B := stage137UpperEndpoints (P i).carrier (criticalHeights S D E) F.Y y
  refine ⟨⟨y, P i, B⟩, ⟨?_, ?_⟩, t, ht, (hspan i).1, (hspan i).2⟩
  · refine ⟨hstep, hproper, hP.cell_subset i, ?_, Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · simpa only [delta, stage137Printed_partition_exponent] using hlength
    · simpa only [hcard, mul_assoc, mul_left_comm, mul_comm] using hi₁
    · simpa only [hcard] using hi₂
    · exact stage137UpperEndpoints_rows_linear S.A S.phi F.R.carrier (P i).carrier
        (criticalHeights S D E) F.Y y (hP.cell_subset i)
        (fun h hh ↦ (hY h hh).1) hbase (fun h hh ↦ (hY h hh).2.2)
  · exact stage137UpperEndpoints_subset_domain S.A (P i).carrier
      (criticalHeights S D E) F.Y y (fun h hh ↦ (hY h hh).1)


def lemma_13_7_printed_bounds : Prop :=
  ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N) (D : Stage134Data N)
    (E : Stage135Data N) (F : Stage136Data N), IsStage136DataPrinted S D E F →
      ∃ G : Stage137Data N, IsStage137DataPrinted S D E F G ∧
        ∃ t : Nat, 0 < t ∧ G.S.step = (t : ZMod N) * F.R.step ∧
          t * (G.S.length - 1) < F.R.length

theorem lemma_13_7_printed_bounds_holds : lemma_13_7_printed_bounds := by
  intro N _ S D E F hF
  exact lemma_13_7_printed_all_scales_with_step_span S D E F hF

end LeanProofs.GowersSzemeredi
