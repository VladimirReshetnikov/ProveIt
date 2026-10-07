import OAI.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
import OAI.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
import OAI.Combinatorics.Progressions.Probability.ComplexPartitionMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerResidueCount (a b r v : ℤ) : ℕ :=
  (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card

noncomputable def rectangularResidueCount {I : Type*} [Fintype I] (a b r v : I → ℤ) : ℕ :=
  ∏ i, integerResidueCount (a i) (b i) (r i) (v i)

noncomputable def integerRectangleVolume {I : Type*} [Fintype I] (a b : I → ℤ) : ℝ :=
  ∏ i, ((b i - a i : ℤ) : ℝ)

theorem rectangularResidueCount_eq_card {I : Type*} [Fintype I] [DecidableEq I] (a b r v : I → ℤ) :
    rectangularResidueCount a b r v = Fintype.card
      (∀ i, ↥(Finset.filter (fun x => x ≡ v i [ZMOD r i]) (Finset.Ico (a i) (b i)))) := by
  classical
  rw [Fintype.card_pi]
  simp [rectangularResidueCount, integerResidueCount]

theorem rectangularResidueCount_relative_error {I : Type*} [Fintype I]
    (a b r v : I → ℤ) (hab : ∀ i, a i < b i) (hr : ∀ i, 0 < r i)
    (hsmall : (∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) ≤ 1 / 2) :
    |(∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) - integerRectangleVolume a b| ≤
      (2 * ∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) * integerRectangleVolume a b := by
  let L : I → ℝ := fun i => ((b i - a i : ℤ) : ℝ)
  let c : I → ℝ := fun i => integerResidueCount (a i) (b i) (r i) (v i)
  let f : I → ℝ := fun i => c i * r i / L i
  let e : I → ℝ := fun i => (r i : ℝ) / L i
  have hL (i) : 0 < L i := by
    dsimp only [L]
    exact_mod_cast sub_pos.mpr (hab i)
  have hrR (i) : (0 : ℝ) < r i := by exact_mod_cast hr i
  have hV : 0 < integerRectangleVolume a b := Finset.prod_pos (fun i _ => hL i)
  have hprod := positive_prod_sub_one_le_twice_sum Finset.univ f e
    (fun i _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hrR i).le) (hL i).le)
    (fun i _ => (div_pos (hrR i) (hL i)).le)
    (fun i _ => scalarResidue_relative_count_error (a i) (b i) (r i) (v i) (hab i) (hr i)) hsmall
  have heq : (∏ i, f i) * integerRectangleVolume a b =
      (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
    change (∏ i, f i) * (∏ i, L i) = _
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i, f i * L i) = ∏ i, c i * r i := by
        apply Finset.prod_congr rfl
        intro i _
        exact div_mul_cancel₀ (c i * r i) (hL i).ne'
      _ = (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
        simp only [Finset.prod_mul_distrib, rectangularResidueCount, Nat.cast_prod, c]
        ring
  calc
    _ = |((∏ i, f i) - 1) * integerRectangleVolume a b| := by
      rw [← heq]
      congr 1
      ring
    _ = |(∏ i, f i) - 1| * integerRectangleVolume a b := by rw [abs_mul, abs_of_pos hV]
    _ ≤ (2 * ∑ i, e i) * integerRectangleVolume a b := mul_le_mul_of_nonneg_right hprod hV.le

end Erdos3

end

section

namespace Erdos3

noncomputable def integerIntervalEquivFin (a : ℤ) (N : ℕ) :
    ↥(Finset.Ico a (a + N)) ≃ Fin N where
  toFun x := ⟨(x.val - a).toNat, by have hx := Finset.mem_Ico.mp x.property; omega⟩
  invFun n := ⟨a + n.val, by simp only [Finset.mem_Ico]; omega⟩
  left_inv x := by
    apply Subtype.ext
    have hx := Finset.mem_Ico.mp x.property
    dsimp only
    omega
  right_inv n := by
    apply Fin.ext
    dsimp only
    omega

theorem integerIntervalEquivFin_val (a : ℤ) (N : ℕ) (x : ↥(Finset.Ico a (a + N))) :
    ((integerIntervalEquivFin a N x).val : ℤ) = x.val - a := by
  have hx := Finset.mem_Ico.mp x.property
  change (((x.val - a).toNat : ℕ) : ℤ) = x.val - a
  omega

@[simp] theorem integerIntervalEquivFin_symm_val (a : ℤ) (N : ℕ) (n : Fin N) :
    ((integerIntervalEquivFin a N).symm n).val = a + n.val := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rectangularResidueCount_pos {I : Type*} [Fintype I]
    (a b r v : I → ℤ) (hab : ∀ i, a i < b i) (hr : ∀ i, 0 < r i)
    (hsmall : (∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) < 1 / 2) :
    0 < rectangularResidueCount a b r v := by
  have hV : 0 < integerRectangleVolume a b :=
    Finset.prod_pos (fun i _ => by exact_mod_cast sub_pos.mpr (hab i))
  have hR : 0 < ∏ i, (r i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hr i)
  have hlower := (abs_le.mp (rectangularResidueCount_relative_error a b r v hab hr hsmall.le)).1
  have hmargin : 0 < (1 - 2 * ∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) * integerRectangleVolume a b :=
    mul_pos (by linarith) hV
  have hprod : 0 < (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by nlinarith
  exact_mod_cast (mul_pos_iff_of_pos_left hR).mp hprod

theorem rectangularResidueLaws_l1 {K I : Type*} [Fintype K] [Nonempty K] [Fintype I]
    (a b : K → I → ℤ) (r s : I → ℤ) (v w : K → I → ℤ)
    (hab : ∀ k i, a k i < b k i) (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    {ε : ℝ} (hε : ε < 1 / 2)
    (hsmallR : ∀ k, (∑ i, (r i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε)
    (hsmallS : ∀ k, (∑ i, (s i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε) :
    0 < (∑ k, (rectangularResidueCount (a k) (b k) r (v k) : ℝ)) ∧
    0 < (∑ k, (rectangularResidueCount (a k) (b k) s (w k) : ℝ)) ∧
    (∑ k, |(rectangularResidueCount (a k) (b k) r (v k) : ℝ) /
        (∑ j, (rectangularResidueCount (a j) (b j) r (v j) : ℝ)) -
      (rectangularResidueCount (a k) (b k) s (w k) : ℝ) /
        (∑ j, (rectangularResidueCount (a j) (b j) s (w j) : ℝ))|) ≤ 8 * ε := by
  let f : K → ℝ := fun k => integerRectangleVolume (a k) (b k)
  let R : ℝ := ∏ i, (r i : ℝ)
  let S : ℝ := ∏ i, (s i : ℝ)
  let cr : K → ℝ := fun k => rectangularResidueCount (a k) (b k) r (v k)
  let cs : K → ℝ := fun k => rectangularResidueCount (a k) (b k) s (w k)
  let g : K → ℝ := fun k => R * cr k
  let h : K → ℝ := fun k => S * cs k
  have hf (k) : 0 < f k := Finset.prod_pos (fun i _ => by exact_mod_cast sub_pos.mpr (hab k i))
  have hR : 0 < R := Finset.prod_pos (fun i _ => by exact_mod_cast hr i)
  have hS : 0 < S := Finset.prod_pos (fun i _ => by exact_mod_cast hs i)
  have hfMass : 0 < ∑ k, f k := Finset.sum_pos (fun k _ => hf k) Finset.univ_nonempty
  have hg (k) : 0 ≤ g k := mul_nonneg hR.le (Nat.cast_nonneg _)
  have hh (k) : 0 ≤ h k := mul_nonneg hS.le (Nat.cast_nonneg _)
  have hgerr (k) : |g k - f k| ≤ (2 * ε) * f k := by
    exact (rectangularResidueCount_relative_error (a k) (b k) r (v k) (hab k) hr
      ((hsmallR k).trans hε.le)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsmallR k) (by norm_num)) (hf k).le)
  have hherr (k) : |h k - f k| ≤ (2 * ε) * f k := by
    exact (rectangularResidueCount_relative_error (a k) (b k) s (w k) (hab k) hs
      ((hsmallS k).trans hε.le)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsmallS k) (by norm_num)) (hf k).le)
  have hgMass := finite_weight_mass_pos_of_relative_error f g hfMass (by linarith : 2 * ε < 1) hgerr
  have hhMass := finite_weight_mass_pos_of_relative_error f h hfMass (by linarith : 2 * ε < 1) hherr
  have hgsum : (∑ k, g k) = R * ∑ k, cr k := (Finset.mul_sum _ _ _).symm
  have hhsum : (∑ k, h k) = S * ∑ k, cs k := (Finset.mul_sum _ _ _).symm
  have hcr : 0 < ∑ k, cr k := (mul_pos_iff_of_pos_left hR).mp (hgsum ▸ hgMass)
  have hcs : 0 < ∑ k, cs k := (mul_pos_iff_of_pos_left hS).mp (hhsum ▸ hhMass)
  have hgnorm (k) : g k / (∑ j, g j) = cr k / (∑ j, cr j) := by
    rw [hgsum]
    dsimp only [g]
    field_simp
  have hhnorm (k) : h k / (∑ j, h j) = cs k / (∑ j, cs j) := by
    rw [hhsum]
    dsimp only [h]
    field_simp
  have hbound := normalized_finite_weights_pair_l1 f g h hg hh hfMass hgMass hhMass hgerr hherr
  simp only [hgnorm, hhnorm] at hbound
  refine ⟨hcr, hcs, hbound.trans_eq ?_⟩
  ring

theorem exists_rectangular_residue_piece_discrepancy {K I : Type*}
    [Fintype K] [Nonempty K] [Fintype I]
    (a b : K → I → ℤ) (r s : I → ℤ) (v w : K → I → ℤ)
    (hab : ∀ k i, a k i < b k i) (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    {ε : ℝ} (hε : ε < 1 / 2)
    (hsmallR : ∀ k, (∑ i, (r i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε)
    (hsmallS : ∀ k, (∑ i, (s i : ℝ) / ((b k i - a k i : ℤ) : ℝ)) ≤ ε)
    (F G : K → ℂ) (hG : ∀ k, ‖G k‖ ≤ 1) :
    let nr : K → ℝ := fun k => rectangularResidueCount (a k) (b k) r (v k)
    let ns : K → ℝ := fun k => rectangularResidueCount (a k) (b k) s (w k)
    ∃ k, 0 < nr k ∧ 0 < ns k ∧
      ‖(∑ j, (nr j : ℂ) * F j) / ((∑ j, nr j : ℝ) : ℂ) -
        (∑ j, (ns j : ℂ) * G j) / ((∑ j, ns j : ℝ) : ℂ)‖ - 8 * ε ≤ ‖F k - G k‖ := by
  intro nr ns
  obtain ⟨hnr, hns, hl1⟩ := rectangularResidueLaws_l1 a b r s v w hab hr hs hε hsmallR hsmallS
  let p := FiniteProbabilityWeights.ofPositiveWeights nr (fun _ => Nat.cast_nonneg _) hnr
  let q := FiniteProbabilityWeights.ofPositiveWeights ns (fun _ => Nat.cast_nonneg _) hns
  obtain ⟨k, hk, hgap⟩ := p.exists_piece_discrepancy_of_weight_l1 q F G hG hl1
  have hk' : 0 < nr k / (∑ j, nr j) := hk
  have hkS : 0 < ns k := by
    change (0 : ℝ) < (rectangularResidueCount (a k) (b k) s (w k) : ℝ)
    exact_mod_cast rectangularResidueCount_pos (a k) (b k) s (w k) (hab k) hs ((hsmallS k).trans_lt hε)
  refine ⟨k, (div_pos_iff_of_pos_right hnr).mp hk', hkS, ?_⟩
  simpa only [p, q, FiniteProbabilityWeights.ofPositiveWeights_complexMean] using hgap

end Erdos3

end

section

namespace Erdos3

noncomputable def intervalCellLower (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) : ℤ :=
  a + P.start k

noncomputable def intervalCellUpper (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) : ℤ :=
  a + P.start k + P.length k

noncomputable def intervalResidueCell (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (r v : ℤ) :
    ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N))) → P.Label :=
  fun x => P.cell (integerIntervalEquivFin a N ⟨x.val, (Finset.mem_filter.mp x.property).1⟩)

theorem intervalResidueCell_eq_iff (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (r v : ℤ)
    (x : ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N)))) (k : P.Label) :
    intervalResidueCell a P r v x = k ↔
      intervalCellLower a P k ≤ x.val ∧ x.val < intervalCellUpper a P k := by
  let y := integerIntervalEquivFin a N ⟨x.val, (Finset.mem_filter.mp x.property).1⟩
  have hy : (y.val : ℤ) = x.val - a := integerIntervalEquivFin_val a N _
  change P.cell y = k ↔ _
  rw [P.cell_eq_iff_of_step_one hstep]
  unfold intervalCellLower intervalCellUpper
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : (P.start k : ℤ) ≤ y.val := by exact_mod_cast hlo
    have hhi' : (y.val : ℤ) < (P.start k : ℤ) + P.length k := by exact_mod_cast hhi
    omega
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h : (P.start k : ℤ) ≤ y.val := by omega
      exact_mod_cast h
    · have h : (y.val : ℤ) < (P.start k : ℤ) + P.length k := by omega
      exact_mod_cast h

noncomputable def intervalResidueCellEquiv (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (hpos : ∀ k, 0 < P.length k) (r v : ℤ) (k : P.Label) :
    {x : ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N))) //
      intervalResidueCell a P r v x = k} ≃
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r])
        (Finset.Ico (intervalCellLower a P k) (intervalCellUpper a P k))) where
  toFun x := ⟨x.val.val, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ((intervalResidueCell_eq_iff a P hstep r v x.val k).mp x.property),
      (Finset.mem_filter.mp x.val.property).2⟩⟩
  invFun x := by
    have hx := Finset.mem_filter.mp x.property
    have hinterval := Finset.mem_Ico.mp hx.1
    have hend := P.end_le_of_step_one hstep k (hpos k)
    have hend' : (P.start k : ℤ) + P.length k ≤ N := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ P.start k := Int.natCast_nonneg _
    have houter : x.val ∈ Finset.Ico a (a + N) := by
      simp only [intervalCellLower, intervalCellUpper] at hinterval
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    let y : ↥(Finset.filter (fun z => z ≡ v [ZMOD r]) (Finset.Ico a (a + N))) :=
      ⟨x.val, Finset.mem_filter.mpr ⟨houter, hx.2⟩⟩
    exact ⟨y, (intervalResidueCell_eq_iff a P hstep r v y k).mpr hinterval⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev IntegerResidueBox {I : Type*} (a b r v : I → ℤ) :=
  ∀ i, ↥(Finset.filter (fun x => x ≡ v i [ZMOD r i]) (Finset.Ico (a i) (b i)))

noncomputable def boxIntervalResidueCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r v : I → ℤ)
    (x : IntegerResidueBox a (fun i => a i + N i) r v) : ∀ i, (P i).Label :=
  fun i => intervalResidueCell (a i) (P i) (r i) (v i) (x i)

noncomputable def boxIntervalResidueCellEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (r v : I → ℤ) (k : ∀ i, (P i).Label) :
    ↥(partitionCell (boxIntervalResidueCell a N P r v) k) ≃
      IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i))
        (fun i => intervalCellUpper (a i) (P i) (k i)) r v := by
  let e₁ : ↥(partitionCell (boxIntervalResidueCell a N P r v) k) ≃
      {x : IntegerResidueBox a (fun i => a i + N i) r v //
        ∀ i, intervalResidueCell (a i) (P i) (r i) (v i) (x i) = k i} :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, boxIntervalResidueCell, funext_iff])
  exact e₁.trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight (fun i =>
    intervalResidueCellEquiv (a i) (P i) (hstep i) (hpos i) (r i) (v i) (k i))))

theorem boxIntervalResidueCell_card {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (r v : I → ℤ) (k : ∀ i, (P i).Label) :
    (partitionCell (boxIntervalResidueCell a N P r v) k).card =
      rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i))
        (fun i => intervalCellUpper (a i) (P i) (k i)) r v := by
  have he := Fintype.card_congr (boxIntervalResidueCellEquiv a N P hstep hpos r v k)
  calc
    _ = Fintype.card (IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i))
        (fun i => intervalCellUpper (a i) (P i) (k i)) r v) := by
      simpa only [Fintype.card_coe] using he
    _ = _ := (rectangularResidueCount_eq_card _ _ _ _).symm

theorem boxIntervalResidue_mixture {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (r v : I → ℤ) (f : IntegerResidueBox a (fun i => a i + N i) r v → ℂ) :
    (𝔼 x, f x) = ∑ k : (∀ i, (P i).Label),
      ((rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i))
          (fun i => intervalCellUpper (a i) (P i) (k i)) r v : ℝ) /
        (∑ j : (∀ i, (P i).Label), (rectangularResidueCount
          (fun i => intervalCellLower (a i) (P i) (j i))
          (fun i => intervalCellUpper (a i) (P i) (j i)) r v : ℝ)) : ℂ) *
      (𝔼 x ∈ partitionCell (boxIntervalResidueCell a N P r v) k, f x) := by
  have hm := complex_expect_partition_count_weights (boxIntervalResidueCell a N P r v) f
  simpa only [boxIntervalResidueCell_card a N P hstep hpos r v] using hm

end Erdos3

end

end OAI
