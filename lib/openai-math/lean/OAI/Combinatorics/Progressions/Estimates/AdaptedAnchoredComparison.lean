import OAI.Combinatorics.Progressions.Lattices.ResidueEventOrDescent

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem anchored_auxiliary_piece_residue_pair {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} (T : D.Niltest (fun _ : σ => 1))
    (lo : σ → ℤ) (N : σ → ℕ) (cells : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (cells i).step k = 1) (hpos : ∀ i k, 0 < (cells i).length k)
    (M P : ℕ) (hM : 0 < M) (hP : 0 < P) (u v : σ → ℤ) (J : σ → ℕ)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (hcop : ∀ i, (M * (M * P)).Coprime (J i))
    (k : AuxiliaryBoxLabels cells (fun _ => M) (fun _ => M * P) u)
    (hk₀ : 0 < (partitionCell (baseAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P)
      (fun _ => Nat.mul_pos hM hP) u) k).card)
    (hk₁ : 0 < (partitionCell (refinedAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P) J
      (fun _ => Nat.mul_pos hM hP) u v hv) k).card) :
    let Q := Nat.lcm M (M * P)
    let lo' : σ → ℤ := fun i => intervalCellLower (lo i) (cells i) (k i).1
    let N' : σ → ℕ := fun i => (cells i).length (k i).1
    ∃ w z : σ → ℤ,
      (∀ i, lo' i ≤ w i ∧ w i < lo' i + N' i) ∧
      (∀ i, lo' i ≤ z i ∧ z i < lo' i + N' i) ∧
      (∀ i, w i ≡ u i [ZMOD (M : ℤ)]) ∧
      (∀ i, z i ≡ v i [ZMOD (M * J i : ℕ)]) ∧
      (∀ i, z i ≡ w i [ZMOD (Q : ℤ)]) ∧
      Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w) ∧
      Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z) ∧
      let S := T.scalarAffinePullback (Q / M : ℕ) (fun i => (commonStrideIndex u M w i : ℚ))
      (𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u) k, residueBoxStrideValue T.eval u M x) =
        residuePairMean S.eval lo' N' Q w z J false ∧
      (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P) J
        (fun _ => Nat.mul_pos hM hP) u v hv) k, residueBoxStrideValue T.eval u M x) =
        residuePairMean S.eval lo' N' Q w z J true := by
  intro Q lo' N'
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hk₀
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hk₁
  let w : σ → ℤ := fun i => (x i).val
  let z : σ → ℤ := fun i => (y i).val
  have hx' := (mem_boxAuxiliaryCell_iff lo N cells hstep (fun _ => M) (fun _ => M * P)
    (fun _ => Nat.mul_pos hM hP) u (fun _ => (M : ℤ)) u (fun _ _ ht => ht) k x).mp hx
  have hy' := (mem_boxAuxiliaryCell_iff lo N cells hstep (fun _ => M) (fun _ => M * P)
    (fun _ => Nat.mul_pos hM hP) u (fun i => (M * J i : ℕ)) v
    (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) k y).mp hy
  have hw : ∀ i, w i ≡ u i [ZMOD (M : ℤ)] := fun i => (Finset.mem_filter.mp (x i).property).2
  have hz : ∀ i, z i ≡ v i [ZMOD (M * J i : ℕ)] := fun i => (Finset.mem_filter.mp (y i).property).2
  have hcombine₀ : ∀ i (t : ℤ),
      (t ≡ u i [ZMOD (M : ℤ)] ∧ t ≡ ((k i).2.val.val : ℤ) [ZMOD (M * P : ℕ)]) ↔
        t ≡ w i [ZMOD (Q : ℤ)] := by
    intro i t
    exact residue_constraints_iff_lcm (hw i) (hx' i).2 t
  have hcombine₁ : ∀ i (t : ℤ),
      (t ≡ v i [ZMOD (M * J i : ℕ)] ∧ t ≡ ((k i).2.val.val : ℤ) [ZMOD (M * P : ℕ)]) ↔
        t ≡ z i [ZMOD (Q * J i : ℕ)] := by
    intro i t
    have hc := ((k i).2.refinedConstraint_iff (hcop i) (v i) (hv i) (z i)).mp ⟨hz i, (hy' i).2⟩
    exact ((k i).2.refinedConstraint_iff (hcop i) (v i) (hv i) t).trans
      ⟨fun ht => ht.trans hc.symm, fun ht => ht.trans hc⟩
  have hzw : ∀ i, z i ≡ w i [ZMOD (Q : ℤ)] := fun i => (hcombine₀ i (z i)).mp
    ⟨refinedResidue_implies_base M (J i) (u i) (v i) (hv i) (z i) (hz i), (hy' i).2⟩
  have hMQ : M ∣ Q := Nat.dvd_lcm_left M (M * P)
  refine ⟨w, z, fun i => (hx' i).1, fun i => (hy' i).1, hw, hz, hzw, ?_, ?_, ?_⟩
  · exact ⟨fun i => ⟨w i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hx' i).1, Int.ModEq.refl _⟩⟩⟩
  · exact ⟨fun i => ⟨z i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hy' i).1, Int.ModEq.refl _⟩⟩⟩
  · intro S
    constructor
    · rw [residuePairMean_false]
      exact (boxAuxiliaryCell_expect lo N cells hstep hpos (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u (fun _ => (M : ℤ)) u (fun _ _ ht => ht) k
        (fun _ => (Q : ℤ)) w hcombine₀ (fun t => T.eval (commonStrideIndex u M t))).trans
        (T.residueBoxStride_rebase lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w u w
          hM hMQ hw (fun _ _ ht => ht))
    · rw [residuePairMean_true]
      exact (boxAuxiliaryCell_expect lo N cells hstep hpos (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u (fun i => (M * J i : ℕ)) v
        (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) k
        (fun i => (Q * J i : ℕ)) z hcombine₁ (fun t => T.eval (commonStrideIndex u M t))).trans
        (T.residueBoxStride_rebase lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z u w
          hM hMQ hw (fun i => refinedResidue_implies_base Q (J i) (w i) (z i) (hzw i)))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def AnchoredChildResidueComparison {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost η δ : ℝ) (lo : σ → ℤ) (N : σ → ℕ) (M P : ℕ) (u v : σ → ℤ) (J : σ → ℕ) : Prop :=
  let Q := Nat.lcm M (M * P)
  ∃ (lo' : σ → ℤ) (N' : σ → ℕ) (w z : σ → ℤ) (U : V.Niltest (fun _ : σ => 1)),
    (∀ i, lo i ≤ lo' i ∧ lo' i + N' i ≤ lo i + N i) ∧
    (∀ i, 0 < N' i) ∧
    (∀ i, δ * (N i : ℝ) / 8 ≤ (N' i : ℝ) ∧ (N' i : ℝ) ≤ δ * (N i : ℝ) / 2) ∧
    (∀ i, lo' i ≤ w i ∧ w i < lo' i + N' i) ∧
    (∀ i, lo' i ≤ z i ∧ z i < lo' i + N' i) ∧
    (∀ i, w i ≡ u i [ZMOD (M : ℤ)]) ∧
    (∀ i, z i ≡ v i [ZMOD (M * J i : ℕ)]) ∧
    (∀ i, z i ≡ w i [ZMOD (Q : ℤ)]) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z) ∧
    U.orbit = V.filtration.realification.scalarAffineOrbitHom (Q / M : ℕ)
      (fun i => (commonStrideIndex u M w i : ℚ)) child ∧
    U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
    η ≤ ‖residuePairMean U.eval lo' N' Q w z J false - residuePairMean U.eval lo' N' Q w z J true‖

theorem anchored_child_comparison_of_piece {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost η δ : ℝ) (lo : σ → ℤ) (N H : σ → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (hlower : ∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ))
    (hupper : ∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4)
    (M P : ℕ) (hM : 0 < M) (hP : 0 < P) (u v : σ → ℤ) (J : σ → ℕ)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (hcop : ∀ i, (M * (M * P)).Coprime (J i))
    (k : AuxiliaryBoxLabels (comparableBoxPartitions N H hH hHN) (fun _ => M) (fun _ => M * P) u)
    (hk₀ : 0 < (partitionCell (baseAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
      (fun _ => M) (fun _ => M * P) (fun _ => Nat.mul_pos hM hP) u) k).card)
    (hk₁ : 0 < (partitionCell (refinedAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
      (fun _ => M) (fun _ => M * P) J (fun _ => Nat.mul_pos hM hP) u v hv) k).card)
    (U : V.Niltest (fun _ : σ => 1)) (hU : U.orbit = child) (hunit : U.UnitIntervalValued)
    (hcost : U.ComplexityLE cost)
    (hgap : η ≤ ‖(𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
        (fun _ => M) (fun _ => M * P) (fun _ => Nat.mul_pos hM hP) u) k, residueBoxStrideValue U.eval u M x) -
      (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
        (fun _ => M) (fun _ => M * P) J (fun _ => Nat.mul_pos hM hP) u v hv) k, residueBoxStrideValue U.eval u M x)‖) :
    AnchoredChildResidueComparison V child cost η δ lo N M P u v J := by
  let cells := comparableBoxPartitions N H hH hHN
  have hstep : ∀ i j, (cells i).step j = 1 := comparableBoxPartitions_step N H hH hHN
  have hpos : ∀ i j, 0 < (cells i).length j := fun i j =>
    (hH i).trans_le (comparableBoxPartitions_length N H hH hHN i j).1
  obtain ⟨w, z, hwpos, hzpos, hw, hz, hzw, hbase, hfine, hmean₀, hmean₁⟩ :=
    anchored_auxiliary_piece_residue_pair U lo N cells hstep hpos M P hM hP u v J hv hcop k hk₀ hk₁
  let Q := Nat.lcm M (M * P)
  let lo' : σ → ℤ := fun i => intervalCellLower (lo i) (cells i) (k i).1
  let N' : σ → ℕ := fun i => (cells i).length (k i).1
  let S := U.scalarAffinePullback (Q / M : ℕ) (fun i => (commonStrideIndex u M w i : ℚ))
  refine ⟨lo', N', w, z, S, ?_, fun i => hpos i (k i).1, ?_, hwpos, hzpos, hw, hz, hzw,
    hbase, hfine, ?_, hunit, hcost, ?_⟩
  · intro i
    have hend := (cells i).end_le_of_step_one (hstep i) (k i).1 (hpos i (k i).1)
    have hend' : ((cells i).start (k i).1 : ℤ) + (cells i).length (k i).1 ≤ N i := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ (cells i).start (k i).1 := Int.natCast_nonneg _
    dsimp only [lo', N', intervalCellLower]
    constructor <;> omega
  · intro i
    have hlen := comparableBoxPartitions_length N H hH hHN i (k i).1
    have hlo : (H i : ℝ) ≤ (N' i : ℝ) := by exact_mod_cast hlen.1
    have hhi : (N' i : ℝ) < 2 * (H i : ℝ) := by exact_mod_cast hlen.2
    exact ⟨(hlower i).trans hlo, by linarith [hupper i]⟩
  · change V.filtration.realification.scalarAffineOrbitHom (Q / M : ℕ)
      (fun i => (commonStrideIndex u M w i : ℚ)) U.orbit = _
    rw [hU]
  · exact hgap.trans_eq (congrArg norm (congrArg₂ (fun a b : ℂ => a - b) hmean₀ hmean₁))

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

theorem AnchoredChildResidueComparison.rebase
    {σ K : Type*} [Fintype σ] [DecidableEq σ] [LieRing K] [LieAlgebra ℚ K] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K t e) (F : V.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (V.basis.repr (F.basis i) j) H)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost cost' η δ : ℝ) (lo : σ → ℤ) (N : σ → ℕ) (M P : ℕ) (u v : σ → ℤ) (J : σ → ℕ)
    (hcomplex : ∀ U : V.Niltest (fun _ : σ => 1), U.ComplexityLE cost →
      (F.rebaseNiltest H hH U).ComplexityLE cost')
    (hcomparison : AnchoredChildResidueComparison V child cost η δ lo N M P u v J) :
    AnchoredChildResidueComparison F.model child cost' η δ lo N M P u v J := by
  obtain ⟨lo', N', w, z, U, hsub, hpos, hlength, hw, hz, hwu, hzv, hzw,
    hbase, hfine, horbit, hunit, hcost, hgap⟩ := hcomparison
  exact ⟨lo', N', w, z, F.rebaseNiltest H hH U, hsub, hpos, hlength, hw, hz, hwu, hzv, hzw,
    hbase, hfine, horbit, F.rebaseNiltest_unit_interval H hH U hunit, hcomplex U hcost, hgap⟩

end Erdos3

end

end OAI
