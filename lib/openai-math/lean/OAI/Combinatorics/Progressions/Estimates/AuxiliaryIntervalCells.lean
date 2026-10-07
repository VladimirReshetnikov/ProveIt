import OAI.Combinatorics.Progressions.Lattices.BoxResiduePartition

namespace OAI

section

namespace Erdos3

noncomputable def intervalAuxiliaryCell (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N)))) :
    P.Label × CompatibleAuxResidue M d u :=
  (intervalResidueCell a P r b x,
    compatibleAuxResidueOfPoint M d hd u x.val (hbase x.val (Finset.mem_filter.mp x.property).2))

theorem intervalAuxiliaryCell_eq_iff (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N))))
    (k : P.Label × CompatibleAuxResidue M d u) :
    intervalAuxiliaryCell a P M d hd u r b hbase x = k ↔
      (intervalCellLower a P k.1 ≤ x.val ∧ x.val < intervalCellUpper a P k.1) ∧
        x.val ≡ (k.2.val.val : ℤ) [ZMOD (d : ℤ)] := by
  rcases k with ⟨j, v⟩
  simp only [intervalAuxiliaryCell, Prod.mk.injEq, intervalResidueCell_eq_iff a P hstep,
    compatibleAuxResidueOfPoint_eq_iff]

noncomputable def intervalAuxiliaryCellEquiv (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (hpos : ∀ k, 0 < P.length k)
    (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (k : P.Label × CompatibleAuxResidue M d u) (R c : ℤ)
    (hcombine : ∀ x : ℤ,
      (x ≡ b [ZMOD r] ∧ x ≡ (k.2.val.val : ℤ) [ZMOD (d : ℤ)]) ↔ x ≡ c [ZMOD R]) :
    {x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N))) //
      intervalAuxiliaryCell a P M d hd u r b hbase x = k} ≃
      ↥(Finset.filter (fun x => x ≡ c [ZMOD R])
        (Finset.Ico (intervalCellLower a P k.1) (intervalCellUpper a P k.1))) where
  toFun x := by
    have hx := (intervalAuxiliaryCell_eq_iff a P hstep M d hd u r b hbase x.val k).mp x.property
    exact ⟨x.val.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hx.1,
      (hcombine x.val.val).mp ⟨(Finset.mem_filter.mp x.val.property).2, hx.2⟩⟩⟩
  invFun x := by
    have hx := Finset.mem_filter.mp x.property
    have hinterval := Finset.mem_Ico.mp hx.1
    have hr := (hcombine x.val).mpr hx.2
    have hend := P.end_le_of_step_one hstep k.1 (hpos k.1)
    have hend' : (P.start k.1 : ℤ) + P.length k.1 ≤ N := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ P.start k.1 := Int.natCast_nonneg _
    have houter : x.val ∈ Finset.Ico a (a + N) := by
      simp only [intervalCellLower, intervalCellUpper] at hinterval
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    let y : ↥(Finset.filter (fun z => z ≡ b [ZMOD r]) (Finset.Ico a (a + N))) :=
      ⟨x.val, Finset.mem_filter.mpr ⟨houter, hr.1⟩⟩
    exact ⟨y, (intervalAuxiliaryCell_eq_iff a P hstep M d hd u r b hbase y k).mpr
      ⟨hinterval, hr.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
