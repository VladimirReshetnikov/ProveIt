import GowersSzemeredi.Proofs07IndexedPartition

/-! Prescribed affine cell lengths with retained integer step geometry. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The universal affine partition retains a positive integer step ratio and
the full span bound inside the parent index interval. -/
theorem corollary_7_11_modular_budget_with_step_span (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (alpha : Real) (m : Nat) (hm : 2 ≤ m)
    (hR : R.IsProper) (hl : 0 < R.length) (hα : 0 < alpha)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hbudget : 34 * (m : Real) ^ 2 ≤
      (R.length : Real) ^ ((23 / 6) * cor711Exponent alpha 1)) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        m ≤ (Q j).length ∧ (Q j).length ≤ m + 1 ∧
        ∀ phi : ZMod N → ZMod N, FreimanHom 8 A phi →
          LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) ∧
      ∃ d : Nat, 0 < d ∧ ∀ j,
        (Q j).step = (d : ZMod N) * R.step ∧ d * ((Q j).length - 1) < R.length := by
  classical
  let P := R.asBox
  let B := liftScalarDomain A
  let U := BaseCase.boxOneIndexAP P
  let C := BaseCase.boxOneIndexDomain P B
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hUlength : U.length = R.length := hwidth
  have hBsub : B ⊆ P.carrier := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    fin_cases i
    exact hA ((mem_liftScalarDomain A x).mp hx)
  have hCcard : C.card = A.card := by
    rw [BaseCase.boxOneIndexDomain_card P hP B, Finset.inter_eq_left.mpr hBsub]
    simp [B, liftScalarDomain]
  have hBdomain : BaseCase.pointOneDomain B = A := by
    ext x
    rw [BaseCase.mem_pointOneDomain]
    simp [B, BaseCase.pointOneEquiv]
  have hCfreiman (phi : ZMod N → ZMod N) (hfreiman : FreimanHom 8 A phi) :
      FreimanHom 8 C (BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0))) := by
    apply BaseCase.boxOneIndex_freiman
    change FreimanHom 8 (BaseCase.pointOneDomain B) phi
    rw [hBdomain]
    exact hfreiman
  obtain ⟨M, T, hTpart, hTcell, hTstep, hTlinear⟩ :=
    corollary_7_11_universal_budget N 1 m U (fun _ ↦ C) alpha
      (by norm_num) (by omega) hα (by simpa only [hUlength] using hl)
      (BaseCase.boxOneIndexAP_proper P)
      (fun _ ↦ ⟨BaseCase.boxOneIndexDomain_subset P B,
        by simpa only [hUlength, hCcard] using hdensity⟩)
      (by simpa only [hUlength] using hbudget)
  let Q : Fin M → ModAP N := fun j ↦ (BaseCase.indexCellBox P (T j)).axis 0
  have hQproper (j : Fin M) : (Q j).IsProper :=
    BaseCase.indexCellBox_proper P hP (T j) (hTcell j).1 (hTpart.cell_subset j) 0
  have hlength (j : Fin M) : m ≤ (T j).length ∧ (T j).length ≤ m + 1 := by
    rcases (hTcell j).2 with h | h <;> omega
  have hQstep (j : Fin M) : (Q j).step ≠ 0 :=
    BaseCase.proper_modAP_step_ne_zero_of_two_le (Q j) (hQproper j)
      (hm.trans (hlength j).1)
  refine ⟨M, Q, ?_, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.indexCellBox P (T j))
      (BaseCase.indexCells_partition P hP T hTpart)
  · intro j
    refine ⟨bne_iff_ne.mpr (hQstep j), hQproper j, (hlength j).1, (hlength j).2, ?_⟩
    intro phi hfreiman
    exact indexCell_scalar_linear P (T j) A phi (hTpart.cell_subset j) (hQstep j)
        (hTlinear (fun _ ↦ BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0)))
          (fun _ ↦ hCfreiman phi hfreiman) (0 : Fin 1) j)

  · obtain ⟨d, hd, hTd⟩ := hTstep
    refine ⟨d, hd, fun j => ⟨?_, ?_⟩⟩
    · change ((T j).step : ZMod N) * R.step = (d : ZMod N) * R.step
      rw [hTd j]
    · have hlen : 0 < (T j).length := by have := (hlength j).1; omega
      have hsub : (T j).carrier ⊆ ({ start := 0, step := 1, length := R.length } : IntAP).carrier := by
        simpa only [U, BaseCase.boxOneIndexAP, hwidth] using hTpart.cell_subset j
      have hspan := intAP_step_span_in_interval (T j) R.length hlen hsub
      rw [hTd j] at hspan
      exact hspan

end LeanProofs.GowersSzemeredi
