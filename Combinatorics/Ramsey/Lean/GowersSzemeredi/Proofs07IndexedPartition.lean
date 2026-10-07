import GowersSzemeredi.Proofs07NinePointLinearity

/-! Retain the integer step and span of affine cells in their parent indices.
These are stronger data than a modular step-multiple identity. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A nonempty integer progression in [0,L) has step times length-minus-one
strictly smaller than L. -/
theorem intAP_step_span_in_interval (R : IntAP) (L : Nat) (hl : 0 < R.length)
    (hsub : R.carrier ⊆ ({ start := 0, step := 1, length := L } : IntAP).carrier) :
    R.step * (R.length - 1) < L := by
  classical
  have hfirst : R.start ∈ R.carrier := by
    apply Finset.mem_image.mpr
    exact ⟨⟨0, hl⟩, Finset.mem_univ _, by simp⟩
  have hlast : R.start + (((R.length - 1) * R.step : Nat) : Int) ∈ R.carrier := by
    apply Finset.mem_image.mpr
    exact ⟨⟨R.length - 1, by omega⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub hfirst)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub hlast)
  have hi' : (i.val : Int) = R.start := by simpa using hi
  have hj' : (j.val : Int) = R.start + (((R.length - 1) * R.step : Nat) : Int) := by simpa using hj
  have hstart : 0 ≤ R.start := hi' ▸ Int.natCast_nonneg i.val
  have hjL : (j.val : Int) < L := by exact_mod_cast j.isLt
  have hspan : (((R.length - 1) * R.step : Nat) : Int) < L := by omega
  have hspanNat : (R.length - 1) * R.step < L := by exact_mod_cast hspan
  simpa only [Nat.mul_comm] using hspanNat

/-- The universal affine partition retains a positive integer step ratio and
the full span bound inside the parent index interval. -/
theorem corollary_7_11_universal_modular_with_step_span (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (alpha : Real)
    (hR : R.IsProper) (hl : 0 < R.length) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha 1) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
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
    corollary_7_11_universal_real_lower_bound N 1 U (fun _ ↦ C) alpha
      (by norm_num) hα (by simpa only [hUlength] using hl)
      (BaseCase.boxOneIndexAP_proper P)
      (fun _ ↦ ⟨BaseCase.boxOneIndexDomain_subset P B,
        by simpa only [hUlength, hCcard] using hdensity⟩)
      (by simpa only [hUlength] using hlarge)
  let Q : Fin M → ModAP N := fun j ↦ (BaseCase.indexCellBox P (T j)).axis 0
  have hQproper (j : Fin M) : (Q j).IsProper :=
    BaseCase.indexCellBox_proper P hP (T j) (hTcell j).1 (hTpart.cell_subset j) 0
  have hXtwo : (2 : Real) < (R.length : Real) ^ cor711Exponent alpha 1 := by
    linarith only [hlarge]
  have hQstep (j : Fin M) : (Q j).step ≠ 0 :=
    BaseCase.proper_modAP_step_ne_zero_of_two_le (Q j) (hQproper j) (by
      have hlen : (2 : Real) < (T j).length :=
        hXtwo.trans_le (by simpa only [hUlength] using (hTcell j).2)
      have hlenNat : 2 < (T j).length := by exact_mod_cast hlen
      change 2 ≤ (T j).length
      omega)
  refine ⟨M, Q, ?_, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.indexCellBox P (T j))
      (BaseCase.indexCells_partition P hP T hTpart)
  · intro j
    refine ⟨bne_iff_ne.mpr (hQstep j), hQproper j, ?_, ?_⟩
    · exact (show (R.length : Real) ^ cor711Exponent alpha 1 ≤ (T j).length by
        simpa only [hUlength] using (hTcell j).2)
    · intro phi hfreiman
      exact indexCell_scalar_linear P (T j) A phi (hTpart.cell_subset j) (hQstep j)
        (hTlinear (fun _ ↦ BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0)))
          (fun _ ↦ hCfreiman phi hfreiman) (0 : Fin 1) j)

  · obtain ⟨d, hd, hTd⟩ := hTstep
    refine ⟨d, hd, fun j => ⟨?_, ?_⟩⟩
    · change ((T j).step : ZMod N) * R.step = (d : ZMod N) * R.step
      rw [hTd j]
    · have hlen : 0 < (T j).length := by
        have hpos : (0 : Real) < (T j).length :=
          (Real.rpow_pos_of_pos (by exact_mod_cast hl : (0 : Real) < R.length) _).trans_le
            (by simpa only [hUlength] using (hTcell j).2)
        exact_mod_cast hpos
      have hsub : (T j).carrier ⊆ ({ start := 0, step := 1, length := R.length } : IntAP).carrier := by
        simpa only [U, BaseCase.boxOneIndexAP, hwidth] using hTpart.cell_subset j
      have hspan := intAP_step_span_in_interval (T j) R.length hlen hsub
      rw [hTd j] at hspan
      exact hspan

end LeanProofs.GowersSzemeredi
