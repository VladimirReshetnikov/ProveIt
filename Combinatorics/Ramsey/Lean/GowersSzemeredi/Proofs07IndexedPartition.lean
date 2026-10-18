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
  have hfirst : R.start ∈ R.carrier := by
    exact Finset.mem_image.mpr (⟨⟨0, hl⟩, Finset.mem_univ _, by simp⟩)
  have hlast : R.start + (((R.length - 1) * R.step : Nat) : Int) ∈ R.carrier := by
    exact Finset.mem_image.mpr (⟨⟨R.length - 1, by omega⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub hfirst)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub hlast)
  have hi' : (i.val : Int) = R.start := by simpa using hi
  have hj' : (j.val : Int) = R.start + (((R.length - 1) * R.step : Nat) : Int) := by simpa using hj
  have hjL : (j.val : Int) < L := by exact_mod_cast j.isLt
  have hspan : (((R.length - 1) * R.step : Nat) : Int) < L := by omega
  have hspanNat : (R.length - 1) * R.step < L := by exact_mod_cast hspan
  simpa only [Nat.mul_comm] using hspanNat

/-- The universal affine partition retains a positive integer step ratio and
the full span bound inside the parent index interval. -/
theorem corollary_7_11_universal_modular_with_step_span (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (alpha : Real)
    (hR : R.IsProper) (hl : 0 < R.length) (hα : 0 < alpha)
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
  let P := R.asBox
  let B := liftScalarDomain A
  let U := BaseCase.boxOneIndexAP P
  let C := BaseCase.boxOneIndexDomain P B
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hUlength : U.length = R.length := hwidth
  have hBsub : B ⊆ P.carrier := fun x hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    fun i ↦ by fin_cases i; exact hA ((mem_liftScalarDomain A x).mp hx)⟩
  have hCcard : C.card = A.card := by
    rw [BaseCase.boxOneIndexDomain_card P hP B, Finset.inter_eq_left.mpr hBsub]
    simp [B, liftScalarDomain]
  have hBdomain : BaseCase.pointOneDomain B = A := by
    ext x
    rw [BaseCase.mem_pointOneDomain]
    simp [B, BaseCase.pointOneEquiv]
  -- the integer partition of the index interval, transported to cells of `R`
  obtain ⟨M, T, hTpart, hTcell, ⟨d, hd, hTd⟩, hTlinear⟩ :=
    corollary_7_11_universal_real_lower_bound N 1 U (fun _ ↦ C) alpha
      (by norm_num) hα (by simpa only [hUlength] using hl)
      (BaseCase.boxOneIndexAP_proper P)
      (fun _ ↦ ⟨BaseCase.boxOneIndexDomain_subset P B,
        by simpa only [hUlength, hCcard] using hdensity⟩)
      (by simpa only [hUlength] using hlarge)
  let Q : Fin M → ModAP N := fun j ↦ (BaseCase.indexCellBox P (T j)).axis 0
  have hQproper (j : Fin M) : (Q j).IsProper :=
    BaseCase.indexCellBox_proper P hP (T j) (hTcell j).1 (hTpart.cell_subset j) 0
  have hTlen (j : Fin M) : (R.length : Real) ^ cor711Exponent alpha 1 ≤ (T j).length := by
    simpa only [hUlength] using (hTcell j).2
  have hT2 (j : Fin M) : 2 < (T j).length := by
    exact_mod_cast (show (2 : Real) < (T j).length by linarith [hTlen j])
  have hQstep (j : Fin M) : (Q j).step ≠ 0 :=
    BaseCase.proper_modAP_step_ne_zero_of_two_le (Q j) (hQproper j) (hT2 j).le
  refine ⟨M, Q, box_one_partition_axes P (fun j ↦ BaseCase.indexCellBox P (T j))
      (BaseCase.indexCells_partition P hP T hTpart), fun j ↦ ⟨bne_iff_ne.mpr (hQstep j),
      hQproper j, hTlen j, fun phi hfreiman ↦ ?_⟩, d, hd, fun j ↦ ⟨?_, ?_⟩⟩
  · exact indexCell_scalar_linear P (T j) A phi (hTpart.cell_subset j) (hQstep j)
      (hTlinear (fun _ ↦ BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0)))
        (fun _ ↦ BaseCase.boxOneIndex_freiman P B _ (by rw [hBdomain]; exact hfreiman)) 0 j)
  · exact congrArg (fun s : Nat ↦ (s : ZMod N) * R.step) (hTd j)
  · have hspan := intAP_step_span_in_interval (T j) R.length (Nat.zero_lt_of_lt (hT2 j))
      (by simpa only [U, BaseCase.boxOneIndexAP, hwidth] using hTpart.cell_subset j)
    rwa [hTd j] at hspan

end LeanProofs.GowersSzemeredi
