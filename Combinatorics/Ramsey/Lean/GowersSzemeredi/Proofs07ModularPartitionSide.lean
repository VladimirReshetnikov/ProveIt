import GowersSzemeredi.Proofs07ModularPartition
import GowersSzemeredi.Proofs07CeilingPartitionSide

/-! Declarations of `Proofs07ModularPartition` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Corollary 7.11 on a proper modular progression, retaining the full
real-power lower length bound and explicit rounding-safe threshold. -/
theorem corollary_7_11_constant_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N) (alpha : Real)
    (hR : R.IsProper) (hl : 0 < R.length) (hα : 0 < alpha)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hfreiman : FreimanHom 8 A phi)
    (hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha 1) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) := by
  let P := R.asBox
  let B := liftScalarDomain A
  let U := BaseCase.boxOneIndexAP P
  let C := BaseCase.boxOneIndexDomain P B
  let psi := BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0))
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
  have hCfreiman : FreimanHom 8 C psi := by
    apply BaseCase.boxOneIndex_freiman
    change FreimanHom 8 (BaseCase.pointOneDomain B) phi
    rw [hBdomain]
    exact hfreiman
  obtain ⟨M, T, hTpart, hTcell, hTstep, hTlinear⟩ :=
    corollary_7_11_constant_real_lower_bound N 1 U (fun _ ↦ C) (fun _ ↦ psi) alpha
      (by norm_num) hα (by simpa only [hUlength] using hl)
      (BaseCase.boxOneIndexAP_proper P)
      (fun _ ↦ ⟨BaseCase.boxOneIndexDomain_subset P B,
        by simpa only [hUlength, hCcard] using hdensity, hCfreiman⟩)
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
  refine ⟨M, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.indexCellBox P (T j))
      (BaseCase.indexCells_partition P hP T hTpart)
  · intro j
    refine ⟨bne_iff_ne.mpr (hQstep j), hQproper j, ?_, ?_⟩
    · exact (show (R.length : Real) ^ cor711Exponent alpha 1 ≤ (T j).length by
        simpa only [hUlength] using (hTcell j).2)
    · exact indexCell_scalar_linear P (T j) A phi (hTpart.cell_subset j) (hQstep j)
        (hTlinear (0 : Fin 1) j)

/-- Corollary 7.11 on a proper modular progression, retaining the full
real-power lower length bound and explicit rounding-safe threshold. -/
theorem corollary_7_11_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N) (alpha : Real)
    (hR : R.IsProper) (hl : 0 < R.length) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hfreiman : FreimanHom 8 A phi)
    (hlarge : 4096 * Real.pi / alpha ≤ (R.length : Real) ^ cor711Exponent alpha 1) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) := by
  apply corollary_7_11_constant_modular N R A phi alpha hR hl hα hA hdensity hfreiman
  have hC : 8 ≤ 4096 * Real.pi / alpha := by
    apply (le_div_iff₀ hα).mpr
    have := Real.pi_gt_three
    nlinarith
  exact hC.trans hlarge

end LeanProofs.GowersSzemeredi
