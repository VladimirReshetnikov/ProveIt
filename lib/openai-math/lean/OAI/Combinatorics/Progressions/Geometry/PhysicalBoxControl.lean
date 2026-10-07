/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.PhysicalCellResidual

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

noncomputable def physicalBoxTruncation (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) (x : I → ℤ) : ℝ :=
  if hx : x ∈ translatedIntegerBox lo N then
    let c := physicalBoxCell lo N P ⟨x, hx⟩
    residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x
  else 0

noncomputable def physicalBoxResidual (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) (x : I → ℤ) : ℝ :=
  if x ∈ translatedIntegerBox lo N then f x - physicalBoxTruncation lo N P hpos q b f x else 0

theorem physicalBoxResidual_zero_off (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (hx : x ∉ translatedIntegerBox lo N) :
    physicalBoxResidual lo N P hpos q b f x = 0 := by
  simp only [physicalBoxResidual, ite_eq_right hx]

theorem physicalBoxResidual_eq_sub (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ x ∉ translatedIntegerBox lo N, f x = 0) (x : I → ℤ) :
    physicalBoxResidual lo N P hpos q b f x = f x - physicalBoxTruncation lo N P hpos q b f x := by
  by_cases hx : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxResidual, ite_eq_left hx]
  · simp only [physicalBoxResidual, physicalBoxTruncation, ite_eq_right hx, dite_eq_right hx, hf x hx, sub_zero]

theorem physicalBoxResidual_on_cell (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (c : ∀ i, (P i).Label) (x : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c}) :
    physicalBoxResidual lo N P hpos q b f x.val.val = f x.val.val -
      residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x.val.val := by
  simp only [physicalBoxResidual, ite_eq_left x.val.property,
    physicalBoxTruncation, dite_eq_left x.val.property]
  rw [x.property]

theorem physicalBoxResidual_cell_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ) (c : ∀ i, (P i).Label)
    (hc : ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    finiteCellMean (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) *
        (finiteCellWeights (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)).weight c := by
  exact physical_cell_residual_energy (physicalBoxCell lo N P) c
    (fun x => physicalBoxResidual lo N P hpos q b f x.val) _ _ 1 (fun _ => 0)
    (physicalBoxCell_nonempty lo N P hpos c) q b f eta hc (physicalBoxCellEquiv lo N P hstep hpos c)
    (physicalBoxResidual_on_cell lo N P hpos q b f c)

theorem physicalBoxResidual_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ)
    (hc : ∀ c : (∀ i, (P i).Label), ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)).mean
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) ≤
      1 + eta * residueTruncationCap ι b eta ^ 2 := by
  exact finite_cell_energy_aggregate (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N))
    (physicalBoxCell lo N P) (fun x => physicalBoxResidual lo N P hpos q b f x.val)
    (fun c => physicalBoxResidual_cell_energy lo N P hstep hpos q b f eta c (hc c))

theorem physicalBoxResidual_cell_residue (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ) (c : ∀ i, (P i).Label)
    (hc : ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta)
    (J : Finset ι) (hJ : J.card ≤ b) (m : ℕ) [NeZero m] (hm : m ∣ ∏ j ∈ J, q j) (r : I → ZMod m) :
    |finiteCellResidueMean (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)
      (fun x => integerVectorResidue m x.val) (fun x => physicalBoxResidual lo N P hpos q b f x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)).weight c *
        (eta * residueTruncationCap ι b eta / (m : ℝ) ^ Fintype.card I) := by
  have h := physical_cell_residual_residue (physicalBoxCell lo N P) c
    (fun x => physicalBoxResidual lo N P hpos q b f x.val) _ _ 1 (fun _ => 0)
    (physicalBoxCell_nonempty lo N P hpos c) q hpair b f eta hc (physicalBoxCellEquiv lo N P hstep hpos c)
    (physicalBoxResidual_on_cell lo N P hpos q b f c) J hJ m hm
    (fun x => integerVectorResidue m x.val) (fun _ => rfl) r
  simpa only [integerVectorResidue_card, Nat.cast_pow] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueIndexLength_one_zero (a : ℤ) (N : ℕ) :
    residueIndexLength a (a + N) 1 0 = N := by
  rw [residueIndexLength_eq_card a (a + N) 1 0 (by norm_num)]
  simp [Int.modEq_one]

theorem residueTruncationCap_nonneg (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) {eta : ℝ} (heta : 0 ≤ eta) : 0 ≤ residueTruncationCap ι b eta := by
  unfold residueTruncationCap
  positivity

theorem physicalBoxResidual_control_of_lengths {I ι : Type*}
    [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog accLog eta : ℝ) (hmodLog : 0 ≤ modLog) (heta : eta ≤ 1)
    (hacc : Real.exp (-accLog) ≤ eta) (hmoduli : ∀ j, (q j : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ i c, Real.exp (modLog * (2 * b : ℕ) + accLog + dimLog + 1) ≤ ((P i).length c : ℝ))
    (c : ∀ i, (P i).Label) :
    ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta := by
  apply residuePhysicalTruncation_control_of_lengths _ _ 1 (fun _ => 0)
    (physicalBoxCell_nonempty lo N P hpos c) q b f
    (fun x hx => hf x (physicalBoxCell_subset lo N P hstep hpos c hx))
    (by decide) (by simp) hpair modLog dimLog accLog eta hmodLog heta hacc hmoduli hdim
  intro i
  simpa only [Nat.cast_one, residueIndexLength_one_zero] using hlength i (c i)

end Erdos3

end

end OAI
