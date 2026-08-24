import GowersSzemeredi.Sections01_03
import Mathlib.Combinatorics.HalesJewett

/-!
# Headline combinatorial proofs for Gowers (2001), Section 1

This module connects the paper's concrete finite-interval formulation of van
der Waerden's theorem to Mathlib's Hales--Jewett theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

open Combinatorics

/-- A combinatorial line becomes an ordinary arithmetic progression after
summing the coordinates of its words. -/
private theorem line_wordValue_eq {k : Nat} [NeZero k] {ι : Type*} [Fintype ι]
    (l : Line (Fin k) ι) (x : Fin k) :
    1 + ∑ j, ((l x j : Fin k) : Nat) =
      1 + ∑ j, ((l 0 j : Fin k) : Nat) +
        (x : Nat) * ∑ j, if l.idxFun j = none then 1 else 0 := by
  have hcoord (j : ι) :
      ((l x j : Fin k) : Nat) = ((l 0 j : Fin k) : Nat) +
        (x : Nat) * if l.idxFun j = none then 1 else 0 := by
    cases h : l.idxFun j with
    | none => simp [Line.coe_apply, h]
    | some y => simp [Line.coe_apply, h]
  simp_rw [hcoord, sum_add_distrib, mul_sum]
  omega

/-- **Gowers, Theorem 1.1 (van der Waerden).** -/
theorem theorem_1_1_holds : theorem_1_1 := by
  intro k r hk hr
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  obtain ⟨ι, instι, hHJ⟩ :=
    Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  let wordValue : (ι → Fin k) → Nat := fun v => 1 + ∑ j, (v j : Nat)
  let M := 1 + Fintype.card ι * (k - 1)
  refine ⟨M, by simp [M], ?_⟩
  intro color
  obtain ⟨l, c, hl⟩ := hHJ (color ∘ wordValue)
  let d := ∑ j, if l.idxFun j = none then 1 else 0
  let a := wordValue (l 0)
  have hd : 0 < d := by
    obtain ⟨j, hj⟩ := l.proper
    have hjmem : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ j
    have hone : (if l.idxFun j = none then 1 else 0) = 1 := by simp [hj]
    have hle : (if l.idxFun j = none then 1 else 0) ≤
        ∑ q ∈ (Finset.univ : Finset ι), if l.idxFun q = none then 1 else 0 := by
      exact Finset.single_le_sum (fun q _ => Nat.zero_le
        (if l.idxFun q = none then 1 else 0)) hjmem
    have : 1 ≤ d := by simpa [d, hone] using hle
    omega
  refine ⟨a, d, c, hd, ?_⟩
  intro i hi
  let x : Fin k := ⟨i, hi⟩
  have hvalue : wordValue (l x) = a + i * d := by
    simpa [wordValue, a, d, x] using line_wordValue_eq l x
  constructor
  · rw [← hvalue]
    apply Finset.mem_Icc.mpr
    constructor
    · simp [wordValue]
    · dsimp [wordValue, M]
      have hcoord (j : ι) : ((l x j : Fin k) : Nat) ≤ k - 1 := by
        exact Nat.le_pred_of_lt (l x j).isLt
      calc
        1 + ∑ j, ((l x j : Fin k) : Nat) ≤
            1 + ∑ _j : ι, (k - 1) := by
              gcongr with j
              exact hcoord j
        _ = 1 + Fintype.card ι * (k - 1) := by simp
  · rw [← hvalue]
    exact hl x

end LeanProofs.GowersSzemeredi
