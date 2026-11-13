import DiophantineConsistency.ArithmeticWangStrip
import DiophantineConsistency.ArithmeticWangRowStep

/-! Internal Wang soundness: a marked cyclic word forces the decimal215 run to
halt before the word length, in every model of IΣ1.

The length `N`, stride `s`, columns, head positions and times are internal and
may be nonstandard; the word `a` is any Σ1-definable function. The walls come
from the least-number principle, row 1 encodes `run 1`, and an internal Σ1
induction on `k < N` carries the row encoding through every operating step.
At time `N` the origin column would show an encoded colour at most433, but
the vertical period returns it to Start's north colour435. This is the
internal counterpart of `WangTiles942Soundness.marked_halts_before_period`;
no external tiling, run, or consistency fact is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticWangSoundness
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWangTable ArithmeticWangPlane ArithmeticWangStrip ArithmeticWangRowStep
  ArithmeticCantor
open ArithmeticMachineRun215 (run run_succ run_zero)
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] ArithmeticWangPlane.pl ArithmeticWangPlane.adr
  ArithmeticMachineRun215.run ArithmeticWangPlane.Colored

theorem actCode_zero : actCode 0 = 12 := by decide +kernel

theorem cantor_zero_zero : cantor (0 : V) 0 = 0 := by
  simp [cantor, triangle]

theorem cantor_one_zero : cantor (1 : V) 0 = 1 := by
  simp [cantor, triangle, one_add_one_eq_two]

/-- The represented configuration after the first blank step: state code2,
left half1 (the written bit), right half0. -/
theorem run_one : run (1 : V) = cantor 2 (cantor 1 0) :=
  ArithmeticWangPlane.initial_run_one

section main
variable {a : V → V} [𝚺₁-Function₁ a] {N s : V} (h : MarkedWord a N s)
include h

theorem row_one (X : V) : northC (pl a N s X 1) = southC (pl a N s X 0) := by
  simpa only [zero_add] using (pl_south h X 0).symm

/-- Row 1 encodes `run 1` between the two seam walls. -/
theorem base_row {L R : V} (hL1 : 1 ≤ L) (hLN : L ≤ N)
    (hLw : northC (pl a N s (N - L) 0) = 437)
    (hLin : ∀ j, 1 ≤ j → j < L → northC (pl a N s (N - j) 0) = 434)
    (hR2 : 2 ≤ R) (hRw : northC (pl a N s (N + R) 0) = 437)
    (hRin : ∀ j, 2 ≤ j → j < R →
      northC (pl a N s (N + j) 0) = 436 ∧ westC (pl a N s (N + j) 0) = 4) :
    RowInv a N s (N - L) (N + R) 1 := by
  have hN : 1 ≤ N := one_le h
  have hlW : N - L < N := tsub_lt_self (lt_of_lt_of_le _root_.zero_lt_one hN) (lt_of_lt_of_le _root_.zero_lt_one hL1)
  have hrW : N + 1 < N + R := (add_lt_add_iff_left N).mpr (lt_of_lt_of_le (by norm_num : (1:V) < 2) hR2)
  refine ⟨?_, ?_, ?_, N + 1, hrW, lt_trans hlW (lt_add_one N), ?_⟩
  · rw [row_one h]; exact (seam_iff (pl_lt h _ _)).mp hLw
  · rw [row_one h]; exact (seam_iff (pl_lt h _ _)).mp hRw
  · rw [run_one, first_cantor]; norm_num
  intro X hXr hXl
  rw [colored_iff, row_one h, run_one]
  simp only [colorV, first_cantor, second_cantor]
  rcases lt_trichotomy X (N + 1) with hlt | heq | hgt
  · rw [if_neg (ne_of_lt hlt)]
    unfold tb
    rw [if_neg (not_le.mpr hlt)]
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hlt) with hXN | hXN
    · subst hXN
      rw [show X + 1 - X - 1 = 0 by simp, fbit_zero_eq, (origin_tile h).2.1,
        mod_eq_self_of_lt (by norm_num : (1:V) < 2)]
    · -- strictly left of Start: initial-left tiles
      have hj1 : 1 ≤ N - X := pos_iff_one_le.mp (tsub_pos_of_lt hXN)
      have h1 : N < L + X := (tsub_lt_iff_left hLN).mp hXl
      have hjL : N - X < L := (tsub_lt_iff_left hXN.le).mpr (by rwa [add_comm])
      have hX : N - (N - X) = X := tsub_tsub_cancel_of_le hXN.le
      have h434 := hLin (N - X) hj1 hjL
      rw [hX] at h434
      rw [(north_434 (pl_lt h _ _) h434).2.2]
      obtain ⟨j, hj⟩ : ∃ j, N - X = j + 1 := ⟨N - X - 1, (tsub_add_cancel_of_le hj1).symm⟩
      rw [show N + 1 - X - 1 = N - X by
        rw [tsub_right_comm, add_tsub_cancel_right], hj, fbit_succ,
        div_eq_zero_of_lt _ (by norm_num : (1:V) < 2), fbit_zero]
  · subst heq
    rw [if_pos rfl, (head_tile h).2.2.2, zero_mod]
    unfold hcV; rw [if_neg (by norm_num)]; norm_num
  · rw [if_neg (ne_of_gt hgt)]
    unfold tb
    rw [if_pos hgt.le]
    simp only [fbit_zero]
    -- strictly right of the initial head: initial-right tiles
    obtain ⟨j, rfl⟩ : ∃ j, X = N + j := ⟨X - N, (add_tsub_cancel_of_le
      (le_trans (le_add_self' N 1) hgt.le)).symm⟩
    have hj2 : 2 ≤ j := by
      have : N + 1 + 1 ≤ N + j := lt_iff_succ_le.mp hgt
      rw [add_assoc, one_add_one_eq_two] at this
      exact le_of_add_le_add_left this
    have hjR : j < R := lt_of_add_lt_add_left hXr
    obtain ⟨h6, h4⟩ := hRin j hj2 hjR
    rcases west_four (pl_lt h _ _) h4 with e | e
    · exact e.2
    · rw [h6] at e; exact absurd e (by norm_num)

/-- **Internal Wang soundness.** In every model of IΣ1, a marked cyclic word of
internal length `N` and stride `s` forces the represented decimal215 run to
halt at some time below `N`. -/
theorem marked_halts : ∃ t < N, first (run t) = 0 := by
  by_contra hcon
  have live : ∀ t < N, first (run t) ≠ 0 := fun t ht h0 => hcon ⟨t, ht, h0⟩
  obtain ⟨L, hL1, hLN, hLw, hLin⟩ := left_wall h
  obtain ⟨R, hR2, hRw, hRin⟩ := right_wall h
  have base := base_row h hL1 hLN hLw hLin hR2 hRw hRin
  have hRow : 𝚺₁-Predicate (RowInv a N s (N - L) (N + R)) := by
    unfold RowInv
    apply HierarchySymbol.Definable.and (by definability)
    apply HierarchySymbol.Definable.and (by definability)
    apply HierarchySymbol.Definable.and (by definability)
    definability
  have rows : ∀ k, k + 1 ≤ N → RowInv a N s (N - L) (N + R) (k + 1) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction with
    | hP => definability
    | zero => intro _; simpa using base
    | succ k ih =>
      intro hk
      exact row_step h (k + 1) (ih (le_trans (le_of_lt (lt_add_one _)) hk))
        (live (k + 1) (lt_of_lt_of_le (lt_add_one _) hk))
  have hN : 1 ≤ N := one_le h
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, (tsub_add_cancel_of_le hN).symm⟩
  obtain ⟨_, _, hst, H, hHr, hHl, hcol⟩ := rows M (le_of_eq hM.symm)
  have hlW : N - L < N := tsub_lt_self (lt_of_lt_of_le _root_.zero_lt_one hN) (lt_of_lt_of_le _root_.zero_lt_one hL1)
  have hrW : N < N + R := lt_add_of_pos_right N (lt_of_lt_of_le (by norm_num : (0:V) < 2) hR2)
  rw [← hM] at hst hcol
  have hc := (colored_iff _ _ _ _).mp (hcol N hrW hlW)
  have hle := colorV_le (H := H) (X := N) hst
  rw [← hc, pl_origin_N h, northC_zero] at hle
  exact absurd hle (by norm_num)

end main

/-- The same statement with the cyclic neighbours written by truncated
subtraction: east neighbour `j - 1` and next-row cell `j - s` (mod `N`). -/
theorem marked_halts_of_cyclic {a : V → V} [𝚺₁-Function₁ a] {N s : V} (hN : 0 < N)
    (hlt : ∀ j < N, a j < 942) (h0 : a 0 = 0)
    (hE : ∀ j < N, eastC (a j) = westC (a ((j + N - 1) % N)))
    (hS : ∀ j < N, southC (a j) = northC (a ((j + N * (s + 1) - s) % N))) :
    ∃ t < N, first (run t) = 0 := by
  have hN1 : 1 ≤ N := pos_iff_one_le.mp hN
  refine marked_halts (a := a) (N := N) (s := s) ⟨hN, hlt, h0, ?_, ?_⟩
  · intro j hj j' hj' hjj
    rw [hE j hj]
    congr 2
    rw [← hjj, add_tsub_assoc_of_le hN1, mod_add_mod _ _ hN,
      show j' + 1 + (N - 1) = j' + N * 1 by rw [add_assoc, add_tsub_cancel_of_le hN1, mul_one],
      mod_add_mul' _ _ hN, mod_eq_self_of_lt hj']
  · intro j hj j' hj' hjj
    rw [hS j hj]
    congr 2
    have hle : s ≤ N * (s + 1) := by
      calc s ≤ 1 * (s + 1) := by rw [one_mul]; exact le_add_self' s 1
        _ ≤ N * (s + 1) := mul_le_mul_of_nonneg_right hN1 (Arithmetic.zero_le _)
    have he : N * (s + 1) - s = (N - 1) * s + N := by
      have : N * (s + 1) = ((N - 1) * s + N) + s := by
        calc N * (s + 1) = (N - 1 + 1) * s + N := by rw [tsub_add_cancel_of_le hN1]; ring
          _ = _ := by ring
      rw [this, add_tsub_cancel_right]
    rw [← hjj, add_tsub_assoc_of_le hle, he, mod_add_mod _ _ hN]
    have : j' + s + ((N - 1) * s + N) = j' + N * (s + 1) := by
      calc j' + s + ((N - 1) * s + N) = j' + ((N - 1 + 1) * s + N) := by ring
        _ = _ := by rw [tsub_add_cancel_of_le hN1]; ring
    rw [this, mod_add_mul' _ _ hN, mod_eq_self_of_lt hj']

end DiophantineConsistency.ArithmeticWangSoundness
