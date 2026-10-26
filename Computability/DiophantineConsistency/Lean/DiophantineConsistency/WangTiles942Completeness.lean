import DiophantineConsistency.WangTiles942CycleBand
import DiophantineConsistency.WangTiles942Soundness
import DiophantineConsistency.DecimalMachineZFC

/-!
# Cofinal actual marked words and the literal machine endpoint

Every sufficiently large width and height may be chosen independently.
Combining the explicit band construction with the literal soundness theorem
closes the marked-word/blank-halting equivalence. The optional consistency
corollary uses the repository's existing syntactic ConZFC and is an external
Lean theorem; no equation converse or internal ZFC formalization is claimed.
-/

namespace DiophantineConsistency.WangTiles942Completeness

open SetTheory.BusyBeaver.ZFC WangTiles942Periodic WangTiles942CycleBand

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Allocate the least allowed left margin and all remaining width to
the right. Both independent trace-margin bounds are retained. -/
theorem width_split (T w : ℕ) (hw : 2*T+4 ≤ w) :
    (T+2)+(w-(T+2)) = w ∧ T+2 ≤ w-(T+2) := by omega

/-- The width and height range independently over all sufficiently large
natural values; no divisibility or coprimality condition is imposed. -/
theorem cofinal_marked_word (T w H : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hw : 2*T+4 ≤ w) (hTH : T+2 ≤ H) (hH : 3 ≤ H) :
    letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
    ∃ a : ZMod (w*H) → Fin 942, MarkedWord (w*H) (w : ℤ) a := by
  letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
  obtain ⟨hwidth,hright⟩ := width_split T w hw
  generalize w-(T+2) = R at hwidth hright
  subst w
  obtain ⟨a,hm,_⟩ := marked_word_of_halt T (T+2) R H
    hh (Nat.le_refl _) hright hTH hH
  exact ⟨a,hm⟩

/-- An actual finite marked word, with its positive modulus carried
explicitly. The stride is arbitrary and Start is not assumed unique. -/
def ExistsMarked : Prop :=
  ∃ (N : ℕ) (hN : 0 < N),
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    ∃ (s : ℤ) (a : ZMod N → Fin 942), MarkedWord N s a

theorem existsMarked_of_blank_halts
    (hh : KDenseBridge.BlankHalts DecimalMachine215.machine) : ExistsMarked := by
  obtain ⟨T,hT⟩ := hh
  have hw : 0 < 2*T+4 := by omega
  have hH : 0 < T+3 := by omega
  letI : NeZero ((2*T+4)*(T+3)) := ⟨Nat.ne_of_gt (Nat.mul_pos hw hH)⟩
  obtain ⟨a,hm⟩ := cofinal_marked_word T (2*T+4) (T+3) hT
    (Nat.le_refl _) (by omega) (by omega)
  exact ⟨(2*T+4)*(T+3),Nat.mul_pos hw hH,(2*T+4 : ℕ),a,hm⟩

theorem blank_halts_of_existsMarked (h : ExistsMarked) :
    KDenseBridge.BlankHalts DecimalMachine215.machine := by
  obtain ⟨N,hN,h⟩ := h
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨s,a,ha⟩ := h
  exact WangTiles942Soundness.marked_blank_halts ha

/-- Both directions use the same literal decimal machine and the same
actual 942-tile indexed language, with no calibration premise. -/
theorem existsMarked_iff_blank_halts :
    ExistsMarked ↔ KDenseBridge.BlankHalts DecimalMachine215.machine :=
  ⟨blank_halts_of_existsMarked,existsMarked_of_blank_halts⟩

/-- External Lean consistency calibration of the actual marked language.
This is not an assertion of consistency and not a Diophantine converse. -/
theorem no_marked_word_iff_conZFC : (¬ ExistsMarked) ↔ ConZFC :=
  (not_congr existsMarked_iff_blank_halts).trans DecimalMachineZFC.blank_nonhalting_iff_conZFC

theorem conZFC_iff_no_marked_word : ConZFC ↔ ¬ ExistsMarked :=
  no_marked_word_iff_conZFC.symm

end DiophantineConsistency.WangTiles942Completeness
