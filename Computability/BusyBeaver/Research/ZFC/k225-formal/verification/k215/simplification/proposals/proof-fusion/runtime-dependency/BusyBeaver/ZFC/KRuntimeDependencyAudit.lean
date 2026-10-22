import BusyBeaver.ZFC.KRuntimeDependency

/-! Boundary cases for the exact-footprint transport theorem.
These examples use the production definitions, not a second interpreter. -/
namespace SetTheory.BusyBeaver.ZFC.KRuntimeDependencyAudit
open KZip KRuntimeCore KRuntimeDependency

def noRows : TMN := fun _ _ => none
def oneRow : TMN := fun q b =>
  if q = 99 ∧ b = false then some (false, false, 12) else none

def missingBit : SConf := (99, false, [], [.bit false])

theorem missing_lookup_recorded : stepReads none missingBit = [(99, false)] := rfl
theorem missing_lookup_stops : sstep noRows none missingBit = none := rfl
theorem missing_is_a_value : ¬ Agrees noRows oneRow (stepReads none missingBit) := by
  intro h
  have he := h (99, false) (by decide)
  cases he

def oracleEntry : SConf := (64, false, [], [.box (.mark 0)])
def fallbackEntry : SConf := (99, false, [], [.box (.mark 0)])

theorem oracle_success_no_reads : stepReads none oracleEntry = [] := by decide
theorem oracle_success_same_result (M N : TMN) :
    sstep M none oracleEntry = sstep N none oracleEntry :=
  sstep_local none oracleEntry (by
    intro k hk
    rw [oracle_success_no_reads] at hk
    contradiction)

theorem failed_oracle_reads_fallback : stepReads none fallbackEntry = [(99, false)] := by decide
theorem failed_oracle_missing_stops : sstep noRows none fallbackEntry = none := by decide
theorem failed_oracle_row_changes_result :
    sstep oneRow none fallbackEntry =
      some ((12, true, [], [.box (.mark 0)]), true) := by decide

def homeEntry : SConf := (2, true, [.bit true], [])
def homeExit : SConf := (84, false, [.bit true], [])

theorem home_has_no_direct_reads : reads true none homeEntry = [] := by decide
theorem home_preserves_positive_flag :
    next true noRows none homeEntry = some (homeExit, true) := by decide
theorem mode_matters_even_without_reads :
    next true noRows none homeEntry ≠ next false noRows none homeEntry := by decide
theorem no_rows_does_not_enable_home : KHomeReady.ready noRows = false := by decide

/-- The actual wrapper client keeps readiness agreement explicitly. -/
theorem wrapper_client (M N : TMN)
    (hr : KHomeReady.ready M = KHomeReady.ready N)
    (br : Branch) (tgt : SConf → Bool) (f : Nat) (s : SConf)
    (ha : Agrees M N (traceReads (KHomeReady.ready M) M br tgt f s false)) :
    KHomeReady.exec M br tgt f s false = KHomeReady.exec N br tgt f s false :=
  home_exec_transport hr br tgt f s false ha

#print axioms missing_is_a_value
#print axioms oracle_success_same_result
#print axioms failed_oracle_row_changes_result
#print axioms home_preserves_positive_flag
#print axioms mode_matters_even_without_reads
#print axioms wrapper_client

end SetTheory.BusyBeaver.ZFC.KRuntimeDependencyAudit
