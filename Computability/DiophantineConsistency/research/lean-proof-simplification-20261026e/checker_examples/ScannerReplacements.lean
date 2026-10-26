import IterationMathlib
import DiophantineConsistency.AnnotatedBoundScan
import DiophantineConsistency.AnnotatedLineScan
import DiophantineConsistency.AnnotatedAxiomContext
import DiophantineConsistency.AnnotatedContextLookup

/-!
Proof-only replacement bodies for actual theorem statements at ProveIt commit
60e9c5d620c6c387d932876cfa2d9376f64ea56c.

The examples are deliberately not installed into the upstream tree. They do
not define replacement executable programs. Full project elaboration is
required before treating them as checked patches.
-/
open CheckerRefactor.MathlibAdapter

namespace DiophantineConsistency.AnnotatedRenameScan

-- Replaces the body of scan_zero (lines 34--37).
example (fuel mode k : Nat) : scan fuel mode k 0 = 0 :=
  rec_fixed (step mode k) fuel 0 (step_zero mode k)

-- Replaces the body of scan_succ (lines 39--46).
example (fuel mode k state : Nat) :
    scan (fuel + 1) mode k state = scan fuel mode k (step mode k state) :=
  rec_succ_right (step mode k) fuel state

-- Replaces the body of scan_done (lines 48--55).
example (fuel mode k history : Nat) :
    scan fuel mode k (Nat.pair 0 history) = Nat.pair 0 history :=
  rec_fixed (step mode k) fuel _ (by simp [step])

end DiophantineConsistency.AnnotatedRenameScan

namespace DiophantineConsistency.AnnotatedBoundScan
example (fuel : Nat) : scan fuel 0 = 0 := rec_fixed step fuel 0 step_zero
example (fuel state : Nat) : scan (fuel + 1) state = scan fuel (step state) :=
  rec_succ_right step fuel state
example (fuel history : Nat) : scan fuel (Nat.pair 0 history) = Nat.pair 0 history :=
  rec_fixed step fuel _ (by simp [step])
end DiophantineConsistency.AnnotatedBoundScan

namespace DiophantineConsistency.AnnotatedLineScan
example (fuel : Nat) : scan fuel 0 = 0 := rec_fixed step fuel 0 step_zero
example (fuel state : Nat) : scan (fuel + 1) state = scan fuel (step state) :=
  rec_succ_right step fuel state
example (fuel history : Nat) : scan fuel (Nat.pair 0 history) = Nat.pair 0 history :=
  rec_fixed step fuel _ (by simp [step])
end DiophantineConsistency.AnnotatedLineScan

namespace DiophantineConsistency.AnnotatedAxiomContext
example (fuel : Nat) : scan fuel 0 = 0 := rec_fixed step fuel 0 (by simp [step])
example (fuel state : Nat) : scan (fuel + 1) state = scan fuel (step state) :=
  rec_succ_right step fuel state
example (fuel history : Nat) : scan fuel (Nat.pair 0 history) = Nat.pair 0 history :=
  rec_fixed step fuel _ (by simp [step])
end DiophantineConsistency.AnnotatedAxiomContext

namespace DiophantineConsistency.AnnotatedContext
example (fuel : Nat) : scan fuel 0 = 0 := rec_fixed step fuel 0 step_zero
example (fuel state : Nat) : scan (fuel + 1) state = scan fuel (step state) :=
  rec_succ_right step fuel state
example (fuel output evidence : Nat) :
    scan fuel (inputCode 1 output evidence) = inputCode 1 output evidence :=
  rec_fixed step fuel _ (by simp only [step, inputCode, Nat.unpair_pair, if_true])
end DiophantineConsistency.AnnotatedContext

namespace DiophantineConsistency.AnnotatedContextLookup
example (code index : Nat) : drop code (index + 1) = drop (tail code) index :=
  rec_succ_right tail index code

-- This removes the nested induction in lookup_contextCode's nil branch.
example (index : Nat) : drop (AnnotatedContext.contextCode []) index =
    AnnotatedContext.contextCode [] :=
  rec_fixed tail index _ tail_nil
end DiophantineConsistency.AnnotatedContextLookup
