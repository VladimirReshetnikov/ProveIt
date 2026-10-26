import DiophantineConsistency.EnumeratorSemantics
import BusyBeaver.ZFC.EnumPerm
import Mathlib.Computability.Primrec.Basic

/-! # Definitions and semantic halting bridge for the literal enumerator

This lower layer contains the original definitions and semantic proofs.
Computability is recovered from the already supplied scalar program in
Computability.lean; no primitive-recursiveness proof is used here.
-/

namespace PriorSemanticLayer
open SetTheory SetTheory.BusyBeaver.ZFC
open EnumPerm Code254 KCode222


private def stateEquiv : St ≃ ℕ × ℕ × ℕ × ℕ × ℕ × ℕ where
  toFun s := (s.pl, s.np, s.tw, s.ws, s.d, s.h)
  invFun s := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : Primcodable St := Primcodable.ofEquiv _ stateEquiv
private instance : DecidableEq St := Encodable.decidableEqOfEncodable _

/-- Run the proof enumerator for a bounded number of steps; `none` stays `none`. -/
def boundedRun (n : ℕ) (s : St) : Option St :=
  (fun o : Option St => o.bind enumStep)^[n] (some s)

private theorem boundedRun_eq (n : ℕ) (s : St) : boundedRun n s = run n s := by
  have hnone : ∀ n, (fun o : Option St => o.bind enumStep)^[n] none = none := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [boundedRun, Function.iterate_succ_apply, Option.bind_some]
      cases he : enumStep s with
      | none =>
          simpa only [run, he] using hnone n
      | some s' => simpa only [boundedRun, run, he] using ih s'

private theorem run_succ_right (n : ℕ) (s : St) :
    run (n + 1) s = (run n s).bind enumStep := by
  rw [← boundedRun_eq, boundedRun, Function.iterate_succ_apply']
  change (boundedRun n s).bind enumStep = _
  rw [boundedRun_eq]

/-- The literal initial state shared with the 215-state proof enumerator. -/
def initialState : St := ⟨0, 4, 0, 0, 0, 0⟩

private theorem exists_none_iff (s : St) : (∃ n, boundedRun n s = none) ↔ HaltsFrom s := by
  simp only [boundedRun_eq]
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing s with
    | zero => cases hn
    | succ n ih =>
        cases he : enumStep s with
        | none => exact ⟨0, s, rfl, he⟩
        | some s' =>
            obtain ⟨k, u, hk, hu⟩ := ih s' (by simpa only [run, he] using hn)
            exact ⟨k + 1, u, by simp only [run, he, hk], hu⟩
  · rintro ⟨n, s', hn, hs'⟩
    exact ⟨n + 1, by rw [run_succ_right, hn, Option.bind_some, hs']⟩

/-- The input is unused: every input is accepted exactly when the falsity code is derivable. -/
def refutationInputs : Set ℕ := fun _ => C222 F

/-- A scalar, executable bounded test for the actual proof enumerator.
Its result is `1` exactly when a refutation has already been found. -/
def haltingTest (t : ℕ) : ℕ :=
  Encodable.encode (decide (boundedRun t initialState = none))

theorem haltingTest_eq_one_iff (t : ℕ) :
    haltingTest t = 1 ↔ boundedRun t initialState = none := by
  by_cases h : boundedRun t initialState = none <;> simp [haltingTest, h]

theorem exists_haltingTest_eq_one_iff : (∃ t, haltingTest t = 1) ↔ C222 F := by
  simp only [haltingTest_eq_one_iff]
  exact (exists_none_iff initialState).trans
    (EnumPerm.halts_iff rfl ⟨C222.truth, C222.truth, good_zero⟩)

end PriorSemanticLayer

namespace TagOnlyDecision
open PriorSemanticLayer

/-- This decision inspects the Option constructor; it has no state equality or encoding argument. -/
def tagOnlyTest (t : ℕ) : ℕ :=
  Encodable.encode (@decide (boundedRun t initialState = none)
    (Option.decidableEqNone (boundedRun t initialState)))

/-- Definitional equality, not merely equality of acceptance behavior. -/
theorem old_test_eq_tagOnly : haltingTest = tagOnlyTest := rfl

theorem no_payload_instance_needed {α : Type} (o : Option α) :
    @decide (o = none) (Option.decidableEqNone o) = o.isNone := by
  cases o <;> rfl

/-- Compare the original incoming source, elaborated with its old instances,
with the separately compiled cleaned actual module. -/
theorem baseline_eq_cleaned : PriorSemanticLayer.haltingTest =
    DiophantineConsistency.haltingTest := rfl

#print axioms baseline_eq_cleaned
#print axioms old_test_eq_tagOnly
#print axioms no_payload_instance_needed
end TagOnlyDecision
