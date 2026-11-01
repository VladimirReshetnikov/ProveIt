import DiophantineConsistency.PRAUniversalAxiomSyntax
import Mathlib.Data.Nat.Pairing
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandSchedule
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage

/-- A strict upper bound on all free variable indices of a term. -/
def bound (t : SyntacticTerm language) : ℕ := t.freeVariables.sup id + 1

theorem lt_bound (t : SyntacticTerm language) {i : ℕ} (h : i ∈ t.freeVariables) : i < bound t := by
  have hi : i ≤ t.freeVariables.sup id := Finset.le_sup (f := id) h
  dsimp [bound]
  omega

/-- Every term receives a unique stage later than all its free variables. -/
def stage (t : SyntacticTerm language) : ℕ := Nat.pair (Encodable.encode t) (bound t) + 1

theorem stage_after (t : SyntacticTerm language) {i : ℕ} (h : i ∈ t.freeVariables) : i < stage t := by
  have ht := lt_bound t h
  have hb := Nat.right_le_pair (Encodable.encode t) (bound t)
  dsimp [stage]
  omega

theorem stage_injective : Function.Injective stage := by
  intro t u h
  have hp : Nat.pair (Encodable.encode t) (bound t) = Nat.pair (Encodable.encode u) (bound u) := by
    dsimp [stage] at h
    omega
  have he : Encodable.encode t = Encodable.encode u := by
    have hp' := congrArg (fun x => (Nat.unpair x).1) hp
    simpa using hp'
  exact Encodable.encode_injective he

def zeroTerm : SyntacticTerm language := .func (.zero 0) Fin.elim0

/-- Decode a term at its assigned stage, using a closed zero term elsewhere. -/
def candidate : ℕ → SyntacticTerm language
  | 0 => zeroTerm
  | j+1 =>
      match Encodable.decode (Nat.unpair j).1 with
      | none => zeroTerm
      | some t => if bound t = (Nat.unpair j).2 then t else zeroTerm

theorem candidate_stage (t : SyntacticTerm language) : candidate (stage t) = t := by
  simp [candidate, stage, Encodable.encodek]

theorem candidate_before (j : ℕ) {i : ℕ} (hi : i ∈ (candidate j).freeVariables) : i < j := by
  cases j with
  | zero => simp [candidate, zeroTerm] at hi
  | succ j =>
      simp only [candidate] at hi
      split at hi
      next h => simp [zeroTerm] at hi
      next t h =>
        split at hi
        next hb =>
          have ht := lt_bound t hi
          have hp := Nat.unpair_right_le j
          omega
        next hb => simp [zeroTerm] at hi
end DiophantineConsistency.HerbrandSchedule
