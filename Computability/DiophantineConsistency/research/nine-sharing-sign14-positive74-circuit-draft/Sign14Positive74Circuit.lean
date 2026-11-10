import DiophantineConsistency.Sign14Positive74ObjectEndpoint

/-! SOURCE ONLY: explicit finite arithmetic circuit, counts and liveness certificate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74Circuit
inductive Arg where
  | var (i : Fin 14) | port (i : Fin 4) | lit (z : ℤ) | reg (i : ℕ)
  deriving DecidableEq, Repr
inductive Op where | add | sub | mul
  deriving DecidableEq, Repr
structure Gate where
  op : Op
  left : Arg
  right : Arg
  deriving DecidableEq, Repr

def gates : List Gate := [
  ⟨.mul, .port 0, .var 0⟩,
  ⟨.add, .reg 0, .lit 1⟩,
  ⟨.mul, .var 8, .reg 1⟩,
  ⟨.mul, .reg 1, .reg 1⟩,
  ⟨.mul, .reg 3, .reg 1⟩,
  ⟨.mul, .var 7, .reg 4⟩,
  ⟨.mul, .reg 2, .reg 5⟩,
  ⟨.add, .reg 6, .reg 5⟩,
  ⟨.add, .var 10, .var 11⟩,
  ⟨.mul, .reg 8, .reg 5⟩,
  ⟨.add, .reg 9, .var 10⟩,
  ⟨.mul, .reg 7, .reg 10⟩,
  ⟨.add, .reg 2, .reg 11⟩,
  ⟨.mul, .lit 4, .reg 7⟩,
  ⟨.add, .reg 13, .lit 3⟩,
  ⟨.mul, .var 13, .reg 14⟩,
  ⟨.add, .reg 12, .reg 15⟩,
  ⟨.mul, .reg 16, .reg 16⟩,
  ⟨.sub, .reg 17, .lit 1⟩,
  ⟨.mul, .reg 7, .reg 7⟩,
  ⟨.add, .reg 19, .reg 14⟩,
  ⟨.mul, .reg 10, .reg 10⟩,
  ⟨.mul, .reg 20, .reg 21⟩,
  ⟨.sub, .reg 18, .reg 22⟩,
  ⟨.mul, .reg 6, .var 9⟩,
  ⟨.add, .reg 24, .reg 8⟩,
  ⟨.sub, .reg 1, .var 1⟩,
  ⟨.mul, .reg 0, .reg 26⟩,
  ⟨.add, .reg 27, .var 2⟩,
  ⟨.mul, .reg 28, .reg 3⟩,
  ⟨.mul, .reg 1, .port 3⟩,
  ⟨.add, .port 2, .reg 30⟩,
  ⟨.mul, .reg 31, .var 0⟩,
  ⟨.add, .reg 29, .reg 32⟩,
  ⟨.sub, .reg 33, .reg 28⟩,
  ⟨.sub, .reg 25, .reg 34⟩,
  ⟨.mul, .reg 35, .reg 35⟩,
  ⟨.mul, .reg 6, .reg 9⟩,
  ⟨.add, .reg 37, .reg 8⟩,
  ⟨.mul, .reg 37, .reg 38⟩,
  ⟨.sub, .reg 36, .reg 39⟩,
  ⟨.sub, .reg 40, .lit 1⟩,
  ⟨.add, .port 1, .var 8⟩,
  ⟨.sub, .reg 26, .var 2⟩,
  ⟨.mul, .reg 42, .reg 43⟩,
  ⟨.sub, .reg 44, .var 1⟩,
  ⟨.sub, .var 3, .lit 1⟩,
  ⟨.mul, .reg 46, .reg 0⟩,
  ⟨.sub, .reg 45, .reg 47⟩,
  ⟨.mul, .var 12, .var 12⟩,
  ⟨.mul, .var 5, .reg 18⟩,
  ⟨.mul, .reg 50, .reg 50⟩,
  ⟨.mul, .var 4, .var 4⟩,
  ⟨.mul, .reg 10, .var 6⟩,
  ⟨.sub, .reg 53, .reg 34⟩,
  ⟨.mul, .reg 52, .reg 54⟩,
  ⟨.sub, .reg 55, .reg 10⟩,
  ⟨.mul, .reg 56, .reg 56⟩,
  ⟨.sub, .reg 49, .reg 57⟩,
  ⟨.mul, .reg 51, .reg 58⟩,
  ⟨.sub, .reg 49, .reg 59⟩,
  ⟨.sub, .reg 60, .lit 1⟩,
  ⟨.mul, .reg 20, .reg 52⟩,
  ⟨.sub, .reg 62, .reg 51⟩,
  ⟨.sub, .reg 63, .reg 20⟩,
  ⟨.mul, .reg 23, .reg 23⟩,
  ⟨.mul, .reg 41, .reg 41⟩,
  ⟨.mul, .reg 48, .reg 48⟩,
  ⟨.mul, .reg 61, .reg 61⟩,
  ⟨.mul, .reg 64, .reg 64⟩,
  ⟨.add, .reg 65, .reg 66⟩,
  ⟨.add, .reg 70, .reg 67⟩,
  ⟨.add, .reg 71, .reg 68⟩,
  ⟨.add, .reg 72, .reg 69⟩]
def parents : List ℕ := [1, 2, 6, 4, 5, 6, 7, 11, 9, 10, 11, 12, 16, 14, 15, 16, 17, 18, 23, 20, 22, 22, 23, 65, 25, 35, 27, 28, 29, 33, 31, 32, 33, 34, 35, 36, 40, 38, 39, 40, 41, 66, 44, 44, 45, 48, 47, 48, 67, 58, 51, 59, 55, 54, 55, 56, 57, 58, 59, 60, 61, 68, 63, 64, 69, 70, 70, 71, 72, 73, 71, 72, 73, 73]
def fallback : Gate := ⟨.add, .lit 0, .lit 0⟩
def gateAt (i : ℕ) : Gate := gates.getD i fallback
def parentAt (i : ℕ) : ℕ := parents.getD i 73

def earlier (i : ℕ) : Arg → Bool
  | .reg j => decide (j < i)
  | _ => true

theorem gateCount : gates.length = 74 := by decide

theorem topological : ∀ i : Fin 74,
    earlier i.val (gateAt i.val).left = true ∧ earlier i.val (gateAt i.val).right = true := by decide

theorem operationCounts :
    (gates.filter fun g => g.op == .add).length = 18 ∧
    (gates.filter fun g => g.op == .sub).length = 18 ∧
    (gates.filter fun g => g.op == .mul).length = 38 := by decide

theorem parentCertificate : ∀ i : Fin 73,
    i.val < parentAt i.val ∧ parentAt i.val < 74 ∧
      ((gateAt (parentAt i.val)).left = .reg i.val ∨
       (gateAt (parentAt i.val)).right = .reg i.val) := by decide

inductive Live : ℕ → Prop where
  | output : Live 73
  | left (i j : ℕ) : Live j → (gateAt j).left = .reg i → Live i
  | right (i j : ℕ) : Live j → (gateAt j).right = .reg i → Live i

theorem everyGateLive (i : Fin 74) : Live i.val := by
  have aux : ∀ d : ℕ, ∀ j : ℕ, j < 74 → 73 - j = d → Live j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj hd
      by_cases he : j = 73
      · subst j; exact Live.output
      · have hj' : j < 73 := by omega
        have hp := parentCertificate ⟨j, hj'⟩
        have hl : Live (parentAt j) := ih (73 - parentAt j) (by omega) (parentAt j) hp.2.1 rfl
        rcases hp.2.2 with hleft | hright
        · exact Live.left j (parentAt j) hl hleft
        · exact Live.right j (parentAt j) hl hright
  exact aux (73 - i.val) i.val i.isLt rfl
end DiophantineConsistency.Sign14Positive74Circuit
#print axioms DiophantineConsistency.Sign14Positive74Circuit.gateCount
#print axioms DiophantineConsistency.Sign14Positive74Circuit.topological
#print axioms DiophantineConsistency.Sign14Positive74Circuit.operationCounts
#print axioms DiophantineConsistency.Sign14Positive74Circuit.everyGateLive
