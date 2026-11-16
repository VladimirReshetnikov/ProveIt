import PackedClock
import ConfigurationStandard

set_option autoImplicit false
namespace PackedStandard
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAHistoryPairCode PRASelectCode
open ConfigurationStep PackedClock List.Vector

theorem evalRootStep (i s : Nat) : eval rootStep (i ::ᵥ s ::ᵥ nil) =
    if (s+1)*(s+1) ≤ i+1 then s+1 else s := by
  change eval selectCode
    (eval ltBitCode (eval mulCode ((s+1) ::ᵥ (s+1) ::ᵥ nil) ::ᵥ (i+2) ::ᵥ nil) ::ᵥ
      (s+1) ::ᵥ s ::ᵥ nil) = _
  rw [eval_mulCode, eval_ltBitCode]
  by_cases h : (s+1)*(s+1) ≤ i+1
  · have h' : (s+1)*(s+1) < i+2 := by omega
    simp only [h, h', ite_true]
    rfl
  · have h' : ¬(s+1)*(s+1) < i+2 := by omega
    simp only [h, h', ite_false]
    rfl

theorem evalRoot (n : Nat) : eval rootCode (n ::ᵥ nil) = Nat.sqrt n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change eval rootStep (n ::ᵥ eval rootCode (n ::ᵥ nil) ::ᵥ nil) = _
    rw [ih, evalRootStep]
    by_cases h : (Nat.sqrt n+1)*(Nat.sqrt n+1) ≤ n+1
    · rw [if_pos h]
      have hl : Nat.sqrt n+1 ≤ Nat.sqrt (n+1) := Nat.le_sqrt.mpr h
      have hu : Nat.sqrt (n+1) ≤ Nat.sqrt n+1 := by
        simpa only [Nat.succ_eq_add_one] using Nat.sqrt_succ_le_succ_sqrt n
      omega
    · rw [if_neg h]
      have hl := Nat.sqrt_le_sqrt (show n ≤ n+1 by omega)
      have hu : Nat.sqrt (n+1) < Nat.sqrt n+1 := Nat.sqrt_lt.mpr (by omega)
      omega
theorem evalUnary {n : Nat} (f : Code 1) (a : Code n) (v : List.Vector Nat n) :
    eval (unary f a) v = eval f (eval a v ::ᵥ nil) := rfl

theorem evalBin {n : Nat} (f : Code 2) (a b : Code n) (v : List.Vector Nat n) :
    eval (bin f a b) v = eval f (eval a v ::ᵥ eval b v ::ᵥ nil) := rfl

theorem evalSelect {n : Nat} (t a b : Code n) (v : List.Vector Nat n) :
    eval (selectAmong t a b) v = if eval t v = 0 then eval b v else eval a v := by
  change eval selectCode (eval t v ::ᵥ eval a v ::ᵥ eval b v ::ᵥ nil) = _
  cases eval t v <;> rfl

theorem evalLeft (n : Nat) : eval decodeLeft (n ::ᵥ nil) = n.unpair.1 := by
  simp only [decodeLeft, lowSide, remainder, squareRoot, evalSelect, evalBin,
    eval_subCode, eval_mulCode, eval_ltBitCode, evalRoot]
  change (if (if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then 1 else 0) = 0
      then Nat.sqrt n else n - Nat.sqrt n * Nat.sqrt n) = n.unpair.1
  simp only [Nat.unpair]
  split_ifs <;> simp_all

theorem evalRight (n : Nat) : eval decodeRight (n ::ᵥ nil) = n.unpair.2 := by
  simp only [decodeRight, lowSide, remainder, squareRoot, evalSelect, evalBin,
    eval_subCode, eval_mulCode, eval_ltBitCode, evalRoot]
  change (if (if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then 1 else 0) = 0
      then n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n else Nat.sqrt n) = n.unpair.2
  simp only [Nat.unpair]
  split_ifs <;> simp_all

theorem evalPair (a b : Nat) : eval pairCode (a ::ᵥ b ::ᵥ nil) = Nat.pair a b := by
  simp only [pairCode, evalSelect, evalBin, eval_addCode, eval_mulCode, eval_ltBitCode]
  change (if (if a < b then 1 else 0) = 0 then a*a+a+b else b*b+a) = Nat.pair a b
  simp only [Nat.pair]
  split_ifs <;> simp_all

theorem evalInject (f : Code 3) (n : Nat) :
    eval (inject3 f) (n ::ᵥ nil) =
      eval f (n.unpair.1 ::ᵥ n.unpair.2.unpair.1 ::ᵥ n.unpair.2.unpair.2 ::ᵥ nil) := by
  change eval f (eval packedQ (n ::ᵥ nil) ::ᵥ eval packedL (n ::ᵥ nil) ::ᵥ
    eval packedR (n ::ᵥ nil) ::ᵥ nil) = _
  simp only [packedQ, packedL, packedR, evalUnary, evalLeft, evalRight]

def pack (c : PA194Bounded.Conf) : Nat := Nat.pair c.1 (Nat.pair c.2.1 c.2.2)
def unpack (n : Nat) : PA194Bounded.Conf := (n.unpair.1,n.unpair.2.unpair.1,n.unpair.2.unpair.2)

theorem unpackPack (c : PA194Bounded.Conf) : unpack (pack c) = c := by
  rcases c with ⟨q,l,r⟩
  simp [pack, unpack, Nat.unpair_pair]

theorem evalPackedStep (n : Nat) : eval encodedStep (n ::ᵥ nil) =
    pack (PA194Bounded.next (unpack n)) := by
  simp only [encodedStep, evalBin, evalPair, evalInject, pack, unpack]
  rw [← ConfigurationStandard.evalStepBounded]

theorem evalClock (n : Nat) : eval clock (n ::ᵥ nil) = pack (PA194Bounded.run n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change eval encodedStep (eval clock (n ::ᵥ nil) ::ᵥ nil) = _
    rw [ih, evalPackedStep, unpackPack]
    rfl

theorem evalIsZero (n : Nat) : eval PRAIsZero.isZeroCode (n ::ᵥ nil) = if n = 0 then 1 else 0 := by
  cases n <;> rfl

theorem evalHaltIndicator (n : Nat) : eval haltIndicator (n ::ᵥ nil) = PA194Bounded.bounded n := by
  simp only [haltIndicator, clockState, const194, evalUnary, evalBin, evalClock,
    evalLeft, TableDispatch.evalConstant, eval_ltBitCode, evalIsZero, PA194Bounded.bounded]
  simp only [pack, Nat.unpair_pair]
  by_cases h : (PA194Bounded.run n).1 < 194 <;> simp [h, Nat.not_lt.mp]

theorem explicitClock_iff_literal_halts :
    (∃ n : Nat, eval haltIndicator (n ::ᵥ nil) = 1) ↔
      M6.Zip.Halts PA194.Literal.machine PA194Bounded.blankZip := by
  simpa only [evalHaltIndicator] using PA194Bounded.exists_bounded_iff_literal_halts
#print axioms explicitClock_iff_literal_halts

#print axioms evalClock
#print axioms evalHaltIndicator

#print axioms evalPair
#print axioms evalInject
#print axioms unpackPack
#print axioms evalPackedStep

#print axioms evalLeft
#print axioms evalRight

#print axioms evalRoot
end PackedStandard
