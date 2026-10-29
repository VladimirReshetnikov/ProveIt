import DiophantineConsistency.HAProofs
import DiophantineConsistency.NaturalExpressionSemiring

/-! # Literal polynomial sentences in the arithmetic language

The compiler uses only `0,S,+,*`. Fixed integers are split into natural
parts before compilation. Binary numerals contain one copy of their
recursive subterm, so enormous constants do not require unary expansion.
The semantic theorem works in every commutative semiring; it is not an
HA proof of any consistency equivalence.
-/

set_option Elab.async false
namespace DiophantineConsistency.ArithmeticExpression
open SetTheory.PA

def binaryNumeral (n : ℕ) : Term :=
  if h : n = 0 then .zero else
    let twice := Term.mul (.succ (.succ .zero)) (binaryNumeral (n / 2))
    if n % 2 = 0 then twice else .succ twice
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- This is a raw arithmetic structure, with no induction assumption. -/
def semiringStructure (R : Type*) [CommSemiring R] : PreModel R where
  zero := 0
  succ := fun x => x + 1
  add := (· + ·)
  mul := (· * ·)

theorem eval_binaryNumeral {R : Type*} [CommSemiring R] (ee : ℕ → R) (n : ℕ) :
    Term.eval (semiringStructure R) ee (binaryNumeral n) = (n : R) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [binaryNumeral]
    split_ifs with hz he
    · subst n
      simp only [Term.eval, semiringStructure, Nat.cast_zero]
    · have hd := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))
      change ((0 : R) + 1 + 1) * Term.eval (semiringStructure R) ee (binaryNumeral (n / 2)) = _
      simp only [zero_add, one_add_one_eq_two, hd]
      have hn : 2 * (n / 2) = n := by have := Nat.mod_add_div n 2; omega
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun k : ℕ => (k : R)) hn
    · have hd := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))
      change ((0 : R) + 1 + 1) * Term.eval (semiringStructure R) ee (binaryNumeral (n / 2)) + 1 = _
      simp only [zero_add, one_add_one_eq_two, hd]
      have hn : 2 * (n / 2) + 1 = n := by
        have := Nat.mod_add_div n 2
        have := Nat.mod_lt n (by decide : 0 < 2)
        omega
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
        congrArg (fun k : ℕ => (k : R)) hn

theorem binaryNumeral_closed (n k : ℕ) : ¬ Term.Free k (binaryNumeral n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [binaryNumeral]
    split_ifs with hz he
    · exact id
    · simpa only [Term.Free, false_or] using
        (ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide)))
    · simpa only [Term.Free, false_or] using
        (ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide)))

def term {σ : Type*} (coordinates : σ → ℕ) : NatExpr σ → Term
  | .constant n => binaryNumeral n
  | .var i => .var (coordinates i)
  | .add p q => .add (term coordinates p) (term coordinates q)
  | .mul p q => .mul (term coordinates p) (term coordinates q)

theorem eval_term {σ R : Type*} [CommSemiring R]
    (e : NatExpr σ) (coordinates : σ → ℕ) (ee : ℕ → R) :
    Term.eval (semiringStructure R) ee (term coordinates e) =
      e.evalSemiring (fun i => ee (coordinates i)) := by
  induction e with
  | constant n => exact eval_binaryNumeral ee n
  | var i => rfl
  | add p q hp hq => exact congrArg₂ (· + ·) hp hq
  | mul p q hp hq => exact congrArg₂ (· * ·) hp hq

theorem free_term {σ : Type*} (e : NatExpr σ) (coordinates : σ → ℕ) (k : ℕ)
    (h : Term.Free k (term coordinates e)) : ∃ i, k = coordinates i := by
  induction e with
  | constant n => exact False.elim (binaryNumeral_closed n k h)
  | var i => exact ⟨i, h⟩
  | add p q hp hq => exact h.elim hp hq
  | mul p q hp hq => exact h.elim hp hq

def equation {σ : Type*} (e : Expr σ) (coordinates : σ → ℕ) : Formula :=
  .eq (term coordinates e.splitNatural.1) (term coordinates e.splitNatural.2)

theorem sat_equation {σ R : Type*} [CommSemiring R]
    (e : Expr σ) (coordinates : σ → ℕ) (ee : ℕ → R) :
    Formula.Sat (semiringStructure R) ee (equation e coordinates) ↔
      e.splitNatural.1.evalSemiring (fun i => ee (coordinates i)) =
        e.splitNatural.2.evalSemiring (fun i => ee (coordinates i)) := by
  simp only [equation, Formula.Sat, eval_term]

/-- Exactly n universal quantifiers, with variable i bound at slot i. -/
def noZeroSentence {n : ℕ} (e : Expr (Fin n)) : Formula :=
  Formula.closeN n (.imp (equation e Fin.val) .bot)

theorem sentence_noZeroSentence {n : ℕ} (e : Expr (Fin n)) :
    Formula.Sentence (noZeroSentence e) := by
  intro k hk
  have hf := Formula.Free_closeN n (.imp (equation e Fin.val) .bot) k hk
  change (Term.Free (n+k) (term Fin.val e.splitNatural.1) ∨
    Term.Free (n+k) (term Fin.val e.splitNatural.2)) ∨ False at hf
  rcases hf with (hp | hq) | hb
  · obtain ⟨i, hi⟩ := free_term _ _ _ hp
    have := i.isLt
    omega
  · obtain ⟨i, hi⟩ := free_term _ _ _ hq
    have := i.isLt
    omega
  · exact hb

/-- All tuples in the structure are quantified, not just numeral tuples. -/
theorem sat_noZeroSentence {n : ℕ} {R : Type*} [CommSemiring R]
    (e : Expr (Fin n)) :
    (∀ ee : ℕ → R, Formula.Sat (semiringStructure R) ee (noZeroSentence e)) ↔
      ∀ v : Fin n → R, e.splitNatural.1.evalSemiring v ≠
        e.splitNatural.2.evalSemiring v := by
  rw [noZeroSentence, Formula.closeN_valid]
  simp only [Formula.Sat, sat_equation]
  constructor
  · intro h v
    let ee : ℕ → R := fun k => if hk : k < n then v ⟨k, hk⟩ else 0
    have hev : (fun i : Fin n => ee i.val) = v := by
      funext i
      simp only [ee, dif_pos i.isLt]
    simpa only [hev] using h ee
  · intro h ee
    exact h (fun i => ee i.val)

theorem sat_noZeroSentence_nat {n : ℕ} (e : Expr (Fin n)) :
    (∀ ee : ℕ → ℕ, Formula.Sat (semiringStructure ℕ) ee (noZeroSentence e)) ↔
      ¬ ∃ v : Fin n → ℕ, e.eval (fun i => (v i : ℤ)) = 0 := by
  rw [sat_noZeroSentence]
  simp only [NatExpr.evalSemiring_nat, Expr.eval_eq_zero_iff_splitNatural,
    not_exists]

end DiophantineConsistency.ArithmeticExpression
