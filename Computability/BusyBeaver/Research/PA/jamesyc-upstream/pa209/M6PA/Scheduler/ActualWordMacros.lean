module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualWordExpression
public import M6PA.Scheduler.ActualWordCoding
public import M6PA.Scheduler.ActualAtomCompiler
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualWordMacros
open ActualWordExpression
open M6.Source M6.Source.Enumeration M6.Source.CommandAtomEncoding
open M6.Source.ActualCommandMacros

/-- Scalar pairing uses the explicit source Cantor graph, not HFS pairing. -/
def pair (a b : Scalar) : Scalar := .head (.pair .a .b) a b (.num 0) (.num 0)
def mpAtom (b : Scalar) : Scalar := pair (.num 1) (pair b (.num 0))
def axAtom (c a b : Scalar) : Scalar := pair (.add c (.num 2)) (pair b (pair a (.num 0)))
def literal : List Nat → Expr
  | [] => .nil
  | a::as => .cons (.num a) (literal as)
def singleton (a : Scalar) : Expr := .cons a .nil

def j (u : Scalar) : Expr := .ifEq u (.num 0) .nil (singleton (mpAtom u))
def head (k : Nat) (a b c : Scalar) : Expr :=
  .append (.append (literal (atoms DISCARD))
    (.cons (axAtom c a b) (literal (atoms (List.replicate (k+1) .shift)))))
    (literal (atoms (popHeads (9-k))))
def head8 (a b c u : Scalar) : Expr :=
  .append (.append (.append (literal (atoms DISCARD)) (j u))
    (.cons (axAtom c (.sub a u) b) (literal (atoms (List.replicate 9 .shift))))) (literal (atoms H))
def gate (a b c : Scalar) : Expr :=
  .append (.append (literal (atoms DISCARD)) (singleton (axAtom c a b))) (literal (atoms (popHeads 10)))
def gen (i : Scalar) : Expr :=
  .append (.append (.append (literal (atoms PUSH)) (j i)) (literal (atoms [.shift])))
    (.cons (axAtom i (.num 0) (.num 0)) (literal (atoms (List.replicate 10 .shift))))
def mp (b : Scalar) : Expr :=
  .append (.append (.cons (.num (atom .shift)) (.cons (.num (atom .shift)) (singleton (mpAtom b))))
    (.cons (axAtom b (.num 0) (.num 0)) (literal (atoms (List.replicate 10 .shift)))))
    (literal (atoms [.shift]))

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualWordCoding

theorem literal_standard (xs : List Nat) (p t d : Nat) : eval (literal xs) p t d=encode xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [literal,eval,ActualCheckExpression.eval,ih,numeral_eq_natCast]

theorem pair_standard (a b : Scalar) (p t d : Nat) :
    ActualCheckExpression.eval (pair a b) p t d = Cantor.pair
      (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d) := by
  simp [pair,ActualCheckExpression.eval,ActualArithmeticGraph.eval_standard,ActualArithmeticGraph.evalNat]

theorem mpAtom_standard (b : Scalar) (p t d : Nat) :
    ActualCheckExpression.eval (mpAtom b) p t d=atom (.mp (ActualCheckExpression.eval b p t d)) := by
  simp [mpAtom,pair_standard,ActualCheckExpression.eval,atom,encodeCommand,numeral_eq_natCast]

theorem axAtom_standard (c a b : Scalar) (p t d : Nat) :
    ActualCheckExpression.eval (axAtom c a b) p t d=atom
      (.ax (ActualCheckExpression.eval c p t d) (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d)) := by
  simp [axAtom,pair_standard,ActualCheckExpression.eval,atom,encodeCommand,numeral_eq_natCast]
  rfl

theorem j_standard (u : Scalar) (p t d : Nat) :
    eval (j u) p t d=encode (atoms (J (ActualCheckExpression.eval u p t d))) := by
  by_cases hu : ActualCheckExpression.eval u p t d=0 <;>
    simp [j,eval,singleton,mpAtom_standard,ActualCheckExpression.eval,J,hu,atoms]

theorem head_standard (k : Nat) (a b c : Scalar) (p t d : Nat) :
    eval (head k a b c) p t d=encode (atoms (headWord k
      (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d) (ActualCheckExpression.eval c p t d))) := by
  simp only [head,eval,literal_standard,axAtom_standard,headWord,atoms,
    List.map_append,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    encode_append,encode_cons]

/-- Foundation's model subtraction agrees with standard truncated subtraction. -/
theorem sub_standard (a b : Nat) :
    @HSub.hSub Nat Nat Nat (@instHSub Nat instSub_foundation) a b =
      @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b := by
  symm
  apply FFL.FirstOrder.Arithmetic.sub_eq_iff.mpr
  constructor
  · intro h
    simp only [FFL.FirstOrder.Arithmetic.le_def] at h
    have hba : _root_.Nat.le b a := by
      rcases h with rfl | h
      · exact _root_.Nat.le_refl _
      · exact _root_.Nat.le_of_lt h
    exact (_root_.Nat.add_sub_of_le hba).symm
  · intro h
    have hab : _root_.Nat.le a b := _root_.Nat.le_of_lt h
    exact _root_.Nat.sub_eq_zero_of_le hab

theorem head8_standard (a b c u : Scalar) (p t d : Nat) :
    eval (head8 a b c u) p t d=encode (atoms (head8Word
      (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d)
      (ActualCheckExpression.eval c p t d) (ActualCheckExpression.eval u p t d))) := by
  simp only [head8,eval,literal_standard,j_standard,axAtom_standard,ActualCheckExpression.eval,
    head8Word,atoms,List.map_append,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    encode_append,encode_cons]
  simp only [sub_standard]

theorem gate_standard (a b c : Scalar) (p t d : Nat) :
    eval (gate a b c) p t d=encode (atoms (gateWord
      (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d) (ActualCheckExpression.eval c p t d))) := by
  simp only [gate,eval,singleton,literal_standard,axAtom_standard,gateWord,atoms,
    List.map_append,List.map_cons,List.map_nil,encode_append,encode_cons,encode_nil]

theorem gen_standard (i : Scalar) (p t d : Nat) :
    eval (gen i) p t d=encode (atoms (genTail (ActualCheckExpression.eval i p t d))) := by
  simp only [gen,eval,literal_standard,j_standard,axAtom_standard,ActualCheckExpression.eval,
    genTail,atoms,List.map_append,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    encode_append,encode_cons]
  simp

theorem mp_standard (b : Scalar) (p t d : Nat) :
    eval (mp b) p t d=encode (atoms (mpTail (ActualCheckExpression.eval b p t d))) := by
  simp only [mp,eval,singleton,literal_standard,mpAtom_standard,axAtom_standard,ActualCheckExpression.eval,
    mpTail,atoms,List.map_append,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    encode_append,encode_cons,encode_nil]
  simp

#print axioms literal_standard
#print axioms head_standard
#print axioms head8_standard
#print axioms gen_standard
#print axioms mp_standard
end M6.PA.ActualWordMacros

