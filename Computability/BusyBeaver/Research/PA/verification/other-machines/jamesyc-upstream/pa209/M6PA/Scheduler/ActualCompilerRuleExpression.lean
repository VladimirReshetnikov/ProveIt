module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualWordMacros
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCompilerRuleExpression
open ActualWordExpression
def zero : Scalar := .num 0
def r1 : Scalar := .right .payload
def r2 : Scalar := .right r1
def r3 : Scalar := .right r2
def r4 : Scalar := .right r3
def a : Scalar := .left .payload
def b : Scalar := .left r1
def c : Scalar := .left r2
def u : Scalar := .left r3
def requireZero (tail : Scalar) (result : Expr) : Expr := .ifEq tail zero result .nil
open M6.Source.ActualCommandMacros M6.Source.CommandAtomEncoding

def mp : Expr := requireZero r3 <|
  .append (.lookup c) (.append (ActualWordMacros.literal (atoms PUSH))
    (.append (.lookup b) (.append (ActualWordMacros.literal (atoms PUSH)) (ActualWordMacros.mp a))))
def gen : Expr := requireZero r2 (.append (.lookup b) (ActualWordMacros.gen a))
def leaf1 : Expr := requireZero r2 (ActualWordMacros.head 1 a b zero)
def leaf2 : Expr := requireZero r3 (ActualWordMacros.head 2 a b c)
def leaf3 : Expr := requireZero r3 (ActualWordMacros.head 3 a b c)
def leaf4 : Expr := requireZero r3 (ActualWordMacros.head 4 a b c)
def leaf5 : Expr := requireZero r3 (ActualWordMacros.head 5 a b c)
def leaf6 : Expr := requireZero r2 (ActualWordMacros.head 6 a b zero)
def leaf7 : Expr := requireZero r3 (ActualWordMacros.head 7 a b c)
def leaf8 : Expr := requireZero r4 (.ifLe u a (ActualWordMacros.head8 a b c u) .nil)
def rawBundle : Expr := requireZero r3 <|
  .ifEq c a .nil (.ifEq c b .nil (ActualWordMacros.gate a b c))

/-- The deterministic compiler checks local tuple/guard shape but does not
recheck child acceptance. The independent checker establishes validity. -/
def rule : Expr :=
  .ifEq .tag (.num 0) mp <|
  .ifEq .tag (.num 1) gen <|
  .ifEq .tag (.num 2) leaf1 <|
  .ifEq .tag (.num 3) leaf2 <|
  .ifEq .tag (.num 4) leaf3 <|
  .ifEq .tag (.num 5) leaf4 <|
  .ifEq .tag (.num 6) leaf5 <|
  .ifEq .tag (.num 7) leaf6 <|
  .ifEq .tag (.num 8) leaf7 <|
  .ifEq .tag (.num 9) leaf8 <|
  .ifEq .tag (.num 10) rawBundle .nil

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualWordCoding NativeCalculus.ActualBasis.Code SourceCantorInternal

private theorem requireZero_eval (tail : Scalar) (result : Expr) (p t d : Nat) :
    eval (requireZero tail result) p t d =
      if ActualCheckExpression.eval tail p t d=0 then eval result p t d else 0 := by
  by_cases h : ActualCheckExpression.eval tail p t d=0 <;>
    simp [requireZero,zero,eval,ActualCheckExpression.eval,h]

theorem leaf1_standard (previous tag payload : Nat) :
    eval leaf1 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 2 payload) := by
  rw [leaf1,requireZero_eval,ActualWordMacros.head_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2=0
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht]

theorem leaf2_standard (previous tag payload : Nat) :
    eval leaf2 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 3 payload) := by
  rw [leaf2,requireZero_eval,ActualWordMacros.head_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht]

theorem leaf3_standard (previous tag payload : Nat) :
    eval leaf3 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 4 payload) := by
  rw [leaf3,requireZero_eval,ActualWordMacros.head_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht]

theorem leaf4_standard (previous tag payload : Nat) :
    eval leaf4 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 5 payload) := by
  rw [leaf4,requireZero_eval,ActualWordMacros.head_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht]

theorem leaf5_standard (previous tag payload : Nat) :
    eval leaf5 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 6 payload) := by
  rw [leaf5,requireZero_eval,ActualWordMacros.head_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht]

theorem leaf6_standard (previous tag payload : Nat) :
    eval leaf6 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 7 payload) := by
  rw [leaf6,requireZero_eval,ActualWordMacros.head_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2=0
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht]

theorem leaf7_standard (previous tag payload : Nat) :
    eval leaf7 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 8 payload) := by
  rw [leaf7,requireZero_eval,ActualWordMacros.head_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht]

private theorem nat_le_condition (x y : Nat) : (x=y ∨ x<y) ↔ x≤y := by omega
private theorem ifLe_eval (x y : Scalar) (yes no : Expr) (p t d : Nat) :
    eval (.ifLe x y yes no) p t d = if ActualCheckExpression.eval x p t d ≤ ActualCheckExpression.eval y p t d then eval yes p t d else eval no p t d := by
  by_cases h : ActualCheckExpression.eval x p t d ≤ ActualCheckExpression.eval y p t d <;>
    simp [eval,FFL.FirstOrder.Arithmetic.le_def,nat_le_condition,h]
private theorem ifEq_eval (x y : Scalar) (yes no : Expr) (p t d : Nat) :
    eval (.ifEq x y yes no) p t d = if ActualCheckExpression.eval x p t d = ActualCheckExpression.eval y p t d then eval yes p t d else eval no p t d := by
  by_cases h : ActualCheckExpression.eval x p t d = ActualCheckExpression.eval y p t d <;>
    simp [eval,h]
private theorem append_eval (xs ys : Expr) (p t d : Nat) :
    eval (.append xs ys) p t d = InternalTrace.HFSAppend.append (eval xs p t d) (eval ys p t d) := rfl
private theorem lookup_eval (i : Scalar) (p t d : Nat) :
    eval (.lookup i) p t d = nth p (ActualCheckExpression.eval i p t d) := rfl

theorem leaf8_standard (previous tag payload : Nat) :
    eval leaf8 previous tag payload=encode (ruleCompileAtoms (fun _ => []) 9 payload) := by
  rw [leaf8,requireZero_eval,ifLe_eval,ActualWordMacros.head8_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode
    (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2).2=0
  all_goals by_cases hu : (M6.Source.Cantor.decode (M6.Source.Cantor.decode
    (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2).1 ≤ (M6.Source.Cantor.decode payload).1
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,unpack4,ht,
    FFL.FirstOrder.Arithmetic.le_def,nat_le_condition,hu,eval]

theorem bundle_standard (previous tag payload : Nat) :
    eval rawBundle previous tag payload=encode (ruleCompileAtoms (fun _ => []) 10 payload) := by
  rw [rawBundle,requireZero_eval,ifEq_eval,ifEq_eval,ActualWordMacros.gate_standard]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode
    (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals by_cases ha : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).1 = (M6.Source.Cantor.decode payload).1
  all_goals by_cases hb : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).1 = (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).1
  all_goals simp [a,b,c,u,r1,r2,r3,r4,zero,ActualCheckExpression.eval,
    decodeLeft,decodeRight,decodeState_standard,ruleCompileAtoms,unpack2,unpack3,ht,ha,hb,eval]

theorem gen_standard (rows : List (List Nat)) (tag payload : Nat) :
    eval gen (encodeRows rows) tag payload=encode (ruleCompileAtoms (fun i => rows.getD i []) 1 payload) := by
  rw [gen,requireZero_eval,append_eval,lookup_eval,ActualWordMacros.gen_standard,nth_encodeRows]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2=0
  all_goals simp [a,b,r1,r2,zero,ActualCheckExpression.eval,decodeLeft,decodeRight,decodeState_standard,
    ruleCompileAtoms,unpack2,ht,encode_append]

theorem mp_standard (rows : List (List Nat)) (tag payload : Nat) :
    eval mp (encodeRows rows) tag payload=encode (ruleCompileAtoms (fun i => rows.getD i []) 0 payload) := by
  rw [mp,requireZero_eval,append_eval,append_eval,append_eval,append_eval,
    lookup_eval,lookup_eval,ActualWordMacros.literal_standard,
    ActualWordMacros.mp_standard,nth_encodeRows,nth_encodeRows]
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals simp [a,b,c,r1,r2,r3,zero,ActualCheckExpression.eval,decodeLeft,decodeRight,decodeState_standard,
    ruleCompileAtoms,unpack2,unpack3,ht,encode_append]

#print axioms leaf8_standard
#print axioms mp_standard
end M6.PA.ActualCompilerRuleExpression

