module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCheckExpression
public import M6PA.Scheduler.ActualTableCoding
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualRuleExpression
open ActualCheckExpression ActualHeadGraphs
def zero : Expr := .num 0
def one : Expr := .num 1
def accepted (x : Expr) : Expr := .add x one
def r1 : Expr := .right .payload
def r2 : Expr := .right r1
def r3 : Expr := .right r2
def r4 : Expr := .right r3
def a : Expr := .left .payload
def b : Expr := .left r1
def c : Expr := .left r2
def u : Expr := .left r3
def h (e : ActualArithmeticGraph.Expr) : Expr := .head e a b c u
def requireZero (tail result : Expr) : Expr := .ifEq tail zero result zero
def minor : Expr := .nth .previous b
def major : Expr := .nth .previous c

/-- Exact V1 MP, with explicit conclusion a, minor child b, major child c.
Some zero is entry one and therefore passes the nonzero child test. -/
def mp : Expr := requireZero r3 <|
  .ifEq minor zero zero <| .ifEq major zero zero <|
  .ifEq major (accepted (.head implicationExpr (.sub minor one) a zero zero))
    (accepted a) zero

def gen : Expr := requireZero r2 <|
  .ifEq minor zero zero (accepted (.head universalExpr a (.sub minor one) zero zero))

def leaf1 : Expr := requireZero r2 (accepted (h rho1Expr))
def leaf2 : Expr := requireZero r3 (accepted (h rho2Expr))
def leaf3 : Expr := requireZero r3 (accepted (h rho3Expr))
def leaf4 : Expr := requireZero r3 (accepted (h rho4Expr))
def leaf5 : Expr := requireZero r3 (accepted (h rho5Expr))
def leaf6 : Expr := requireZero r2 (accepted (.head rho6Expr a b zero zero))
def leaf7 : Expr := requireZero r3 (accepted (h rho7Expr))
def leaf8 : Expr := requireZero r4 (.ifLe u a (accepted (h rho8Expr)) zero)
def rawBundle : Expr := requireZero r3 <|
  .ifEq c a zero (.ifEq c b zero (accepted (h bundleExpr)))

/-- Invalid tags reject. This finite selector has no unverified host lookup. -/
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
  .ifEq .tag (.num 10) rawBundle zero

open NativeCalculus.ActualBasis.Code ActualTableCoding
open SourceCantorInternal

/-- First exact V1 leaf calibration; field failure is encoded zero rather than
being confused with a successful proof of formula zero. -/
theorem leaf1_standard (previous tag payload : Nat) :
    eval leaf1 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 2 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2=0
  all_goals
    simp [leaf1,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho1_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,optionCode,ht]



theorem leaf2_standard (previous tag payload : Nat) :
    eval leaf2 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 3 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals
    simp [leaf2,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho2_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,optionCode,ht]

theorem leaf3_standard (previous tag payload : Nat) :
    eval leaf3 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 4 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals
    simp [leaf3,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho3_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,optionCode,ht]

theorem leaf4_standard (previous tag payload : Nat) :
    eval leaf4 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 5 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals
    simp [leaf4,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho4_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,optionCode,ht]

theorem leaf5_standard (previous tag payload : Nat) :
    eval leaf5 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 6 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals
    simp [leaf5,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho5_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,optionCode,ht]

theorem leaf6_standard (previous tag payload : Nat) :
    eval leaf6 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 7 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2=0
  all_goals
    simp [leaf6,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho6_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,optionCode,ht]

theorem leaf7_standard (previous tag payload : Nat) :
    eval leaf7 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 8 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals
    simp [leaf7,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho7_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,optionCode,ht]

private theorem nat_le_condition (a b : Nat) : (a=b ∨ a<b) ↔ a≤b := by omega

theorem leaf8_standard (previous tag payload : Nat) :
    eval leaf8 previous tag payload =
      optionCode (ruleCheck (fun _ => none) 9 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode
    (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2).2=0
  all_goals by_cases hu : (M6.Source.Cantor.decode (M6.Source.Cantor.decode
    (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2).1 ≤ (M6.Source.Cantor.decode payload).1
  all_goals
    simp [leaf8,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,rho8_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,unpack4,optionCode,ht,
      FFL.FirstOrder.Arithmetic.le_def,nat_le_condition,hu]

theorem bundle_standard (previous tag payload : Nat) :
    eval rawBundle previous tag payload =
      optionCode (ruleCheck (fun _ => none) 10 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode
    (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals by_cases ha : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).1 = (M6.Source.Cantor.decode payload).1
  all_goals by_cases hb : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).1 = (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).1
  all_goals
    simp [rawBundle,requireZero,accepted,h,a,b,c,u,r1,r2,r3,r4,zero,one,
      eval,ActualArithmeticGraph.eval_standard,bundle_exact,
      decodeLeft,decodeRight,decodeState_standard,
      ruleCheck,unpack2,unpack3,optionCode,ht,ha,hb]



private theorem optionCode_if (p : Prop) [Decidable p] (x y : Option Nat) :
    optionCode (if p then x else y) = if p then optionCode x else optionCode y := by
  by_cases hp : p <;> simp [hp]

theorem gen_standard (xs : List (Option Nat)) (tag payload : Nat) :
    eval gen (encodeTable xs) tag payload =
      optionCode (ruleCheck (fun i => xs.getD i none) 1 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2=0
  all_goals cases hm : xs.getD (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).1 none
  all_goals simp only [List.getD] at hm
  all_goals
    simp [gen,requireZero,accepted,minor,a,b,r1,r2,zero,one,
      eval,ActualArithmeticGraph.eval_standard,universal_exact,
      decodeLeft,decodeRight,decodeState_standard,nth_encodeTable,
      ruleCheck,unpack2,optionCode,ht,hm]

theorem mp_standard (xs : List (Option Nat)) (tag payload : Nat) :
    eval mp (encodeTable xs) tag payload =
      optionCode (ruleCheck (fun i => xs.getD i none) 0 payload) := by
  by_cases ht : (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).2=0
  all_goals cases hm : xs.getD (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).1 none
  all_goals cases hi : xs.getD (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode payload).2).2).1 none
  all_goals simp only [List.getD] at hm hi
  all_goals
    simp [mp,requireZero,accepted,minor,major,a,b,c,r1,r2,r3,zero,one,
      eval,ActualArithmeticGraph.eval_standard,implication_exact,
      decodeLeft,decodeRight,decodeState_standard,nth_encodeTable,
      ruleCheck,unpack2,unpack3,optionCode_if,optionCode,ht,hm,hi]
  all_goals split <;> rfl

end M6.PA.ActualRuleExpression

