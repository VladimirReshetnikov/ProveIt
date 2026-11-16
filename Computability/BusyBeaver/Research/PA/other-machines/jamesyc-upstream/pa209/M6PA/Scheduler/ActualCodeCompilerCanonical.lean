module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCodeCompiler
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor M6.Source.Enumeration
open M6.Source.ActualCommandMacros
attribute [local irreducible] PUSH H genTail mpTail headWord head8Word gateWord

theorem compileTree_encode {a : Nat} (p : Proof a) (fuel : Nat) (hf : depth p≤fuel) :
    compileTree fuel (encode p)=compile p := by
  induction p generalizing fuel with
  | @mp a b p q ihp ihq =>
    cases fuel with
    | zero => have h:=depth_positive (.mp p q); omega
    | succ fuel =>
      have hp : depth p≤fuel := by change max (depth p) (depth q)+1≤fuel+1 at hf; omega
      have hq : depth q≤fuel := by change max (depth p) (depth q)+1≤fuel+1 at hf; omega
      change compileTree (fuel+1) (pair 0 (pack3 b (encode p) (encode q))) =
        compile q ++ PUSH ++ compile p ++ PUSH ++ mpTail b
      rw [compileTree_pair]
      simp [ruleCompile,ihp fuel hp,ihq fuel hq]
  | @all x a p ih =>
    cases fuel with
    | zero => have h:=depth_positive (.all x p); omega
    | succ fuel =>
      have hp : depth p≤fuel := by change depth p+1≤fuel+1 at hf; omega
      change compileTree (fuel+1) (pair 1 (pack2 x (encode p))) = compile p ++ genTail x
      rw [compileTree_pair]
      simp [ruleCompile,ih fuel hp]
  | r1 a b =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 2 (pack2 a b)) = headWord 1 a b 0
      rw [compileTree_pair]
      simp [ruleCompile]
  | r2 a b c =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 3 (pack3 a b c)) = headWord 2 a b c
      rw [compileTree_pair]
      simp [ruleCompile]
  | r3 a b c =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 4 (pack3 a b c)) = headWord 3 a b c
      rw [compileTree_pair]
      simp [ruleCompile]
  | r4 a b c =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 5 (pack3 a b c)) = headWord 4 a b c
      rw [compileTree_pair]
      simp [ruleCompile]
  | r5 a b c =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 6 (pack3 a b c)) = headWord 5 a b c
      rw [compileTree_pair]
      simp [ruleCompile]
  | r6 a b =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 7 (pack2 a b)) = headWord 6 a b 0
      rw [compileTree_pair]
      simp [ruleCompile]
  | r7 a b c =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 8 (pack3 a b c)) = headWord 7 a b c
      rw [compileTree_pair]
      simp [ruleCompile]
  | r8 a b c u hu =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 9 (pack4 a b c u)) = head8Word a b c u
      rw [compileTree_pair]
      simp [ruleCompile,hu]
  | bundle a b c ha hb =>
    cases fuel with
    | zero => change 1≤0 at hf; omega
    | succ fuel =>
      change compileTree (fuel+1) (pair 10 (pack3 a b c)) = gateWord a b c
      rw [compileTree_pair]
      simp [ruleCompile,ha,hb]

theorem compileCertificate_certificate {a : Nat} (p : Proof a) :
    compileCertificate (certificate p)=compile p := by
  simp only [compileCertificate,certificate,decode_pair]
  exact compileTree_encode p (depth p) (Nat.le_refl _)

#print axioms compileTree_encode
#print axioms compileCertificate_certificate
end M6.PA.NativeCalculus.ActualBasis.Code

