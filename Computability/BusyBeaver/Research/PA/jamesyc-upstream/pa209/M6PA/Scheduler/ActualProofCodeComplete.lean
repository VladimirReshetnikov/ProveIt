module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualProofCode
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor

theorem depth_positive {a : Nat} (p : Proof a) : 0 < depth p := by
  cases p <;> exact Nat.zero_lt_succ _

theorem check_pair (fuel tag data : Nat) :
    check (fuel+1) (pair tag data) = ruleCheck (check fuel) tag data := by
  simp only [check,decode_pair]

theorem check_encode {a : Nat} (p : Proof a) (fuel : Nat) (hf : depth p ≤ fuel) :
    check fuel (encode p) = some a := by
  induction p generalizing fuel with
  | @mp a b p q ihp ihq =>
    cases fuel with
    | zero => have h := depth_positive (.mp p q); omega
    | succ fuel =>
      have hp : depth p ≤ fuel := by change max (depth p) (depth q)+1 ≤ fuel+1 at hf; omega
      have hq : depth q ≤ fuel := by change max (depth p) (depth q)+1 ≤ fuel+1 at hf; omega
      change check (fuel+1) (pair 0 (pack3 b (encode p) (encode q))) = some b
      rw [check_pair]
      simp [ruleCheck,ihp fuel hp,ihq fuel hq,source_wim_eq]
  | @all x a p ih =>
    cases fuel with
    | zero => have h := depth_positive (.all x p); omega
    | succ fuel =>
      have hp : depth p ≤ fuel := by change depth p+1 ≤ fuel+1 at hf; omega
      change check (fuel+1) (pair 1 (pack2 x (encode p))) = some (wal x a)
      rw [check_pair]
      simp [ruleCheck,ih fuel hp,source_wal_eq]
  | r1 a b =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 2 (pack2 a b)) = some (ActualAXCode.rho1 a b)
      rw [check_pair]
      simp [ruleCheck]
  | r2 a b c =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 3 (pack3 a b c)) = some (ActualAXCode.rho2 a b c)
      rw [check_pair]
      simp [ruleCheck]
  | r3 a b c =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 4 (pack3 a b c)) = some (ActualAXCode.rho3 a b c)
      rw [check_pair]
      simp [ruleCheck]
  | r4 a b c =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 5 (pack3 a b c)) = some (ActualAXCode.rho4 a b c)
      rw [check_pair]
      simp [ruleCheck]
  | r5 a b c =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 6 (pack3 a b c)) = some (ActualAXCode.rho5 a b c)
      rw [check_pair]
      simp [ruleCheck]
  | r6 a b =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 7 (pack2 a b)) = some (ActualAXCode.rho6 a b)
      rw [check_pair]
      simp [ruleCheck]
  | r7 a b c =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 8 (pack3 a b c)) = some (ActualAXCode.rho7 a b c)
      rw [check_pair]
      simp [ruleCheck]
  | r8 a b c u hu =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 9 (pack4 a b c u)) = some (ActualAXCode.rho8 a b c u)
      rw [check_pair]
      simp [ruleCheck,hu]
  | bundle a b c ha hb =>
    cases fuel with
    | zero => change 1 ≤ 0 at hf; omega
    | succ fuel =>
      change check (fuel+1) (pair 10 (pack3 a b c)) = some (ActualAXCode.bundle a b c)
      rw [check_pair]
      simp [ruleCheck,ha,hb]

theorem verify_certificate {a : Nat} (p : Proof a) : verify (certificate p) = some a := by
  simp only [verify,certificate,decode_pair]
  exact check_encode p (depth p) (Nat.le_refl _)
#print axioms check_encode
#print axioms verify_certificate
end M6.PA.NativeCalculus.ActualBasis.Code

