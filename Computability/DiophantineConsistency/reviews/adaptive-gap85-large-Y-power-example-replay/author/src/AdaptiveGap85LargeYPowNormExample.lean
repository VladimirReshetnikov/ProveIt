import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! A partial natural-number Pell configuration with X=2^m and Y≥7·2^m.
It violates cubic divisibility and is not asserted to be a full 85-zero. -/
namespace AdaptiveGap85LargeYPowNormExample

def X : ℕ := 32
def Y : ℕ := 579
def eta : ℕ := 1124771305294163
def zeta : ℕ := 2557910790150835
def first : ℕ := 39506754748831455196225
def main : ℕ := 40767096680767114407749
def Q : ℕ := X*Y*Y
def a : ℕ := Y*(X+1)
def k : ℕ := eta+zeta
def c : ℕ := eta+Y*k

theorem parameters : X=2^5 ∧ 7*2^5≤Y ∧ 0<eta ∧ 0<zeta := by
  norm_num [X,Y,eta,zeta]

theorem two_norms : first*first=1+Q*(Q+1)*k*k ∧
    main*main=1+((a+1)*(a+3))*c*c := by
  norm_num [first,main,Q,a,k,c,X,Y,eta,zeta]

theorem index_polynomials :
    k=32*Q*Q+32*Q+6 ∧
    c=16*a^4+128*a^3+372*a^2+464*a+209 ∧
    first=32*Q^3+48*Q^2+18*Q+1 ∧
    main=16*a^5+160*a^4+620*a^3+1160*a^2+1045*a+362 := by
  norm_num [first,main,Q,a,k,c,X,Y,eta,zeta]

theorem no_nontrivial_cube (q : ℕ) (hq : 2≤q) : ¬q*q*q∣Y := by
  intro hdiv
  have hcub : q*q*q≤579 := Nat.le_of_dvd (by decide) (by simpa [Y] using hdiv)
  have hq8 : q≤8 := by
    by_contra hn
    have hq9 : 9≤q := by omega
    have h729 : 729≤q*q*q := by
      calc
        729 = 9*9*9 := by norm_num
        _ ≤ q*q*q := Nat.mul_le_mul (Nat.mul_le_mul hq9 hq9) hq9
    omega
  interval_cases q <;> norm_num [Y] at hdiv
end AdaptiveGap85LargeYPowNormExample
