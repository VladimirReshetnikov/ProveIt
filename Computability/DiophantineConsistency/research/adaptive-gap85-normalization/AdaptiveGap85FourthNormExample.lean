import Mathlib.Tactic.NormNum

/-! A concrete partial arithmetic configuration with first Pell index three
and main Pell index four. It is not asserted to be an 85-equation zero. -/
namespace AdaptiveGap85FourthNormExample

def X : ℕ := 253
def Y : ℕ := 8
def q : ℕ := 2
def eta : ℕ := 197347912
def zeta : ℕ := 8192957886
def first : ℕ := 135860026569345
def main : ℕ := 136928445049441
def Q : ℕ := X*Y*Y
def a : ℕ := Y*(X+1)
def k : ℕ := eta+zeta
def c : ℕ := eta+Y*k

theorem parameters : 1≤X ∧ 8≤Y ∧ 2≤q ∧ 0<eta ∧ 0<zeta ∧ q*q*q∣Y := by
  norm_num [X,Y,q,eta,zeta]

theorem two_norms : first*first=1+Q*(Q+1)*k*k ∧
    main*main=1+((a+1)*(a+3))*c*c := by
  norm_num [first,main,Q,a,k,c,X,Y,eta,zeta]

theorem index_polynomials :
    k=32*Q*Q+32*Q+6 ∧ c=4*(a+2)*(2*((a+1)*(a+3))+1) ∧
    first=32*Q^3+48*Q^2+18*Q+1 ∧
    main=8*a^4+64*a^3+184*a^2+224*a+97 := by
  norm_num [first,main,Q,a,k,c,X,Y,eta,zeta]
end AdaptiveGap85FourthNormExample
