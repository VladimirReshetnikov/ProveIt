import Trace74GuardFreeRankUpper

/-! Source draft: the lower-endpoint polynomial certificate as an ordered-ring
    inequality. No Pell, graph-zero or divisibility binding is claimed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Trace74FirstThreeLower
variable {R : Type*} [CommRing R]

def k (X Y : R) : R := 32*(X*Y^2)^2+32*(X*Y^2)+6
def c (X Y : R) : R := 16*(Y*(X+1)+1)^4-12*(Y*(X+1)+1)^2+1
def slack (X Y W : R) : R :=
  16*Y^4*(X^2*W+4*X+1)+32*(2*X^3+6*X^2+5*X+2)*Y^3+
    (84*X^2+136*X+84)*Y^2+40*X*Y+34*(Y-1)+33

theorem identity (X Y W : R) (h : 2*Y+W=X^2+4*X+4) :
    c X Y=k X Y*(Y+1)+slack X Y W := by
  have he : c X Y-k X Y*(Y+1)-slack X Y W =
      16*X^2*Y^4*((X^2+4*X+4)-(2*Y+W)) := by
    dsimp [c,k,slack]
    ring
  rw [←h,sub_self,mul_zero] at he
  linear_combination he

section Ordered
variable [LinearOrder R] [IsStrictOrderedRing R]

theorem lower_contradiction (X Y W : R)
    (hX : 0≤X) (hY : 1≤Y) (hW : 0≤W)
    (h : 2*Y+W=X^2+4*X+4) : k X Y*(Y+1)<c X Y := by
  have hY0 : 0≤Y := le_trans (by norm_num : (0:R)≤1) hY
  have hY1 : 0≤Y-1 := sub_nonneg.mpr hY
  have hs : 0<slack X Y W := by
    dsimp [slack]
    positivity
  rw [identity X Y W h]
  linarith
end Ordered

#print axioms identity
#print axioms lower_contradiction
end Trace74FirstThreeLower
