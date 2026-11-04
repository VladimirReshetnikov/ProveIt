import Trace74OddOrdinateBound

/-! UNCHECKED DRAFT. Fifth-ordinate growth in the same arithmetic models. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N2FifthGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ordinate_five (b : V) :
    ycoord 5 b=16*(b+1)^4+64*(b+1)^3+84*(b+1)^2+40*(b+1)+5 := by
  have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
  have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
  have hx2 : xcoord 2 b=(b+2)*xcoord 1 b+ArithmeticPellRecurrence.delta b*ycoord 1 b := by
    simpa only [show (1:V)+1=2 by ring] using x_succ (1:V) b
  have hy2 : ycoord 2 b=xcoord 1 b+(b+2)*ycoord 1 b := by
    simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) b
  have hx3 : xcoord 3 b=(b+2)*xcoord 2 b+ArithmeticPellRecurrence.delta b*ycoord 2 b := by
    simpa only [show (2:V)+1=3 by ring] using x_succ (2:V) b
  have hy3 : ycoord 3 b=xcoord 2 b+(b+2)*ycoord 2 b := by
    simpa only [show (2:V)+1=3 by ring] using y_succ (2:V) b
  have hx4 : xcoord 4 b=(b+2)*xcoord 3 b+ArithmeticPellRecurrence.delta b*ycoord 3 b := by
    simpa only [show (3:V)+1=4 by ring] using x_succ (3:V) b
  have hy4 : ycoord 4 b=xcoord 3 b+(b+2)*ycoord 3 b := by
    simpa only [show (3:V)+1=4 by ring] using y_succ (3:V) b
  have hy5 : ycoord 5 b=xcoord 4 b+(b+2)*ycoord 4 b := by
    simpa only [show (4:V)+1=5 by ring] using y_succ (4:V) b
  rw [hy5,hx4,hy4,hx3,hy3,hx2,hy2,hx1,hy1]
  unfold ArithmeticPellRecurrence.delta
  ring

theorem ordinate_five_exceeds_small_k (X Y : V) (hX : 0<X) (hY : 0<Y) :
    (8*X*(Y*Y)+4)*(Y+1) < ycoord 5 (Y*(X+1)-1) := by
  have hX1 : 1≤X := pos_iff_one_le.mp hX
  have hY1 : 1≤Y := pos_iff_one_le.mp hY
  have hXY2 : 1≤X*(Y*Y) := one_le_mul hX1 (one_le_mul hY1 hY1)
  have hYplus : Y+1≤2*Y := calc
    Y+1≤Y+Y := _root_.add_le_add (le_refl Y) hY1
    _=2*Y := by ring
  have hfactor : 8*X*(Y*Y)+4≤12*X*(Y*Y) := by
    have hf : (4:V)≤4*(X*(Y*Y)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hXY2 (by simp : (0:V)≤4)
    calc
      8*X*(Y*Y)+4≤8*X*(Y*Y)+4*(X*(Y*Y)) := _root_.add_le_add (le_refl _) hf
      _=12*X*(Y*Y) := by ring
  have hk_upper : (8*X*(Y*Y)+4)*(Y+1)≤24*X*Y^3 := calc
    (8*X*(Y*Y)+4)*(Y+1)≤(12*X*(Y*Y))*(2*Y) := mul_le_mul hfactor hYplus (by simp) (by simp)
    _=24*X*Y^3 := by ring
  have hx2 : 2*X≤(X+1)^2 := calc
    2*X≤2*X+(X^2+1) := by simp
    _=(X+1)^2 := by ring
  have hxone : 1≤(X+1)^2 := by
    have h : 1≤X+1 := by simp
    simpa only [pow_two] using one_le_mul h h
  have hx4 : 2*X≤(X+1)^4 := calc
    2*X≤(X+1)^2 := hx2
    _≤(X+1)^2*(X+1)^2 := le_mul_of_one_le_right (by simp) hxone
    _=(X+1)^4 := by ring
  have hy4 : Y^3≤Y^4 := calc
    Y^3≤Y^3*Y := le_mul_of_one_le_right (by simp) hY1
    _=Y^4 := by ring
  have hA4 : 2*X*Y^3≤(Y*(X+1))^4 := calc
    2*X*Y^3≤(X+1)^4*Y^4 := mul_le_mul hx4 hy4 (by simp) (by simp)
    _=(Y*(X+1))^4 := by ring
  have hT : 0<X*Y^3 := mul_pos hX (pow_pos hY _)
  have hstrict : 24*X*Y^3<32*X*Y^3 := calc
    24*X*Y^3<24*X*Y^3+8*(X*Y^3) := lt_add_of_pos_right _ (mul_pos (by norm_num) hT)
    _=32*X*Y^3 := by ring
  have hApos : 0<Y*(X+1) := mul_pos hY (add_pos hX (by simp))
  have hA1 : Y*(X+1)-1+1=Y*(X+1) := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hpoly : ycoord 5 (Y*(X+1)-1)=
      16*(Y*(X+1))^4+64*(Y*(X+1))^3+84*(Y*(X+1))^2+40*(Y*(X+1))+5 := by
    rw [ordinate_five,hA1]
  calc
    (8*X*(Y*Y)+4)*(Y+1)≤24*X*Y^3 := hk_upper
    _<32*X*Y^3 := hstrict
    _≤16*(Y*(X+1))^4 := by
      simpa only [show (32:V)=16*2 by ring,mul_assoc] using mul_le_mul_of_nonneg_left hA4 (by simp : (0:V)≤16)
    _<ycoord 5 (Y*(X+1)-1) := by
      rw [hpoly]
      have hrest : 0<64*(Y*(X+1))^3+84*(Y*(X+1))^2+40*(Y*(X+1))+5 := by simp
      calc
        16*(Y*(X+1))^4 < 16*(Y*(X+1))^4+
            (64*(Y*(X+1))^3+84*(Y*(X+1))^2+40*(Y*(X+1))+5) := lt_add_of_pos_right _ hrest
        _=16*(Y*(X+1))^4+64*(Y*(X+1))^3+84*(Y*(X+1))^2+40*(Y*(X+1))+5 := by ring

#print axioms Trace74N2FifthGrowth.ordinate_five
#print axioms Trace74N2FifthGrowth.ordinate_five_exceeds_small_k
end Trace74N2FifthGrowth
