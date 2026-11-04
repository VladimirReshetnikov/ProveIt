import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! UNCHECKED DRAFT. Scalar natural rank and q⁴ window under individual F/C
bounds, without the stronger F+C<q guard. No graph-zero implication is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74NaturalRankWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem add_le_right {x y : V} (h : x≤y) (z : V) : x+z≤y+z :=
  _root_.add_le_add h (le_refl z)

private theorem slack_equation (q r t G L M Z : V)
    (hr : r+1=q) (ht : t+1=q*q)
    (hG : G+L+q+1=q*q) (hM : M+Z+q+1=r*(1+2*q)) :
    G*t+M+L*t+Z+q^3+q+1=q^4 := by
  have ht' : t=r*r+2*r := by
    apply add_right_cancel (b:=(1:V))
    calc
      t+1=q*q := ht
      _=(r*r+2*r)+1 := by rw [←hr]; ring
  apply add_right_cancel (b:=(q+1)*t+(q+1))
  calc
    (G*t+M+L*t+Z+q^3+q+1)+((q+1)*t+(q+1))=
      (G+L+q+1)*t+(M+Z+q+1)+q^3+q+1 := by ring
    _=q*q*t+r*(1+2*q)+q^3+q+1 := by rw [hG,hM]
    _=q^4+((q+1)*t+(q+1)) := by rw [ht',←hr]; ring

def rank (q MC MF J F C : V) : V :=
  (q*(q-F)-C)*(q^2-1)+(MC+q*MF)*J

theorem scalar_window (q beta MC MF J F C : V)
    (hb31 : (31:V)≤beta) (hJ : 0<J) (hFpos : 0<F) (hF : F<q)
    (hCpos : 0<C) (hC : C≤q) (hMC : MC<beta)
    (hMFlo : beta<MF) (hMFhi : MF<2*beta) (hq : q=beta*J+1) :
    3*q<rank q MC MF J F C ∧ rank q MC MF J F C+q^3+q+1≤q^4 := by
  have hJ1 : 1≤J := pos_iff_one_le.mp hJ
  have hbetaJ : (31:V)≤beta*J := le_trans hb31 (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hJ1 (by simp : (0:V)≤beta))
  have hq32 : (32:V)≤q := by
    rw [hq]
    simpa only [show (32:V)=31+1 by ring,add_comm] using _root_.add_le_add_right hbetaJ (1:V)
  have hqpos : 0<q := lt_of_lt_of_le (by norm_num : (0:V)<32) hq32
  have hq1 : q-1+1=q := tsub_add_cancel_of_le (pos_iff_one_le.mp hqpos)
  have hqF : 0<q-F := tsub_pos_iff_lt.mpr hF
  have hv : q-F+F=q := tsub_add_cancel_of_le (le_of_lt hF)
  have hCmul : C≤q*(q-F) := le_trans hC
    (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hqF))
  let G:=q*(q-F)-C
  let M:=(MC+q*MF)*J
  have hG : G+C=q*(q-F) := tsub_add_cancel_of_le hCmul
  have hq3 : (3:V)<q := lt_of_lt_of_le (by norm_num : (3:V)<32) hq32
  have hqmf : q≤MF*J := calc
    q=beta*J+1 := hq
    _≤beta*J+J := by simpa [add_comm] using add_le_add_left hJ1 (beta*J)
    _=(beta+1)*J := by ring
    _≤MF*J := mul_le_mul_of_nonneg_right (lt_iff_succ_le.mp hMFlo) (by simp)
  have hq2M : q*q≤M := calc
    q*q≤q*(MF*J) := mul_le_mul_of_nonneg_left hqmf (by simp)
    _=(q*MF)*J := by ring
    _≤(MC+q*MF)*J := mul_le_mul_of_nonneg_right (by simp) (by simp)
  have hlo : 3*q<rank q MC MF J F C := calc
    3*q<q*q := mul_lt_mul_of_pos_right hq3 hqpos
    _≤M := hq2M
    _≤rank q MC MF J F C := by dsimp [rank,M,G]; simp
  have hF0 : F-1+1=F := tsub_add_cancel_of_le (pos_iff_one_le.mp hFpos)
  have hC0 : C-1+1=C := tsub_add_cancel_of_le (pos_iff_one_le.mp hCpos)
  have hJ0 : J-1+1=J := tsub_add_cancel_of_le hJ1
  have hMC0 : MC+(beta-MC-1)+1=beta := calc
    MC+(beta-MC-1)+1=(beta-MC-1+1)+MC := by ring
    _=(beta-MC)+MC := by rw [tsub_add_cancel_of_le (pos_iff_one_le.mp (tsub_pos_iff_lt.mpr hMC))]
    _=beta := tsub_add_cancel_of_le (le_of_lt hMC)
  have hMF0 : MF+(2*beta-MF-1)+1=2*beta := calc
    MF+(2*beta-MF-1)+1=(2*beta-MF-1+1)+MF := by ring
    _=(2*beta-MF)+MF := by rw [tsub_add_cancel_of_le (pos_iff_one_le.mp (tsub_pos_iff_lt.mpr hMFhi))]
    _=2*beta := tsub_add_cancel_of_le (le_of_lt hMFhi)
  let L:=q*(F-1)+(C-1)
  let Z:=(q+1)*(J-1)+J*((beta-MC-1)+q*(2*beta-MF-1))
  have hGsum : G+L+q+1=q*q := calc
    G+L+q+1=(G+(C-1+1))+q*(F-1+1) := by dsimp [L]; ring
    _=(G+C)+q*F := by rw [hC0,hF0]
    _=q*(q-F)+q*F := by rw [hG]
    _=q*(q-F+F) := by ring
    _=q*q := by rw [hv]
  have hbeta : beta*J=q-1 := by
    apply add_right_cancel (b:=(1:V))
    exact hq.symm.trans hq1.symm
  have hMsum : M+Z+q+1=(q-1)*(1+2*q) := calc
    M+Z+q+1=(MC+q*MF)*J+(q+1)*(J-1+1)+J*((beta-MC-1)+q*(2*beta-MF-1)) := by dsimp [M,Z]; ring
    _=J*((MC+(beta-MC-1)+1)+q*(MF+(2*beta-MF-1)+1)) := by rw [hJ0]; ring
    _=beta*J*(1+2*q) := by rw [hMC0,hMF0]; ring
    _=(q-1)*(1+2*q) := by rw [hbeta]
  have hq2 : 1≤q*q := one_le_mul (pos_iff_one_le.mp hqpos) (pos_iff_one_le.mp hqpos)
  have ht : q^2-1+1=q*q := by simpa only [pow_two] using tsub_add_cancel_of_le hq2
  have hslack : rank q MC MF J F C+L*(q^2-1)+Z+q^3+q+1=q^4 := by
    exact slack_equation q (q-1) (q^2-1) G L M Z hq1 ht hGsum hMsum
  have hupper : rank q MC MF J F C+q^3+q+1≤q^4 := by
    have hh : rank q MC MF J F C≤rank q MC MF J F C+L*(q^2-1)+Z := by simp
    have hh' := add_le_right (add_le_right (add_le_right hh (q^3)) q) 1
    exact le_of_le_of_eq hh' hslack
  exact ⟨hlo,hupper⟩

#print axioms Trace74NaturalRankWindow.scalar_window
end Trace74NaturalRankWindow
