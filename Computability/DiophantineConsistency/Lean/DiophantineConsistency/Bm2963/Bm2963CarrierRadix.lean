import DiophantineConsistency.ArithmeticCarrierRadix2011
import DiophantineConsistency.Bm2963.Bm2963Ports

/-! # The block-mask2963 maintained zero gives its represented power and radix

The counterpart of `ArithmeticCarrierRadix2011` at the block-mask2963 ports
(`β = 2^139261 − 1`, width `139261 = 47·2963`). The power and the radix
alignment are the port-generic `ArithmeticPellPowerRecovery.maintained_power`
and `ArithmeticRadixAlignment.factor_alignment`; only positivity and the
literal split zero of `Bm2963Ports.expression` are premises. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Bm2963CarrierRadix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 (Equations)
open ObjectCurrentEquation2011 (internalZero_positiveShift)
open Bm2963Ports
open ArithmeticCarrierRadix2011 (exp_nat_cast)
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.radix Bm2963MaskData.beta
  Bm2963MaskData.lowPort Bm2963MaskData.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (v : Fin 14 → V) : V := (Bm2963MaskData.beta:V)*v 0+1
def X (v : Fin 14 → V) : V := v 8*q v
def Y (v : Fin 14 → V) : V := v 7*(q v)^3
def rank (v : Fin 14 → V) : V :=
  ((q v-1)*(q v-v 1)+v 2)*((q v)^2-1)+
    ((Bm2963MaskData.lowPort:V)+q v*((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V))*v 0

private theorem cast_pred_power (r n : ℕ) (hr : 0<r) :
    ((r^n-1:ℕ):V)+1=(r:V)^n := by
  have h : (r^n-1)+1=r^n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.pow_pos hr)))
  exact_mod_cast h

/-- The enormous fixed coefficient is related symbolically to its width. -/
theorem current_beta_exp_add_one :
    (Bm2963MaskData.beta:V)+1=Exp.exp (Bm2963MaskData.width:V) := by
  unfold Bm2963MaskData.beta
  rw [cast_pred_power Bm2963MaskData.radix 2963 (by
    unfold Bm2963MaskData.radix
    exact Nat.pow_pos (by decide))]
  unfold Bm2963MaskData.radix Bm2963MaskData.width
  rw [Nat.cast_pow,Nat.cast_ofNat,←pow_mul,exp_nat_cast]

theorem current_beta_exp :
    (Bm2963MaskData.beta:V)=Exp.exp (Bm2963MaskData.width:V)-1 := by
  rw [←current_beta_exp_add_one (V:=V)]
  simp

theorem current_width : (Bm2963MaskData.width:V)=139261 ∧
    (2:V)≤(Bm2963MaskData.width:V) := by
  constructor <;> norm_num [Bm2963MaskData.width]

private theorem power_of_equations (v : Fin 14 → V) (hv : ∀j,0<v j)
    (he : Equations (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V)
      (Bm2963MaskData.lowPort:V) ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V) v) :
    X v=Exp.exp (rank v) ∧ Exponential (rank v) (X v) ∧ Exp.exp (rank v)<Y v := by
  obtain ⟨hb,hl,hh⟩:=current_bounds (V:=V)
  obtain ⟨ht,hn,hm,hf,hu⟩:=he
  exact ArithmeticPellPowerRecovery.maintained_power
    (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V) (Bm2963MaskData.lowPort:V)
    ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) hb hl hh
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9)
    (hv 10) (hv 11) (hv 12) (hv 13) ht hn hm hf hu

/-- Only positivity and this actual maintained split zero are premises. -/
theorem current_power (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    X v=Exp.exp (rank v) ∧ Exponential (rank v) (X v) ∧ Exp.exp (rank v)<Y v :=
  power_of_equations v hv (current_equations v hv hz)

/-- L is not the existing coordinate v9. The residual exponent may be zero. -/
def Radix (v : Fin 14 → V) : Prop :=
  ∃ L : V, 0<L ∧ q v=Exp.exp ((Bm2963MaskData.width:V)*L) ∧
    (Bm2963MaskData.width:V)*L≤rank v ∧
    v 8=Exp.exp (rank v-(Bm2963MaskData.width:V)*L) ∧
    Exponential ((Bm2963MaskData.width:V)*L) (q v) ∧
    Exponential (rank v-(Bm2963MaskData.width:V)*L) (v 8)

/-- The radix alignment from the recovered power alone (public: the 94/67 chain reuses it). -/
theorem radix_of_power (v : Fin 14 → V) (hJ : 0<v 0)
    (hp : X v=Exp.exp (rank v)) : Radix v := by
  have he : Exp.exp (rank v)=v 8*((Exp.exp (Bm2963MaskData.width:V)-1)*v 0+1) := by
    simpa only [X, q, current_beta_exp (V:=V)] using hp.symm
  obtain ⟨_,L,hL,hq,hbound,hw⟩:=ArithmeticRadixAlignment.factor_alignment
    (Bm2963MaskData.width:V) (v 0) (rank v) (v 8) (current_width (V:=V)).2 hJ he
  have hq' : q v=Exp.exp ((Bm2963MaskData.width:V)*L) := by
    simpa only [q,current_beta_exp (V:=V)] using hq
  exact ⟨L,hL,hq',hbound,hw,by rw [hq']; exact exponential_exp _,
    by rw [hw]; exact exponential_exp _⟩

/-- The literal zero itself supplies every power and radix hypothesis. -/
theorem current_radix (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    (X v=Exp.exp (rank v) ∧ Exponential (rank v) (X v) ∧ Exp.exp (rank v)<Y v) ∧
      Radix v := by
  have hp:=current_power v hv hz
  exact ⟨hp,radix_of_power v (hv 0) hp.1⟩

/-- Public natural-zero clients reuse the accepted single-shift binding. -/
theorem current_natural_power (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v=
      naturalExpression.splitNatural.2.evalSemiring v) :
    let u:=fun j => v j+1
    X u=Exp.exp (rank u) ∧ Exponential (rank u) (X u) ∧ Exp.exp (rank u)<Y u :=
  current_power _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)

theorem current_natural_radix (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v=
      naturalExpression.splitNatural.2.evalSemiring v) :
    let u:=fun j => v j+1
    (X u=Exp.exp (rank u) ∧ Exponential (rank u) (X u) ∧ Exp.exp (rank u)<Y u) ∧
      Radix u :=
  current_radix _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)

end Bm2963CarrierRadix

#print axioms Bm2963CarrierRadix.current_beta_exp
#print axioms Bm2963CarrierRadix.current_width
#print axioms Bm2963CarrierRadix.radix_of_power
#print axioms Bm2963CarrierRadix.current_power
#print axioms Bm2963CarrierRadix.current_radix
#print axioms Bm2963CarrierRadix.current_natural_power
#print axioms Bm2963CarrierRadix.current_natural_radix
