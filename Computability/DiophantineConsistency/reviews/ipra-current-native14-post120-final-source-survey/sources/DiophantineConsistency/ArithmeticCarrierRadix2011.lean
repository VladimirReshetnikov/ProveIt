import DiophantineConsistency.ArithmeticCarrierSoundness2011
import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticRadixAlignment

/-! The same actual maintained zero gives its represented power and radix.
The recovered block count is independent of the first-norm quotient coordinate.
No source, port, norm, index or power premise is supplied by the public clients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCarrierRadix2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (v : Fin 14 → V) : V := (CurrentMasks2011.beta:V)*v 0+1
def X (v : Fin 14 → V) : V := v 8*q v
def Y (v : Fin 14 → V) : V := v 7*(q v)^3
def rank (v : Fin 14 → V) : V :=
  ((q v-1)*(q v-v 1)+v 2)*((q v)^2-1)+
    ((CurrentMasks2011.lowPort:V)+q v*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*v 0

/-- This induction concerns only a standard numeral parameter. Internal
exponents in every subsequent client remain arbitrary model elements. -/
theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

private theorem cast_pred_power (r n : ℕ) (hr : 0<r) :
    ((r^n-1:ℕ):V)+1=(r:V)^n := by
  have h : (r^n-1)+1=r^n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.pow_pos hr)))
  exact_mod_cast h

/-- The enormous fixed coefficient is related symbolically to its width. -/
theorem current_beta_exp_add_one :
    (CurrentMasks2011.beta:V)+1=Exp.exp (CurrentMasks2011.width:V) := by
  unfold CurrentMasks2011.beta
  rw [cast_pred_power CurrentMasks2011.radix 2011 (by
    unfold CurrentMasks2011.radix
    exact Nat.pow_pos (by decide))]
  unfold CurrentMasks2011.radix CurrentMasks2011.width
  rw [Nat.cast_pow,Nat.cast_ofNat,←pow_mul,exp_nat_cast]

theorem current_beta_exp :
    (CurrentMasks2011.beta:V)=Exp.exp (CurrentMasks2011.width:V)-1 := by
  rw [←current_beta_exp_add_one (V:=V)]
  simp

theorem current_width : (CurrentMasks2011.width:V)=94517 ∧
    (2:V)≤(CurrentMasks2011.width:V) := by
  constructor <;> norm_num [CurrentMasks2011.width]

private theorem power_of_equations (v : Fin 14 → V) (hv : ∀j,0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v) :
    X v=Exp.exp (rank v) ∧ Exponential (rank v) (X v) ∧ Exp.exp (rank v)<Y v := by
  obtain ⟨hb,hl,hh⟩:=current_bounds (V:=V)
  obtain ⟨ht,hn,hm,hf,hu⟩:=he
  exact ArithmeticPellPowerRecovery.maintained_power
    (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
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
  ∃ L : V, 0<L ∧ q v=Exp.exp ((CurrentMasks2011.width:V)*L) ∧
    (CurrentMasks2011.width:V)*L≤rank v ∧
    v 8=Exp.exp (rank v-(CurrentMasks2011.width:V)*L) ∧
    Exponential ((CurrentMasks2011.width:V)*L) (q v) ∧
    Exponential (rank v-(CurrentMasks2011.width:V)*L) (v 8)

private theorem radix_of_power (v : Fin 14 → V) (hJ : 0<v 0)
    (hp : X v=Exp.exp (rank v)) : Radix v := by
  have he : Exp.exp (rank v)=v 8*((Exp.exp (CurrentMasks2011.width:V)-1)*v 0+1) := by
    simpa only [X, q, current_beta_exp (V:=V)] using hp.symm
  obtain ⟨_,L,hL,hq,hbound,hw⟩:=ArithmeticRadixAlignment.factor_alignment
    (CurrentMasks2011.width:V) (v 0) (rank v) (v 8) (current_width (V:=V)).2 hJ he
  have hq' : q v=Exp.exp ((CurrentMasks2011.width:V)*L) := by
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

end DiophantineConsistency.ArithmeticCarrierRadix2011
