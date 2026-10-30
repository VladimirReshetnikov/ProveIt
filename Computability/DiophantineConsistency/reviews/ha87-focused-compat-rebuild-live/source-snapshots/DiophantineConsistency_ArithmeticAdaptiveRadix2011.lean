import DiophantineConsistency.ArithmeticAdaptiveMersenne2011

/-! Recover the actual adaptive radix and its represented exponential graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRadix2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptivePowerProjection2011 ArithmeticAdaptivePowerFinish2011
open ArithmeticAdaptiveMersenne2011 ArithmeticRadixAlignment
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]
private theorem cast_pred_power (r n : ℕ) (hr : 0<r) :
    ((r^n-1:ℕ):V)+1=(r:V)^n := by
  have h : (r^n-1)+1=r^n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.pow_pos hr)))
  exact_mod_cast h
private theorem beta_exp_add_one :
    (CurrentMasks2011.beta:V)+1=Exp.exp (CurrentMasks2011.width:V) := by
  unfold CurrentMasks2011.beta
  rw [cast_pred_power CurrentMasks2011.radix 2011 (by
    unfold CurrentMasks2011.radix
    exact Nat.pow_pos (by decide))]
  unfold CurrentMasks2011.radix CurrentMasks2011.width
  rw [Nat.cast_pow,Nat.cast_ofNat,←pow_mul,exp_nat_cast]
private theorem beta_exp :
    (CurrentMasks2011.beta:V)=Exp.exp (CurrentMasks2011.width:V)-1 := by
  rw [←beta_exp_add_one (V:=V)]
  simp
private theorem width_ge_four : (4:V)≤(CurrentMasks2011.width:V) := by
  norm_num [CurrentMasks2011.width]

def Radix (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(CurrentMasks2011.beta:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+
    ((CurrentMasks2011.lowPort:V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*v 0
  ∃ N w : V, 0<N ∧ q=Exp.exp ((CurrentMasks2011.width:V)*N) ∧
    (CurrentMasks2011.width:V)*N≤R ∧ w=Exp.exp (R-(CurrentMasks2011.width:V)*N) ∧
    v 6=q*w ∧ Exponential ((CurrentMasks2011.width:V)*N) q ∧
    Exponential (R-(CurrentMasks2011.width:V)*N) w

theorem current_radix (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : Radix v := by
  let d : V := (CurrentMasks2011.width:V)
  let q : V := 1+v 0*(CurrentMasks2011.beta:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+
    ((CurrentMasks2011.lowPort:V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*v 0
  have hd : 4≤d := width_ge_four
  have hd2 : 2≤d := le_trans (by norm_num : (2:V)≤4) hd
  have hq : q=(Exp.exp d-1)*v 0+1 := by dsimp [q,d]; rw [←beta_exp]; ring
  have hX : v 6=Exp.exp R := by
    have h := current_power_finish v hv hz
    change v 6=Exp.exp R at h
    exact h
  have hq3 : q∣3*Exp.exp R := by
    have h := (current_projection v hv hz).1
    change (1+v 0*(currentPorts 0:V))∣3*v 6 at h
    rw [hX] at h
    simpa only [currentPorts,Matrix.cons_val_zero] using h
  have hdiv : q∣Exp.exp R := cancel_three d R q (v 0) hd hq hq3
  obtain ⟨w,hw⟩ := hdiv
  have hfact : Exp.exp R=w*((Exp.exp d-1)*v 0+1) := by rw [←hq,hw]; ring
  obtain ⟨_,N,hN,hqN,hNR,hwexp⟩ := factor_alignment d (v 0) R w hd2 (hv 0) hfact
  have hqn : q=Exp.exp (d*N) := hq.trans hqN
  have hXq : v 6=q*w := by rw [hX,hw]
  refine ⟨N,w,hN,hqn,hNR,hwexp,hXq,?_,?_⟩
  · change Exponential (d*N) q
    rw [hqn]; exact exponential_exp _
  · change Exponential (R-d*N) w
    rw [hwexp]; exact exponential_exp _

theorem current_natural_radix (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Radix (fun j => v j+1) :=
  current_radix _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveRadix2011
