import DiophantineConsistency.AdaptiveDirectOrdinate86Forward

/-! Fixed-port 86-zero to 87-zero direction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Forward
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem power_left_step (r n : ℕ) : r*r^n=r^(n+1) := by
  rw [pow_succ,Nat.mul_comm]

private theorem two_power_bound (r n m : ℕ) (hr : 2≤r) (hn : n+1≤m) :
    2*r^n≤r^m := calc
  _≤r*r^n:=Nat.mul_le_mul_right _ hr
  _=r^(n+1):=power_left_step r n
  _≤r^m:=Nat.pow_le_pow_right (by omega) hn

private theorem pow_extends (r n : ℕ) (hn : n≠0) : r≤r^n := Nat.le_self_pow hn r

private theorem current_bounds_nat :
    15≤CurrentMasks2011.beta ∧ CurrentMasks2011.lowPort<CurrentMasks2011.beta ∧
      CurrentMasks2011.highPort+CurrentMasks2011.beta<2*CurrentMasks2011.beta := by
  have hr : 16≤CurrentMasks2011.radix:=by unfold CurrentMasks2011.radix; decide
  have hr1 : 1<CurrentMasks2011.radix:=by omega
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011:=
    pow_extends _ _ (by decide)
  have hb : 15≤CurrentMasks2011.beta:=by unfold CurrentMasks2011.beta; omega
  have hz : 0∈CurrentMasks2011.lowSupport:=by
    rw [CurrentMasks2011.lowSupport_def]
    simp
  have hm : 1≤LowMaskCoding.supportValue CurrentMasks2011.radix CurrentMasks2011.lowSupport:=by
    simpa only [LowMaskCoding.supportValue,pow_zero] using Finset.single_le_sum (fun j _ => Nat.zero_le (_^j)) hz
  have hl : CurrentMasks2011.lowPort<CurrentMasks2011.beta:=by
    unfold CurrentMasks2011.lowPort LowMaskCoding.mask
    rw [←CurrentMasks2011.beta]
    simp only [show (2:ℕ)-1=1 by decide,one_mul]
    exact Nat.sub_lt (by omega : 0<CurrentMasks2011.beta) (by omega : 0<LowMaskCoding.supportValue CurrentMasks2011.radix CurrentMasks2011.lowSupport)
  have hlen : CurrentMasks2011.highPrefix.length=1006:=by
    simp only [CurrentMasks2011.highPrefix,List.length_cons,List.length_append,List.length_replicate,List.length_nil]
  have hd : ∀x∈CurrentMasks2011.highPrefix,x<CurrentMasks2011.radix:=by
    intro x hx
    simp only [CurrentMasks2011.highPrefix,List.mem_cons,List.mem_append,List.mem_replicate,
      List.not_mem_nil,or_false] at hx
    norm_num [CurrentMasks2011.radix] at hx ⊢
    omega
  have hhigh : CurrentMasks2011.highPort<CurrentMasks2011.radix^1006:=by
    unfold CurrentMasks2011.highPort CurrentMasks2011.highDigits
    rw [Nat.ofDigits_append_replicate_zero]
    simpa only [hlen] using Nat.ofDigits_lt_base_pow_length hr1 hd
  have hpow : 2*CurrentMasks2011.radix^1006≤CurrentMasks2011.radix^2011:=
    two_power_bound _ _ _ (by omega) (by decide)
  have hpowpos : 0<CurrentMasks2011.radix^1006:=pow_pos (by omega) _
  have hh : CurrentMasks2011.highPort<CurrentMasks2011.beta:=by
    unfold CurrentMasks2011.beta
    omega
  exact ⟨hb,hl,by omega⟩

theorem fixed_port_bounds : 0<(currentPorts 0:V) ∧
    (currentPorts 2:V)<(currentPorts 0:V) ∧
    (currentPorts 3:V)<2*(currentPorts 0:V) := by
  obtain ⟨hb,hl,hh⟩ := current_bounds_nat
  have hb' : 0<currentPorts 0 := by
    simpa only [currentPorts,Matrix.cons_val_zero] using (show 0<CurrentMasks2011.beta by omega)
  have hl' : currentPorts 2<currentPorts 0 := by
    change CurrentMasks2011.lowPort<CurrentMasks2011.beta
    exact hl
  have hh' : currentPorts 3<2*currentPorts 0 := by
    change CurrentMasks2011.highPort+CurrentMasks2011.beta<2*CurrentMasks2011.beta
    exact hh
  exact ⟨by exact_mod_cast hb',by exact_mod_cast hl',by exact_mod_cast hh'⟩

theorem current_86_zero_to_87_zero (v : Fin 13 → V)
    (hz : InternalZero naturalExpression86 v) :
    ∃ w : Fin 13 → V, InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 w := by
  let v14 : Fin 14 → V := fun i => if h : i.val<13 then v ⟨i.val,h⟩+1 else 0
  have he : (fun i : Fin 13 => v14 (embed i)) = (fun i => v i+1) := by
    funext i
    simp [v14,embed]
  have hv : ∀i : Fin 13,0<v14 (embed i) := by
    intro i
    rw [show v14 (embed i)=v i+1 by simpa only using congrFun he i]
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (expressionAt86 (fun j => (currentPorts j:ℤ))) (fun i => v14 (embed i)) := by
    rw [currentPorts_cast,he]
    exact (internalZero_positiveShift expression86 v).mp hz
  obtain ⟨hb,hl,hh⟩ := fixed_port_bounds (V:=V)
  obtain ⟨w,hw⟩ := new_positive_zero_to_old_natural86 currentPorts v14 hb hl hh hv hz'
  refine ⟨w,?_⟩
  rw [currentPorts_cast] at hw
  exact hw
end DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
