import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! Private compatibility source for the newly public rank-window bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveTransport2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
private theorem power_left_step (r n : ℕ) : r*r^n=r^(n+1) := by
  rw [pow_succ,Nat.mul_comm]

private theorem two_power_bound (r n m : ℕ) (hr : 2≤r) (hn : n+1≤m) :
    2*r^n≤r^m := calc
  _≤r*r^n:=Nat.mul_le_mul_right _ hr
  _=r^(n+1):=power_left_step r n
  _≤r^m:=Nat.pow_le_pow_right (by omega) hn

private theorem pow_extends (r n : ℕ) (hn : n≠0) : r≤r^n := Nat.le_self_pow hn r

theorem current_bounds_nat :
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

end DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
