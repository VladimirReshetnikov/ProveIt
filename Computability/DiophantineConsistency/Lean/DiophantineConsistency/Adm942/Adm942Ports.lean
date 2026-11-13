import DiophantineConsistency.ArithmeticCarrierSoundness2011
import DiophantineConsistency.Adm942.Adm942Kernel

/-! # The four admissible942 ports and the maintained expression at them

The ports `β, K, MC, MF_source = MF_native + β` (`PROOF.md` §3), in the 2011
order and shape (`CurrentMasks2011.ports`, fourth port `highPort + beta`), as
symbolic natural numbers. The literal Carrier65 expression at these ports is
`ObjectCurrentEquation2011.expressionAt`, which is port-parametric; so the five
additive equations of a positive zero come from the port-generic
`ArithmeticCarrierSoundness2011.expressionAt_equations`, once the scalar port
bounds are proved here (the counterparts of `current_bounds`,
`current_equations`, `current_natural_equations`).

The million-bit numerals are never evaluated: the port projections are proved
for arbitrary arguments (`portsOf_*`), and the bounds are proved on atoms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942Ports
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 (Equations expressionAt_equations)
open ObjectCurrentEquation2011 (expressionAt positiveShift internalZero_positiveShift)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 2011 port shape, for arbitrary arguments. -/
def portsOf (β K L H : ℕ) : Fin 4 → ℕ := ![β, K, L, H + β]

theorem portsOf_zero (β K L H : ℕ) : portsOf β K L H 0 = β := rfl
theorem portsOf_one (β K L H : ℕ) : portsOf β K L H 1 = K := rfl
theorem portsOf_two (β K L H : ℕ) : portsOf β K L H 2 = L := rfl
theorem portsOf_three (β K L H : ℕ) : portsOf β K L H 3 = H + β := rfl

/-- The four actual admissible942 ports. -/
def ports : Fin 4 → ℕ :=
  portsOf Adm942MaskData.beta Adm942Kernel.K Adm942MaskData.lowPort Adm942MaskData.highPort

/-- The maintained literal expression at the admissible942 ports. -/
def expression : Expr (Fin 14) := expressionAt (fun j => ((ports j : ℕ) : ℤ))

def naturalExpression : Expr (Fin 14) := positiveShift expression

attribute [local irreducible] Adm942Kernel.K Adm942MaskData.radix Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort Adm942MaskData.highPrefix

theorem ports_zero : ports 0 = Adm942MaskData.beta := by
  unfold ports; exact portsOf_zero _ _ _ _
theorem ports_one : ports 1 = Adm942Kernel.K := by
  unfold ports; exact portsOf_one _ _ _ _
theorem ports_two : ports 2 = Adm942MaskData.lowPort := by
  unfold ports; exact portsOf_two _ _ _ _
theorem ports_three : ports 3 = Adm942MaskData.highPort + Adm942MaskData.beta := by
  unfold ports; exact portsOf_three _ _ _ _

private theorem two_power_bound (r n m : ℕ) (hr : 2≤r) (hn : n+1≤m) :
    2*r^n≤r^m := calc
  _≤r*r^n:=Nat.mul_le_mul_right _ hr
  _=r^(n+1):=by rw [pow_succ,Nat.mul_comm]
  _≤r^m:=Nat.pow_le_pow_right (by omega) hn

/-- `MF_native < ρ^4023`: its top four digits vanish. -/
theorem highPort_lt_pow : Adm942MaskData.highPort < Adm942MaskData.radix^4023 := by
  have hr1 : 1<Adm942MaskData.radix:=by unfold Adm942MaskData.radix; decide
  have hd : ∀x∈Adm942MaskData.highPrefix,x<Adm942MaskData.radix:=by
    intro x hx
    rw [Adm942MaskData.radix_eq]
    exact Adm942MaskData.highDigits_lt' (List.mem_append_left _ hx)
  unfold Adm942MaskData.highPort Adm942MaskData.highDigits
  rw [Nat.ofDigits_append_replicate_zero]
  simpa only [Adm942MaskData.highPrefix_length] using Nat.ofDigits_lt_base_pow_length hr1 hd

theorem current_bounds_nat :
    46≤Adm942MaskData.beta ∧ Adm942MaskData.lowPort<Adm942MaskData.beta ∧
      Adm942MaskData.highPort+Adm942MaskData.beta<2*Adm942MaskData.beta := by
  have hr : 64≤Adm942MaskData.radix:=by unfold Adm942MaskData.radix; decide
  have hp : Adm942MaskData.radix≤Adm942MaskData.radix^4027:=Nat.le_self_pow (by decide) _
  have hb : 46≤Adm942MaskData.beta:=by unfold Adm942MaskData.beta; omega
  have hz : 0∈Adm942MaskData.lowSupport:=(Adm942MaskData.mem_lowSupport 0).mpr (Or.inl (by decide))
  have hm : 1≤LowMaskCoding.supportValue Adm942MaskData.radix Adm942MaskData.lowSupport:=by
    simpa only [LowMaskCoding.supportValue,pow_zero] using
      Finset.single_le_sum (fun j _ => Nat.zero_le (_^j)) hz
  have hl : Adm942MaskData.lowPort<Adm942MaskData.beta:=by
    unfold Adm942MaskData.lowPort LowMaskCoding.mask
    rw [←Adm942MaskData.beta]
    simp only [show (2:ℕ)-1=1 by decide,one_mul]
    exact Nat.sub_lt (by omega : 0<Adm942MaskData.beta) (by omega)
  have hhigh := highPort_lt_pow
  have hpow : 2*Adm942MaskData.radix^4023≤Adm942MaskData.radix^4027:=
    two_power_bound _ _ _ (by omega) (by decide)
  have hh : Adm942MaskData.highPort<Adm942MaskData.beta:=by
    unfold Adm942MaskData.beta
    omega
  exact ⟨hb,hl,by omega⟩

/-- The actual fixed port inequalities, cast into every model of IΣ1. -/
theorem current_bounds :
    (15:V)≤(Adm942MaskData.beta:V) ∧
    (Adm942MaskData.lowPort:V)<(Adm942MaskData.beta:V) ∧
    ((Adm942MaskData.highPort+Adm942MaskData.beta:ℕ):V)<2*(Adm942MaskData.beta:V) := by
  obtain ⟨hb,hl,hh⟩:=current_bounds_nat
  exact ⟨by exact_mod_cast le_trans (by decide) hb,by exact_mod_cast hl,by exact_mod_cast hh⟩

/-- The port-bound hypotheses of the port-generic halting-chain leaves. -/
theorem leaf_bounds :
    0 < ((ports 0 : ℕ) : V) ∧ ((ports 2 : ℕ) : V) < ((ports 0 : ℕ) : V) ∧
      ((ports 3 : ℕ) : V) < 2*((ports 0 : ℕ) : V) ∧ (46:V) ≤ ((ports 0 : ℕ) : V) := by
  obtain ⟨hb,hl,hh⟩:=current_bounds_nat
  rw [ports_zero, ports_two, ports_three]
  exact ⟨by exact_mod_cast lt_of_lt_of_le (by decide) hb, by exact_mod_cast hl,
    by exact_mod_cast hh, by exact_mod_cast hb⟩

/-- No port, product, norm or transport oracle: only the actual positive zero. -/
theorem current_equations (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    Equations (Adm942MaskData.beta:V) (Adm942Kernel.K:V)
      (Adm942MaskData.lowPort:V) ((Adm942MaskData.highPort+Adm942MaskData.beta:ℕ):V) v := by
  obtain ⟨hb,hl,hh⟩:=current_bounds (V:=V)
  have h:=expressionAt_equations ports v
    (by rw [ports_zero]; exact lt_of_lt_of_le (by simp) hb)
    (by rw [ports_zero, ports_two]; exact hl)
    (by rw [ports_zero, ports_three]; exact hh) hv hz
  rwa [ports_zero, ports_one, ports_two, ports_three] at h

/-- The maintained natural expression performs exactly one positive shift. -/
theorem current_natural_equations (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v=
      naturalExpression.splitNatural.2.evalSemiring v) :
    Equations (Adm942MaskData.beta:V) (Adm942Kernel.K:V)
      (Adm942MaskData.lowPort:V) ((Adm942MaskData.highPort+Adm942MaskData.beta:ℕ):V)
      (fun j => v j+1) := by
  apply current_equations _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
  exact (internalZero_positiveShift expression v).mp hz

/-- A positive zero of the admissible942 expression. -/
def PositiveZero (u : Fin 14 → V) : Prop :=
  (∀ j, 0 < u j) ∧
    expression.splitNatural.1.evalSemiring u = expression.splitNatural.2.evalSemiring u

/-- A natural zero at `v` is exactly a zero of the original polynomial at `v+1`. -/
theorem natural_zero_iff (v : Fin 14 → V) :
    naturalExpression.splitNatural.1.evalSemiring v =
        naturalExpression.splitNatural.2.evalSemiring v ↔
      expression.splitNatural.1.evalSemiring (fun j => v j + 1) =
        expression.splitNatural.2.evalSemiring (fun j => v j + 1) := by
  unfold naturalExpression
  exact internalZero_positiveShift expression v

end Adm942Ports

#print axioms Adm942Ports.highPort_lt_pow
#print axioms Adm942Ports.current_bounds_nat
#print axioms Adm942Ports.current_bounds
#print axioms Adm942Ports.leaf_bounds
#print axioms Adm942Ports.current_equations
#print axioms Adm942Ports.current_natural_equations
#print axioms Adm942Ports.natural_zero_iff
