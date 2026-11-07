import DiophantineConsistency.Source34.Source34Kernel
import DiophantineConsistency.Compact44.CompactListMask
import DiophantineConsistency.Compact44.CompactFixedBeta
import DiophantineConsistency.Compact44.CompactSymbolicPorts

/-! # The four ports of the source34 tuple

The ports of `source34_coefficients.md`, as symbolic natural numbers, in the
form of `Mixed121Ports`:

* `betaNat = 2^(121·8801) − 1`;
* `K = paramKernel rho` (`Source34Kernel`);
* `lowNat = MC`, the radix-`2^121` digit list
  `CompactListMask.digits (2^121) 8801 1063 (E ∖ {1})`, with the source34
  support `E`;
* `highNat = MF_native`, the explicit list `highDigits`, whose field targets
  are the parity-separated tracks `1000 + 2j` and `1021 + 2j`. The fourth port
  is `β + MF_native`, the source34 `MF`.

`research/source34-calibration/tools/check_ports.py` rebuilds `MC` and `MF`
from these lists and matches the source34 payloads byte for byte. That is a
finite check outside Lean. The leaf bounds are proved symbolically, as for
121x8801. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Ports
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The radix `B = 2^121`. -/
def radix : ℕ := 2^121

def betaNat : ℕ := 2^(121*8801) - 1

/-- The mask support `E ∖ {1}`. -/
def maskSupport : Finset ℕ := (Source34Kernel.support.filter (· ≠ 1)).toFinset

def lowNat : ℕ := Nat.ofDigits radix (CompactListMask.digits radix 8801 1063 maskSupport)

/-- `μ = 1022 + Σ_{j<44} W_j`, the clause-target digit of `MF_native`. -/
def mu : ℕ := 1022 + ∑ j ∈ Finset.range 44, Mixed121Kernel.W j
def padding : ℕ := 2^119 - 1
def lastPadding : ℕ := 2^27 - 1

/-- One parity-separated field track: twenty digits `1, 0, 1, 0, …`. -/
def track : List ℕ := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0]

/-- The low 8800 digits of `MF_native`: the tracks sit at `1000..1019` and
`1021..1040`. -/
def highInit : List ℕ :=
  [4] ++ List.replicate 999 0 ++ track ++ [0] ++ track ++ List.replicate 1154 0 ++ [1] ++
  List.replicate 1100 0 ++ [1] ++
  List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++
  List.replicate 3296 0 ++ List.replicate 7 padding ++ [lastPadding]

def highDigits : List ℕ := highInit ++ [0]
def highNat : ℕ := Nat.ofDigits radix highDigits

/-- The port tuple `β, K, MC, β + MF_native`. -/
def ports : Fin 4 → ℕ :=
  CompactSymbolicPorts.ports betaNat (Source34Kernel.paramKernel Mixed121Kernel.rho) lowNat highNat

theorem highInit_length : highInit.length = 8800 := by
  simp only [highInit, track, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]

theorem highDigits_length : highDigits.length = 8801 := by
  simp only [highDigits, List.length_append, highInit_length, List.length_cons, List.length_nil]

theorem mu_lt : mu < radix := by
  unfold mu radix
  have h : ∑ j ∈ Finset.range 44, Mixed121Kernel.W j < 2^99 := by
    unfold Mixed121Kernel.W
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  generalize ∑ j ∈ Finset.range 44, Mixed121Kernel.W j = S at h
  norm_num at h ⊢
  omega

theorem highInit_digit_lt (x : ℕ) (hx : x ∈ highInit) : x < radix := by
  have hmu := mu_lt
  have hp : padding < radix := by unfold padding radix; norm_num
  have hl : lastPadding < radix := by unfold lastPadding radix; norm_num
  have h1 : (1:ℕ) < radix := by unfold radix; norm_num
  have h4 : (4:ℕ) < radix := by unfold radix; norm_num
  have h0 : (0:ℕ) < radix := by unfold radix; norm_num
  revert x
  simp only [highInit, track, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_replicate, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    h4, h0, h1, hmu, hp, hl, or_true, and_self, true_and, and_true]

theorem radix_pow : radix^8801 = 2^(121*8801) := by unfold radix; rw [← pow_mul]

theorem one_lt_radix : 1 < radix := by unfold radix; norm_num

theorem high_lt : highNat < radix^8800 := by
  unfold highNat highDigits
  rw [Nat.ofDigits_append, highInit_length]
  simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero]
  have := Nat.ofDigits_lt_base_pow_length one_lt_radix highInit_digit_lt
  rwa [highInit_length] at this

theorem high_pos : 4 ≤ highNat := by
  unfold highNat highDigits highInit
  simp only [List.append_assoc, List.singleton_append, List.cons_append, Nat.ofDigits_cons,
    Nat.cast_id]
  generalize Nat.ofDigits radix _ = T
  omega

theorem beta_pos : 0 < betaNat := by
  unfold betaNat
  have : 2 ≤ 2^(121*8801) := Nat.le_self_pow (by norm_num) 2
  generalize 2^(121*8801) = Q at this ⊢
  omega

theorem beta_ge : 46 ≤ betaNat := by
  unfold betaNat
  have : 2^6 ≤ 2^(121*8801) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  generalize 2^(121*8801) = Q at this ⊢
  norm_num at this
  omega

theorem high_lt_beta : highNat < betaNat := by
  have h := high_lt
  have hp : radix^8800 < radix^8801 := Nat.pow_lt_pow_right one_lt_radix (by norm_num)
  have hr := radix_pow
  unfold betaNat
  generalize radix^8800 = A at h hp
  generalize radix^8801 = P at hp hr
  generalize 2^(121*8801) = Q at hr ⊢
  omega

theorem zero_mem_support : (0:ℕ) ∈ maskSupport := by
  unfold maskSupport
  rw [List.mem_toFinset, List.mem_filter]
  refine ⟨?_, by decide⟩
  unfold Source34Kernel.support
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_range.mpr (by norm_num)))

theorem low_lt_beta : lowNat < betaNat := by
  have h := CompactListMask.digits_add_defect radix 8801 1063 maskSupport
    (by unfold radix; norm_num)
  have hd : 1 ≤ ∑ j ∈ Finset.range 8801, CompactListMask.defect 1063 maskSupport j * radix^j := by
    have hmem : (0:ℕ) ∈ Finset.range 8801 := Finset.mem_range.mpr (by norm_num)
    have hle := Finset.single_le_sum (f := fun j => CompactListMask.defect 1063 maskSupport j * radix^j)
      (fun _ _ => Nat.zero_le _) hmem
    have h0 : CompactListMask.defect 1063 maskSupport 0 * radix^0 = 1 := by
      simp only [CompactListMask.defect, if_neg (by norm_num : (0:ℕ) ≠ 1063),
        if_pos zero_mem_support, pow_zero, mul_one]
    rw [h0] at hle
    exact hle
  have hr := radix_pow
  unfold lowNat betaNat
  generalize ∑ j ∈ Finset.range 8801, CompactListMask.defect 1063 maskSupport j * radix^j = D
    at h hd
  generalize Nat.ofDigits radix (CompactListMask.digits radix 8801 1063 maskSupport) = M at h ⊢
  generalize radix^8801 = P at h hr
  generalize 2^(121*8801) = Q at hr ⊢
  omega

/-! ## Model forms -/

attribute [local irreducible] betaNat lowNat highNat Source34Kernel.paramKernel
  Mixed121Kernel.rho

/-! The port projections are proved for arbitrary arguments. A concrete
`ports 3 = betaNat + highNat := rfl` makes the kernel's Nat-literal extension
evaluate both million-bit summands (`local irreducible` binds only the
elaborator), which ran for more than half an hour. -/
theorem ports_zero (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 0 = β := rfl
theorem ports_two (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 2 = L := rfl
theorem ports_three (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 3 = β + H := rfl

theorem beta_identity : (betaNat:V)+1 = Exp.exp ((121:V)*8801) := by
  have h := CompactFixedBeta.beta_identity_generic (V:=V) (121*8801)
  simpa only [betaNat, Nat.cast_mul, Nat.cast_ofNat] using h

theorem port_beta : ((ports 0 : ℕ) : V) = Exp.exp ((121:V)*8801) - 1 := by
  have h := beta_identity (V:=V)
  unfold ports
  rw [ports_zero, ← h, add_tsub_cancel_right]

/-- The port-bound hypotheses of the port-generic halting-chain leaves. -/
theorem leaf_bounds :
    0 < ((ports 0 : ℕ) : V) ∧ ((ports 2 : ℕ) : V) < ((ports 0 : ℕ) : V) ∧
      ((ports 3 : ℕ) : V) < 2*((ports 0 : ℕ) : V) ∧ (46:V) ≤ ((ports 0 : ℕ) : V) := by
  unfold ports
  rw [ports_zero, ports_two, ports_three]
  refine ⟨by exact_mod_cast beta_pos, by exact_mod_cast low_lt_beta, ?_, ?_⟩
  · have : betaNat + highNat < 2*betaNat := by have := high_lt_beta; omega
    exact_mod_cast this
  · exact_mod_cast beta_ge

theorem high_mul_pos (J : V) (hJ : 0 < J) : 1 ≤ (highNat:V)*J := by
  have h4 : (1:V) ≤ highNat := by
    have := high_pos; exact_mod_cast (le_trans (by norm_num) this)
  calc (1:V) = 1*1 := by rw [one_mul]
    _ ≤ (highNat:V)*J := mul_le_mul' h4 (pos_iff_one_le.mp hJ)
end Source34Ports
#print axioms Source34Ports.highDigits_length
#print axioms Source34Ports.high_lt
#print axioms Source34Ports.high_pos
#print axioms Source34Ports.low_lt_beta
#print axioms Source34Ports.high_lt_beta
#print axioms Source34Ports.beta_identity
#print axioms Source34Ports.port_beta
#print axioms Source34Ports.leaf_bounds
#print axioms Source34Ports.high_mul_pos
