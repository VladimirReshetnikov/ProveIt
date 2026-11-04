import DiophantineConsistency.Compact44.CompactHeterogeneousCarry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCarryReset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.CompactHeterogeneousCarry
open DiophantineConsistency.ArithmeticCyclicWord
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {ι : Type*} [Fintype ι]
variable {w n F b : V} {D a X : ι → V}

/-- A target following a column with enough spare capacity has zero
    carry entering it, even with a nonzero global cyclic carry bound. -/
theorem clean_after_bounded_predecessor
    (h : CarryInput w n F b D a X) {k s t half : V} (hk : k < n)
    (hpred : raw w a X (cyc n k 1) ≤ s + t)
    (ht : t ≤ half) (hroom : s + b < half)
    (hbase : half + half = Exp.exp w) :
    carry w n a X (cyc n k 1) = 0 ∧
      dig w F k = raw w a X k % Exp.exp w := by
  let j : V := cyc n k 1
  have hj : j < n := cyc_lt h.n_pos k 1
  have hprev : carry w n a X (cyc n j 1) ≤ b := carry_le h (cyc_lt h.n_pos j 1)
  have hsmall : raw w a X j + carry w n a X (cyc n j 1) < Exp.exp w := by
    calc
      raw w a X j + carry w n a X (cyc n j 1) ≤ (s+t)+b := add_le_add hpred hprev
      _ = (s+b)+t := by ring
      _ < half+half := add_lt_add_of_lt_of_le hroom ht
      _ = Exp.exp w := hbase
  have hzero : carry w n a X j = 0 := by
    rw [(carry_column h hj).1, div_eq_zero_of_lt _ hsmall]
  have hd := (carry_column h hk).2
  rw [hzero, add_zero] at hd
  exact ⟨hzero, hd⟩
/-- If the target column itself is also below the radix, its output digit
    is the unmodified column sum. -/
theorem digit_after_bounded_predecessor
    (h : CarryInput w n F b D a X) {k s t half : V} (hk : k < n)
    (hpred : raw w a X (cyc n k 1) ≤ s + t)
    (ht : t ≤ half) (hroom : s + b < half)
    (hbase : half + half = Exp.exp w) (htarget : raw w a X k < Exp.exp w) :
    carry w n a X (cyc n k 1) = 0 ∧ dig w F k = raw w a X k := by
  obtain ⟨hc,hd⟩ := clean_after_bounded_predecessor h hk hpred ht hroom hbase
  exact ⟨hc, hd.trans (mod_eq_self_of_lt htarget)⟩
end CompactCarryReset
#print axioms CompactCarryReset.digit_after_bounded_predecessor
#print axioms CompactCarryReset.clean_after_bounded_predecessor
