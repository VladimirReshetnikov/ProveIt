import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactTilePayload
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def value (w n e s : V) : V := w+256*n+131072*e+33554432*s+127*17179869184

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

/-- The 8,9,8,9-bit edge labels and seven fixed occupancy/anchor bits
produce a positive 41-bit compact44 payload in any arithmetic model. -/
theorem value_bounds (w n e s : V)
    (hw : w<256) (hn : n<512) (he : e<256) (hs : s<512) :
    0<value w n e s ∧ value w n e s<Exp.exp 41 := by
  have h17 : w+256*n<131072 := calc
    _<256+256*n := add_lt_add_of_lt_of_le hw le_rfl
    _=256*(n+1) := by ring
    _≤256*512 := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hn) (by simp)
    _=131072 := by norm_num
  have h25 : w+256*n+131072*e<33554432 := calc
    _<131072+131072*e := add_lt_add_of_lt_of_le h17 le_rfl
    _=131072*(e+1) := by ring
    _≤131072*256 := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp he) (by simp)
    _=33554432 := by norm_num
  have h34 : w+256*n+131072*e+33554432*s<17179869184 := calc
    _<33554432+33554432*s := add_lt_add_of_lt_of_le h25 le_rfl
    _=33554432*(s+1) := by ring
    _≤33554432*512 := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hs) (by simp)
    _=17179869184 := by norm_num
  have hexp : Exp.exp (41:V)=2199023255552 := by
    have he := exp_nat_cast (V:=V) 41
    norm_num only [Nat.cast_ofNat] at he
    rw [he]
  constructor
  · dsimp [value]
    exact add_pos_of_nonneg_of_pos (by simp) (by norm_num)
  · dsimp [value]
    rw [hexp]
    calc
      _<17179869184+127*17179869184 := add_lt_add_of_lt_of_le h34 le_rfl
      _=2199023255552 := by norm_num
end CompactTilePayload
#print axioms CompactTilePayload.value_bounds
