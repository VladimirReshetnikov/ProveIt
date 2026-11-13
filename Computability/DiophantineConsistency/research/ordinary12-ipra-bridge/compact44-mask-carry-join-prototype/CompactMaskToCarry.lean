import DiophantineConsistency.CompactScaledCarry
import DiophantineConsistency.CompactMaskSlot
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactMaskToCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.CompactScaledCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {ι : Type*} [Fintype ι]

theorem digit_le_three_of_mask (X M k : V) (h : NoCarry X M)
    (hm : dig 67 M k = Exp.exp 67 - 1 ∨
          dig 67 M k = Exp.exp 67 - 2 ∨
          dig 67 M k = Exp.exp 67 - 4) :
    dig 67 X k ≤ 3 := by
  rcases hm with h1 | h2 | h4
  · rw [CompactMaskSlot.forbidden_at X M k h h1]; norm_num
  · exact le_trans (CompactMaskSlot.ordinary_at X M k h h2) (by norm_num)
  · exact CompactMaskSlot.dummy_at X M k h h4

/-- Explicit all-position mask classification and no-carry premises supply the
D=3 input. The actual repeated compact44 mask is not identified here. -/
theorem carry_input_of_mask (n F b : V) (a X M : ι → V)
    (hn : 0 < n) (hmod : 0 < Exp.exp (67*n)-1)
    (hword : ∀ i, X i < Exp.exp (67*n))
    (hnocarry : ∀ i, NoCarry (X i) (M i))
    (hmasks : ∀ i, ∀ k < n, dig 67 (M i) k = Exp.exp 67 - 1 ∨
          dig 67 (M i) k = Exp.exp 67 - 2 ∨
          dig 67 (M i) k = Exp.exp 67 - 4)
    (hF : F < Exp.exp (67*n)-1)
    (hcongr : (∑ i, a i * X i) % (Exp.exp (67*n)-1) = F % (Exp.exp (67*n)-1))
    (hmass : (∑ i, a i) * 3 + 1 ≤ (b+1) * (Exp.exp 67 - 1)) :
    CarryInput 67 n F b 3 a X := by
  exact ⟨hn, hmod, hword, (fun i k hk => digit_le_three_of_mask (X i) (M i) k (hnocarry i) (hmasks i k hk)), hF, hcongr, hmass⟩
/-- A classified finite block stays classified at every position of its
model-length repetition. The block classification remains a hypothesis. -/
theorem repeated_mask_class (m block N k : V) (hm : 0 < m)
    (hblock : block < Exp.exp (67*m))
    (hclass : ∀ j < m, dig 67 block j = Exp.exp 67 - 1 ∨
        dig 67 block j = Exp.exp 67 - 2 ∨ dig 67 block j = Exp.exp 67 - 4)
    (hk : k < m*N) :
    dig 67 (block * ArithmeticRepunit.rep (67*m) N) k = Exp.exp 67 - 1 ∨
      dig 67 (block * ArithmeticRepunit.rep (67*m) N) k = Exp.exp 67 - 2 ∨
      dig 67 (block * ArithmeticRepunit.rep (67*m) N) k = Exp.exp 67 - 4 := by
  rw [dig_mul_rep 67 m block hblock N k hk]
  exact hclass (k % m) (mod_lt k hm)

/-- NoCarry against a repeated classified mask bounds all word digits by 3. -/
theorem repeated_mask_digit_le_three (X m block N k : V) (hm : 0 < m)
    (hblock : block < Exp.exp (67*m))
    (hclass : ∀ j < m, dig 67 block j = Exp.exp 67 - 1 ∨
        dig 67 block j = Exp.exp 67 - 2 ∨ dig 67 block j = Exp.exp 67 - 4)
    (hk : k < m*N) (hnc : NoCarry X (block * ArithmeticRepunit.rep (67*m) N)) :
    dig 67 X k ≤ 3 := by
  exact digit_le_three_of_mask X _ k hnc (repeated_mask_class m block N k hm hblock hclass hk)
end CompactMaskToCarry
#print axioms CompactMaskToCarry.repeated_mask_class
#print axioms CompactMaskToCarry.repeated_mask_digit_le_three
#print axioms CompactMaskToCarry.digit_le_three_of_mask
#print axioms CompactMaskToCarry.carry_input_of_mask
