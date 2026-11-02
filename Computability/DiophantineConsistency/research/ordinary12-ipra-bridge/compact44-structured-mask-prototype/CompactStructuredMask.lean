import DiophantineConsistency.ArithmeticPackingBlocks
import DiophantineConsistency.ArithmeticBinaryPopulation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactStructuredMask
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPackingBlocks ArithmeticWindowDigits ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Digit recipe with forbidden slot 1 and 2-bit dummy slot 1063. The support
bitset is a parameter; its equality to the retained compact44 support is not
assumed or established here. -/
def maskDigit (support rho forbidden special j : V) : V :=
  if j=special then rho-4 else
  if j=forbidden then rho-1 else
  if fbit support j=1 then rho-2 else rho-1

theorem maskDigit_lt (support j : V) : maskDigit support (Exp.exp 67) 1 1063 j < Exp.exp 67 := by
  unfold maskDigit
  split_ifs <;> exact tsub_lt_self (exp_pos _) (by norm_num)

theorem maskDigit_class (support j : V) :
    maskDigit support (Exp.exp 67) 1 1063 j = Exp.exp 67-1 ∨ maskDigit support (Exp.exp 67) 1 1063 j = Exp.exp 67-2 ∨
      maskDigit support (Exp.exp 67) 1 1063 j = Exp.exp 67-4 := by
  unfold maskDigit
  split_ifs <;> simp

/-- External induction on a standard natural length constructs model blocks
without requiring an internal definability instance for the digit family. -/
theorem standard_blocks_exists (w : V) (f : V → V) (hf : ∀ j, f j < Exp.exp w)
    (n : ℕ) : ∃ Y, Blocks w f (n:V) Y := by
  induction n with
  | zero => exact ⟨0, by simpa using blocks_zero w f⟩
  | succ n ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨Y + f (n:V) * Exp.exp (w*(n:V)), ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using blocks_succ hY (hf (n:V))

/-- Exact per-position recipe for the structured block; the support word is a
parameter and the block is not identified with the retained MC port. -/
theorem structured_exact_block (support : V) :
    ∃ block, Blocks 67 (maskDigit support (Exp.exp 67) 1 1063) (8807:V) block :=
  standard_blocks_exists 67 (maskDigit support (Exp.exp 67) 1 1063)
    (maskDigit_lt support) 8807

/-- A structured block exists for each model support word. This theorem does
not identify it with the retained compact44 MC constant. -/
theorem structured_block (support : V) (h0 : fbit support 0=1) :
    ∃ block : V, block < Exp.exp (67*8807) ∧
    (∀ j : V, j < 8807 → dig 67 block j = Exp.exp 67-1 ∨ dig 67 block j = Exp.exp 67-2 ∨
      dig 67 block j = Exp.exp 67-4) ∧ dig 67 block 0 = Exp.exp 67-2 := by
  obtain ⟨block,hb⟩ := standard_blocks_exists (67:V)
    (maskDigit support (Exp.exp 67) 1 1063) (maskDigit_lt support) 8807
  refine ⟨block,hb.1,?_,?_⟩
  · intro j hj
    rw [hb.2 j hj]
    exact maskDigit_class support j
  · rw [hb.2 0 (by norm_num : (0:V)<8807)]
    simp [maskDigit,h0]
end CompactStructuredMask
#print axioms CompactStructuredMask.structured_exact_block
#print axioms CompactStructuredMask.standard_blocks_exists
#print axioms CompactStructuredMask.structured_block
