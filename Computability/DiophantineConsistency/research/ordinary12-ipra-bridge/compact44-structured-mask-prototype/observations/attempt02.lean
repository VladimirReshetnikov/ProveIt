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

instance (support rho forbidden special : V) : 𝚺₁-Function₁ (maskDigit support rho forbidden special) := by
  unfold maskDigit
  definability

theorem maskDigit_lt (support j : V) : maskDigit support (Exp.exp 67) 1 1063 j < Exp.exp 67 := by
  unfold maskDigit
  split_ifs <;> exact tsub_lt_self (exp_pos _) (by norm_num)

theorem maskDigit_class (support j : V) :
    maskDigit support (Exp.exp 67) 1 1063 j = Exp.exp 67-1 ∨ maskDigit support (Exp.exp 67) 1 1063 j = Exp.exp 67-2 ∨
      maskDigit support (Exp.exp 67) 1 1063 j = Exp.exp 67-4 := by
  unfold maskDigit
  split_ifs <;> simp

theorem structured_block (support : V) :
    let block := bsum 67 (maskDigit support (Exp.exp 67) 1 1063) 8807
    block < Exp.exp (67*8807) ∧
    (∀ j < 8807, dig 67 block j = Exp.exp 67-1 ∨ dig 67 block j = Exp.exp 67-2 ∨
      dig 67 block j = Exp.exp 67-4) := by
  have hb := bsum_blocks (w := (67:V)) (f := maskDigit support (Exp.exp 67) 1 1063)
    (n := (8807:V)) (fun j _ => maskDigit_lt support j)
  refine ⟨hb.1, fun j hj => ?_⟩
  rw [hb.2 j hj]
  exact maskDigit_class support j

theorem structured_origin (support : V) (h0 : fbit support 0=1) :
    dig 67 (bsum 67 (maskDigit support (Exp.exp 67) 1 1063) 8807) 0 = Exp.exp 67-2 := by
  rw [dig_bsum (w := (67:V)) (f := maskDigit support (Exp.exp 67) 1 1063)
    (fun j _ => maskDigit_lt support j) (by norm_num : (0:V)<8807)]
  simp [maskDigit,h0]
end CompactStructuredMask
#print axioms CompactStructuredMask.structured_block
#print axioms CompactStructuredMask.structured_origin
