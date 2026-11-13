import DiophantineConsistency.FixedGraphLocalNoCarry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SelectedBandDecoder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticBinaryCarry CompactSymbolicKernel CompactPartialBand
open FixedGraphSelectedInputs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def copyWord (n C : V) (T : ℕ) : V :=
  ∑ j : Fin 41, (2:V)^j.val*copyDigit position n C (T:V) T j

def Conclusion (n C : V) (T : ℕ) : Prop :=
  ((∀ j : Fin 943, selectorDigit n C (T:V) T j=0) ∧ copyWord n C T=0) ∨
  ∃ j : Fin 943, CompactSelectorSum.Selected (selectorDigit n C (T:V) T) j ∧
    copyWord n C T=Compact943Decoder.tileValue (V:=V) j

theorem decode (n C : V) (T : ℕ) (hin : Inputs n C T)
    (hnc : NoCarry (FixedGraphRawBands.decoderBand position T n C (T:V)) (Exp.exp 51-2)) :
    Conclusion n C T := by
  obtain ⟨hs,hc,hw⟩ := hin
  have hdecode := Compact943Decoder.decode_iff (selectorDigit n C (T:V) T) (copyWord n C T) hs hw
  apply hdecode.mp
  exact hnc
#print axioms SelectedBandDecoder.decode
end SelectedBandDecoder
