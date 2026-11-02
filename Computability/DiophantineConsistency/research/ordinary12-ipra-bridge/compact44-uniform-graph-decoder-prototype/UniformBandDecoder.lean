import DiophantineConsistency.UniformBandInputs
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace UniformBandDecoder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticBinaryCarry CompactSymbolicKernel CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def copyWord (n C k : V) (T : ℕ) : V :=
  ∑ j : Fin 41, (2:V)^j.val*copyDigit position n C k T j

def Conclusion (n C k : V) (T : ℕ) : Prop :=
  ((∀ j : Fin 943, selectorDigit n C k T j=0) ∧ copyWord n C k T=0) ∨
  ∃ j : Fin 943, CompactSelectorSum.Selected (selectorDigit n C k T) j ∧
    copyWord n C k T=Compact943Decoder.tileValue (V:=V) j

theorem decode (n C k : V) (T : ℕ) (hin : UniformBandInputs.Inputs n C k T)
    (hnc : NoCarry (FixedGraphRawBands.decoderBand position T n C k) (Exp.exp 51-2)) :
    Conclusion n C k T := by
  obtain ⟨hs,hc,hw⟩ := hin
  have hdecode := Compact943Decoder.decode_iff (selectorDigit n C k T) (copyWord n C k T) hs hw
  exact hdecode.mp hnc
#print axioms UniformBandDecoder.decode
end UniformBandDecoder
