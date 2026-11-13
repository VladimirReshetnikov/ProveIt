import DirectBFSActivePhasePacking
import DirectBFSWordFieldHigh
import DirectBFSMarkedTarget
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSWordPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPacking ArithmeticBinaryCarry ArithmeticWindowDigits
open DirectBFSConstructedWord DirectBFSFourFieldsPacking
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pack_word {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] {N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (h0 : dummy 0%2=0)
    (hN : 1<N) (hs : 0<s) (hsN : s<N)
    (hMC : (CompactConcreteIncrement.mask:V)+1<Exp.exp 590069)
    (hHPpos : 1≤(CompactSymbolicPorts.highNat:V)) (hHPlt : (CompactSymbolicPorts.highNat:V)<Exp.exp 590069) :
    PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V) N s (cellWord row dummy) := by
  apply DirectBFSActivePhasePacking.pack_from_active hw h0 hN hs hsN hMC hHPpos hHPlt
  intro j hj p _ hp
  rcases hp with hv | hh | h2195 | h3296 | h4393 | h5495
  · exact DirectBFSWordFieldHigh.vertical_fields row dummy hw hN hsN hj hv.1 hv.2
  · exact DirectBFSWordFieldHigh.horizontal_fields row dummy hw hN hsN hj hh.1 hh.2
  · subst p; exact DirectBFSWordAnchorHigh.phase2195_noCarry row dummy hw hN hsN hj
  · subst p; exact DirectBFSWordAnchorHigh.phase3296_noCarry row dummy hw hN hsN hj
  · subst p; exact (DirectBFSMarkedTarget.marked_targets_noCarry row dummy hw hN hsN j hj).1
  · subst p; exact (DirectBFSMarkedTarget.marked_targets_noCarry row dummy hw hN hsN j hj).2
#print axioms DirectBFSWordPacking.pack_word
end DirectBFSWordPacking
