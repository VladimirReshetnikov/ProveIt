import CompactGenericStride
import CompactPositiveTransport

/-! Calibration of the same compact rank implies positive shifted transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCalibratedTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPacking CompactConstructedRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem calibrated_transport {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 590069 K low high N s X) (hs0 : 0<s) (hsN : s<N)
    (hcal : rank K N s X % (590069*N) = (590069*s) % (590069*N)) :
    let R := rank K N s X
    let q := Exp.exp ((590069:V)*N)
    let w := Exp.exp (R-590069*N)
    let C := Cw 590069 N X
    let F := Fw 590069 K N s X
    ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧ (K+w)*C=F+z*(q-1) := by
  have hbig := (CompactRankResidueJoin.properties h).2.2
  have hstride := CompactGenericStride.stride (590069:V) N s (rank K N s X)
    (by norm_num) hs0 hsN hcal hbig
  exact CompactPositiveTransport.positive_shifted_transport h hbig hstride.2.2.2.2

#print axioms CompactCalibratedTransport.calibrated_transport
end CompactCalibratedTransport
