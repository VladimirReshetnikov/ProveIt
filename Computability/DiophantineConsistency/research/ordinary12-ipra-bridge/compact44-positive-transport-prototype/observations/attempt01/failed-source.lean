import CompactRankResidueJoin

/-! Shift the generic packing transport quotient and prove it is positive. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPositiveTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPacking
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Calibration remains explicit: the chosen power must have the packing
    rotation residue. The rank lower bound makes the shifted quotient positive. -/
theorem positive_shifted_transport {K N s R : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 590069 K CompactConstructedRank.low CompactConstructedRank.high N s X)
    (hbig : 2*(590069*N)<R)
    (hmod : Exp.exp (R-590069*N) % (Exp.exp (590069*N)-1) =
      Exp.exp (590069*s) % (Exp.exp (590069*N)-1)) :
    let u := (590069:V)*N
    let q := Exp.exp u
    let w := Exp.exp (R-u)
    let C := Cw 590069 N X
    let F := Fw 590069 K N s X
    ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧ (K+w)*C=F+z*(q-1) := by
  let u : V := 590069*N
  let q := Exp.exp u
  let w := Exp.exp (R-u)
  let C := Cw 590069 N X
  let F := Fw 590069 K N s X
  have huR : u≤R := le_of_lt (lt_of_le_of_lt
    (show u≤2*u by simpa only [two_mul] using le_add_of_nonneg_right (Arithmetic.zero_le u)) hbig)
  have hsub : u+(R-u)=R := add_tsub_cancel_of_le huR
  have hlt : u<R-u := by
    apply lt_of_add_lt_add_left (a := u)
    rw [hsub]
    simpa only [two_mul] using hbig
  have hqw : q*w=Exp.exp R := by
    dsimp only [q,w]
    rw [←exp_add,hsub]
  have hwq : q<w := exp_monotone_lt.mpr hlt
  have hq1 : q-1+1=q := tsub_add_cancel_of_le (one_le_exp _)
  have hC : 0<C := C_pos h
  have hF : F<q := lt_of_lt_of_le (F_lt_M h) tsub_le_self
  have hWle : w≤(K+w)*C := le_trans (le_add_of_nonneg_left (Arithmetic.zero_le K))
    (le_mul_of_one_le_right (Arithmetic.zero_le (K+w)) (pos_iff_one_le.mp hC))
  have hCF : F<(K+w)*C := lt_of_lt_of_le (lt_trans hF hwq) hWle
  have htr := packing_transport h w hmod
  let z := (K+w)*C/(q-1)
  have heq : (K+w)*C+q=(z+1)*(q-1)+1+F := calc
    _=((K+w)*C+(q-F))+F := by rw [add_assoc,add_tsub_cancel_of_le (le_of_lt hF)]
    _=(z+1)*(q-1)+1+F := by
      rw [htr]
      rfl
  have heq' : (K+w)*C+q=(F+z*(q-1))+q := calc
    _=(z+1)*(q-1)+1+F := heq
    _=(F+z*(q-1))+q := by rw [←hq1]; ring
  have hshift : (K+w)*C=F+z*(q-1) := add_right_cancel heq'
  have hz : 0<z := by
    rcases zero_or_succ z with hz | ⟨t,ht⟩
    · rw [hz] at hshift
      simp at hshift
      exact (ne_of_gt hCF) hshift.symm
    · rw [ht]
      exact lt_of_le_of_lt (Arithmetic.zero_le t) (lt_add_one t)
  exact ⟨z,hz,hqw,hshift⟩

#print axioms CompactPositiveTransport.positive_shifted_transport
end CompactPositiveTransport
