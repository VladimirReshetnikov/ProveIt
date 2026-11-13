import CompactFirstSeed
import CompactRankResidueJoin

/-! A positive shifted compact transport supplies the first-carrier seed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactFirstTransportSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPacking ArithmeticOuterSeed ArithmeticWindowDigits
open CompactConstructedRank CompactFirstSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_from_transport {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 590069 K low high N s X)
    (sY n eta zeta gamma w z : V) (hsY : 0<sY) (hz : 0<z)
    (hseed : SeedRelations (590069*N) (rank K N s X) sY n eta zeta gamma)
    (hqW : Exp.exp (590069*N)*w=Exp.exp (rank K N s X))
    (htransport : (K+w)*Cw 590069 N X = Fw 590069 K N s X+
      z*(Exp.exp (590069*N)-1)) :
    let q := Exp.exp ((590069:V)*N)
    let R := rank K N s X
    let Y := sY*q^3
    let E := Exp.exp R*Y
    let k := eta+zeta
    let ell := E*Y*k
    let tau := E*n+k-R
    let C := Cw 590069 N X
    let F := Fw 590069 K N s X
    (q*K+Exp.exp R)*C = q*F+(q-1)*(q*z) ∧
    ∃ r : V, 0<r ∧
      (q^3*(q-1))*(ell+k+r)+Y*(q-1) =
      (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*(q*z)) := by
  let u : V := 590069*N
  let q := Exp.exp u
  have hu2 : (2:V)≤u := le_trans (by dsimp [u]; norm_num)
    (le_mul_of_one_le_right (by norm_num) (pos_iff_one_le.mp (N_pos h)))
  have he2 : Exp.exp (2:V)=4 := by
    rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
    norm_num
  have hq4 : (4:V)≤q := by
    dsimp only [q]
    simpa only [he2] using (exp_monotone_le.mpr hu2)
  have hq : (2:V)≤q-1 := by
    apply le_tsub_of_add_le_left
    exact le_trans (by norm_num : (2:V)+1≤4) hq4
  have hb : (1:V)≤q*z := one_le_mul (one_le_exp _) (pos_iff_one_le.mp hz)
  have hphase := (CompactRankResidueJoin.properties h).2.1
  have hfirst := positive_first_of_seed u (rank K N s X) sY n eta zeta gamma (q*z)
    hsY hphase hq hb hseed
  constructor
  · calc
      (q*K+Exp.exp (rank K N s X))*Cw 590069 N X = q*((K+w)*Cw 590069 N X) := by rw [←hqW]; ring
      _=q*Fw 590069 K N s X+(q-1)*(q*z) := by rw [htransport]; ring
  · obtain ⟨r,hr,_,heq⟩ := hfirst
    exact ⟨r,hr,by simpa only [mul_assoc,mul_comm,mul_left_comm] using heq⟩

#print axioms CompactFirstTransportSeed.first_from_transport
end CompactFirstTransportSeed
