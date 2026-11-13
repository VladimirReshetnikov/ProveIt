import FirstQuotient87
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Source-only first-Pell index/residue extraction from an 87 own-zero.
No rank identification, other graph zero or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstIndex87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive q³ quotient and first-Pell index, with the two residue witnesses,
from the same 87 own-zero. No root sign is selected. -/
theorem index_residues (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hX : 0<v 6) (hY : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    let m := (v 6*v 7)*v 7
    ∃ s tau n r w : V, 0<s ∧ v 7=Q beta v*s ∧ 0<tau ∧
      n≤k v ∧ xcoord n (2*(m-1)+1)=tau ∧
      2*ycoord n (2*(m-1)+1)=k v ∧ tau=1+2*m*r ∧ k v=2*n+4*m*w := by
  let m := (v 6*v 7)*v 7
  obtain ⟨s,tau,hs,hYq,ht,hn⟩ :=
    FirstQuotient87Draft.quotient_and_root p beta v hbeta hJ hY hport hz
  have hm : 0<m := by dsimp [m]; exact mul_pos (mul_pos hX hY) hY
  have hm1 : 1≤m := pos_iff_one_le.mp hm
  have he : m-1+1=m := tsub_add_cancel_of_le hm1
  have hnorm : tau*tau=1+m*(m+1)*(k v)*(k v) := by
    rw [hn]
    dsimp [m,radicand,firstP,ell]
    ring
  have hd : ArithmeticPellFirstNorm.discriminant (m-1)=m*(m+1) := by
    unfold ArithmeticPellFirstNorm.discriminant
    rw [show m-1+2=(m-1+1)+1 by ring,he]
  have hdisc : tau*tau=1+ArithmeticPellFirstNorm.discriminant (m-1)*(k v)*(k v) := by
    rw [hd]
    exact hnorm
  obtain ⟨n,r,w,hnk,hx,hy,hr,hk⟩ := ArithmeticPellFirstNorm.solution_residues (m-1) tau (k v) hdisc
  have hr' : tau=1+2*m*r := by simpa only [he] using hr
  have hk' : k v=2*n+4*m*w := by simpa only [he] using hk
  exact ⟨s,tau,n,r,w,hs,hYq,ht,hnk,hx,hy,hr',hk'⟩

end DiophantineConsistency.FirstIndex87Draft

#print axioms DiophantineConsistency.FirstIndex87Draft.index_residues
