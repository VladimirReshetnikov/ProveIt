import FirstIndex87
import Q4Rank87

/-! Source-only first-index congruence from the 87 own zero. No other graph
zero, rank-window removal, exact index or Lean elaboration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstIndexModQ487Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence ArithmeticAdaptiveFirstDivisibility2011
open NaturalRank84Draft FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- First Pell index congruence, retaining all quotient and Pell witnesses. -/
theorem first_index_mod_q4 (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    let qq := q beta v
    let R := naturalRank beta MC MF v
    let m := (v 6*v 7)*v 7
    ∃ s tau n r w : V, 0<s ∧ v 7=Q beta v*s ∧ 0<tau ∧
      n≤k v ∧ xcoord n (2*(m-1)+1)=tau ∧
      2*ycoord n (2*(m-1)+1)=k v ∧ tau=1+2*m*r ∧ k v=2*n+4*m*w ∧
      (2*n)%(qq^4)=(R+1)%(qq^4) := by
  let qq := q beta v
  let R := naturalRank beta MC MF v
  let m := (v 6*v 7)*v 7
  have hq : 0<qq := by dsimp [qq,q]; simp
  have hm : 0<qq^4 := pow_pos hq _
  obtain ⟨s,tau,n,r,w,hs,hY,ht,hn,hx,hy,hr,hk⟩ :=
    FirstIndex87Draft.index_residues p beta v hbeta (hv 0) (hv 6) (hv 7) hport hz
  have hmag : qq^4∣magnitude (R+1,k v) := by
    simpa only [qq,R] using
      Q4Rank87Draft.q4_rank p beta K MC MF v hbeta hport hK hMC hMF hv hz
  have hmod : (R+1)%(qq^4)=(k v)%(qq^4) := magnitude_mod (R+1,k v) (qq^4) hm hmag
  have hmultiple : qq^4∣4*m*w := by
    refine ⟨4*(v 6)*qq^2*(s*s)*w,?_⟩
    dsimp [m,qq]
    rw [hY]
    dsimp [Q]
    ring
  have hmod' : (R+1)%(qq^4)=(2*n)%(qq^4) := by
    rw [hk,add_comm (2*n) (4*m*w),mod_add_remove_left_of_dvd hmultiple hm] at hmod
    exact hmod
  exact ⟨s,tau,n,r,w,hs,hY,ht,hn,hx,hy,hr,hk,hmod'.symm⟩

end DiophantineConsistency.FirstIndexModQ487Draft

#print axioms DiophantineConsistency.FirstIndexModQ487Draft.first_index_mod_q4
