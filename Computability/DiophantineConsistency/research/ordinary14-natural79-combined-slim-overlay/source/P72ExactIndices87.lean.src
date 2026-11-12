import P72FirstInputs87
import MainIndex87
import StrongNorm87
import AuxNorm87
import DiophantineConsistency.Compact44.P72Exact

/-! Source-only P72 exact-index composition from the 87 own zero; imports are
unelaborated. No provider closure, Lean or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P72ExactIndices87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence ArithmeticPellHalfIndex NaturalRank84Draft
open FirstFields86Draft StrongNorm87Draft MainBalance87Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed P72 exact-index application, with one 87 own-zero and all
port/mask hypotheses explicit; retains the same main carrier root. -/
theorem exact_indices (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    let qq := q beta v
    let R := naturalRank beta MC MF v
    let H : V := 3+4*a v
    ∃ n m d w : V, 13≤n ∧ n<m ∧ m=R ∧ 2*n=R+1 ∧
      2*ycoord n (2*((X v*Y v)*Y v-1)+1)=k v ∧ k v=2*n+4*((X v*Y v)*Y v)*w ∧
      xcoord m (a v)=d ∧ ycoord m (a v)=c v ∧
      U beta v*d+H*k v=U beta v*(X v+a v*c v)+
        H*(U beta v*v 12+X v*Y v*qq+R+1) := by
  let qq := q beta v
  let R := naturalRank beta MC MF v
  let xx := X v
  let yy := Y v
  let aa := a v
  let cc := c v
  let kk := k v
  have hgap : v 1+v 2<qq := by
    simpa only [qq,q,AuxGraphNormClientDraft.q] using
      GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz
  have hF1 : 1≤v 1 := pos_iff_one_le.mp (hv 1)
  have ha1 : 1≤v 2 := pos_iff_one_le.mp (hv 2)
  have hgap1 : v 1+v 2+1≤qq := lt_iff_succ_le.mp hgap
  have hq3 : 3≤qq := by nlinarith
  have hX : 0<xx := hv 6
  have hc : cc=v 9+yy*kk := rfl
  have ha : aa=xx*yy+yy := rfl
  have hdelta : Delta v=delta aa := by dsimp [Delta,delta,aa]; ring
  obtain ⟨hR26,hRwindow,s,tau,n,r,w,hs,hY,ht,hn,hxfirst,hny,hr,hks,hnmod⟩ :=
    P72FirstInputs87Draft.first_inputs p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  have hYq : yy=qq*(qq*qq)*s := by simpa only [yy,Y,qq,Q] using hY
  obtain ⟨d,m,hm,hx,hy,hnorm,hbal⟩ :=
    MainIndex87Draft.main_index p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz
  have hstrong := StrongNorm87Draft.strong_norm p v hz
  rw [hdelta] at hstrong
  have haux := AuxNorm87Draft.aux_norm p beta K MC MF v hport hK hMCcast hMFcast hv hz
  change 2*ycoord n (2*((xx*yy)*yy-1)+1)=kk at hny
  change kk=2*n+4*((xx*yy)*yy)*w at hks
  have hexact := P72Exact.indices_ordinary qq xx yy kk R d cc aa s (v 4) (v 3) (v 5) (v 11)
    n w (qq^4) m (v 9) hq3 hX hs hYq (hv 9) hc (hv 4) (hv 3) ha
    hR26 hny hks hRwindow hnmod hy hnorm hstrong haux
  exact ⟨n,m,d,w,hexact.1,hexact.2.1,hexact.2.2.1,hexact.2.2.2,
    hny,hks,hx,hy,hbal⟩

end DiophantineConsistency.P72ExactIndices87Draft

#print axioms DiophantineConsistency.P72ExactIndices87Draft.exact_indices
