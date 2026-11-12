import P72ExactIndices
import CarrierGamma
import ConditionalComparison

/-! Source-only positive 84→85 model map. Its exact-index, gamma and graph
imports are unelaborated drafts. The opposite implication is separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelMap84To85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence
open NaturalRank84Draft ModifiedCarrierGammaDraft Conditional84To85Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive 84→85 map under natural port casts and explicit mask
bounds, using the 84 graph's own zero throughout. No 85 zero is assumed. -/
theorem positive_map (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P85QcubeGraph.graph p).output v' := by
  let q := AuxGraphNormClientDraft.q beta v
  let R := naturalRank beta MC MF v
  let U := AuxGraphNormClientDraft.U beta v
  let X := AuxGraphNormClientDraft.X beta v
  let Y := AuxGraphNormClientDraft.Y beta v
  let a := AuxGraphNormClientDraft.a beta v
  let c := AuxGraphNormClientDraft.c beta v
  let k := AuxGraphNormClientDraft.k v
  let H : V := 3+4*a
  obtain ⟨n,m,d,s,_,_,hmR,hnR,_,hks,hx,hy,hbal⟩ :=
    P72ExactIndices84Draft.exact_indices p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  let W : V := 4*X*q*(v 7)*s
  have hk : k=R+1+U*W := by
    rw [hks,hnR]
    dsimp [U,Y,W,AuxGraphNormClientDraft.U,AuxGraphNormClientDraft.Y]
    ring
  have hq0 : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hq : 1≤q := pos_iff_one_le.mp hq0
  have hY : 0<Y := by
    dsimp [Y,AuxGraphNormClientDraft.Y]
    exact mul_pos (mul_pos hq0 (mul_pos hq0 hq0)) (hv 7)
  have hU : 0<U := by
    dsimp [U,AuxGraphNormClientDraft.U]
    exact mul_pos hY (mul_pos hq0 hq0)
  have hX : X=q*v 6 := rfl
  have ha : a=X*Y+Y := rfl
  have hH : H=4*a+3 := by dsimp [H]; ring
  have hR40 : 40≤R := RankLower4084Draft.rank_lower40 p beta K MC MF v hbeta hport hK hv hz
  have hR3 : 3≤R := le_trans (by norm_num : (3:V)≤40) hR40
  have hc : c=ycoord R a := by rw [←hmR]; exact hy.symm
  have hd : d=xcoord R a := by rw [←hmR]; exact hx.symm
  have hgamma : v 6<v 12 :=
    gamma_gt_from_modified_balance U H d X Y a c (v 12) k R W q (v 6)
      hU hY hq hX ha hH hR3 hc hd hk hbal
  exact map_84_to_85 p beta v hport hv hgamma hz

end DiophantineConsistency.ModelMap84To85Draft

#print axioms DiophantineConsistency.ModelMap84To85Draft.positive_map
