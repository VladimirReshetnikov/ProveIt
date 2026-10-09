import GowersSzemeredi.Proofs16CoherentCommonNeighbours
import GowersSzemeredi.Proofs16CoherentRelationMass

/-! Dense difference graphs contain large coherent cliques after only two
factor-six radius losses. Two common-neighborhood steps suffice. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem CoherentBridgeSystem.fibre_clique {N ell depth : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta delta : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta)
    (hdepth : 1 ≤ depth) (hd : 0 < delta)
    (heCodegree : eta ≤ delta^2/64) (hePartners : eta ≤ delta/4)
    (a : ZMod N)
    (hE : delta*(N : Real)^2 ≤ (coherentDifferenceEdges X B theta F sigma 1 a).card) :
    ∃ T ⊆ X, (∀ u ∈ T, u+a ∈ X) ∧ 3*delta*N/8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T, CoherentRelationLevel X B theta F sigma 3 (u+a,u) (v+a,v) := by
  let G := fun u v => CoherentRelationLevel X B theta F sigma 1 (u+a,u) (v+a,v)
  have hG : ∀ u v, G u v → G v u := fun u v huv => CoherentRelationLevel.symm huv
  have hcount : (∑ u : ZMod N, (graphNeighbours G u).card) =
      (coherentDifferenceEdges X B theta F sigma 1 a).card := by
    simp only [G,graphNeighbours,coherentDifferenceEdges,Finset.card_filter,Fintype.sum_prod_type]
  have hsum : delta*(Fintype.card (ZMod N) : Real)^2 ≤
      ∑ u : ZMod N, ((graphNeighbours G u).card : Real) := by
    rw [← Nat.cast_sum,hcount,ZMod.card]
    exact hE
  obtain ⟨T,hT,hcommon⟩ := exists_dense_common_codegree_set G hG hd hsum
  simp only [ZMod.card] at hT hcommon
  have hfirst (u v : ZMod N)
      (hc : delta^2*(N : Real)/64 ≤ ((graphCommonNeighbours G u v).card : Real)) :
      CoherentRelationLevel X B theta F sigma 2 (u+a,u) (v+a,v) := by
    apply h.common_neighbours he (Nat.zero_le _) a u v
    exact (show eta*(N : Real) ≤ delta^2*(N : Real)/64 by
      have hh := mul_le_mul_of_nonneg_right heCodegree (Nat.cast_nonneg N)
      nlinarith only [hh]).trans hc
  have hclique : ∀ u ∈ T, ∀ v ∈ T,
      CoherentRelationLevel X B theta F sigma 3 (u+a,u) (v+a,v) := by
    intro u hu v hv
    apply h.common_neighbours he hdepth a u v
    have hsub : (Finset.univ.filter (fun z : ZMod N =>
        delta^2*(N : Real)/64 ≤ ((graphCommonNeighbours G u z).card : Real) ∧
        delta^2*(N : Real)/64 ≤ ((graphCommonNeighbours G v z).card : Real))) ⊆
        graphCommonNeighbours
          (fun x y => CoherentRelationLevel X B theta F sigma 2 (x+a,x) (y+a,y)) u v := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfirst u z (Finset.mem_filter.mp hz).2.1,
        hfirst v z (Finset.mem_filter.mp hz).2.2⟩
    have hsmall : eta*(N : Real) ≤ delta*(N : Real)/4 := by
      have hh := mul_le_mul_of_nonneg_right hePartners (Nat.cast_nonneg N)
      nlinarith only [hh]
    exact (hsmall.trans (hcommon u hu v hv)).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  exact ⟨T,fun u hu => (hclique u hu u hu).1.2,
    fun u hu => (hclique u hu u hu).1.1,hT,hclique⟩

end LeanProofs.GowersSzemeredi
