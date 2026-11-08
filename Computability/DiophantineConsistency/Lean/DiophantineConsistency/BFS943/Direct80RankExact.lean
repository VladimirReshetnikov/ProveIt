import DiophantineConsistency.BFS943.Direct80NaturalRank
import DiophantineConsistency.BFS943.Direct80RankWindow
import DiophantineConsistency.BFS943.Direct80RankSize
import DiophantineConsistency.BFS943.Direct80RankEquality

/-! Fixed-port rank window yields exact odd main-index recovery. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80RankExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open TenPositive80Graph TenPositive80Factors TenPositive80ResidueBinding TenPositive80NaturalRank
open TenPositive80RankEquality Direct80RankSize
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rank_def_eq (p : Fin 4 → ℕ) (v : Fin 10 → V) : rankNat p v=Direct80RankWindow.rank p v := by
  have hq : q p v=1+v 0*(p 0:V) := by dsimp [q,b]; ring
  change (b p v*(q p v-v 1)+v 2)*(q p v*q p v-1)+
      ((p 2:V)+q p v*(p 3:V))*v 0 =
    (v 2+((1+v 0*(p 0:V))-v 1)*(v 0*(p 0:V)))*
      ((1+v 0*(p 0:V))*(1+v 0*(p 0:V))-1)+
        v 0*((p 2:V)+(p 3:V)*(1+v 0*(p 0:V)))
  rw [←hq]
  have hb : v 0*(p 0:V)=b p v := by dsimp [b]; ring
  rw [hb]
  ring

theorem magnitude_of_graph_rank (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (rp rn R : V)
    (hrep : (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι rp-ι rn)
    (hnat : (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι R) :
    absdiff rp rn=R := by
  have hring : (ι rp:DiffRing V)-ι rn=ι R := hrep.symm.trans hnat
  have heq : rp=rn+R := by
    apply ι_injective
    calc
      (ι rp:DiffRing V)=((ι rp:DiffRing V)-ι rn)+ι rn := by ring
      _=ι R+ι rn := by rw [hring]
      _=ι (rn+R) := by rw [map_add]; ring
  have hh : magnitude (rp,rn)=R := magnitude_of_add heq
  exact hh

theorem graph_rank_exact (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    24≤rankNat p v ∧ rankNat p v+(q p v)^3+q p v+1≤(q p v)^4 ∧
    rankNat p v%2=1 ∧ c p v=ycoord (rankNat p v) (A p v-1) := by
  obtain ⟨hnat,_hpos,hgap⟩ := graph_natural_rank p v hb hv hz
  have hgap' : v 1+v 2<1+v 0*(p 0:V) := by
    have he : q p v=1+v 0*(p 0:V) := by dsimp [q,b]; ring
    rwa [←he]
  have hw := Direct80RankWindow.window p v hb hl hh hv hgap'
  have he : q p v=1+v 0*(p 0:V) := by dsimp [q,b]; ring
  change 24≤Direct80RankWindow.rank p v ∧
    Direct80RankWindow.rank p v+(1+v 0*(p 0:V))^3+(1+v 0*(p 0:V))+1≤(1+v 0*(p 0:V))^4 at hw
  rw [←rank_def_eq p v,←he] at hw
  have hRle : rankNat p v≤(q p v)^4 := by
    calc
      rankNat p v≤rankNat p v+(q p v)^3 := by simp
      _≤rankNat p v+(q p v)^3+q p v := by simp
      _≤rankNat p v+(q p v)^3+q p v+1 := by simp
      _≤(q p v)^4 := hw.2
  have hsize : 2*(q p v)^4<c p v := (graph_rank_size p v hb hv hz).2
  have hsmall : ∀ rp rn : V,
      (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι rp-ι rn →
      2*absdiff rp rn<c p v := by
    intro rp rn hrep
    rw [magnitude_of_graph_rank p v rp rn (rankNat p v) hrep hnat]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hRle (by simp)) hsize
  obtain ⟨r,rp,rn,_hr,hodd,hc,hrep,hmag⟩ := graph_rank_equality_of_small p v hb hv hz hsmall
  have hR : rankNat p v=r := by
    have h := magnitude_of_graph_rank p v rp rn (rankNat p v) hrep hnat
    exact h.symm.trans hmag
  exact ⟨hw.1,hw.2,by rw [hR]; exact hodd,by rw [hR]; exact hc⟩

#print axioms TenPositive80RankExact.graph_rank_exact
end TenPositive80RankExact
