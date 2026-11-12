import DirectNorms85
import QCubeSize
import SignedScaledRoot
import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

/-! Source-only direct 85 own-zero main norm and balance. No 84 zero,
FreeJ zero, q|X, Pell index or endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.MainBalance85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticAdaptiveMainOrientation2011
open NaturalRank84Draft DirectNorms85Draft SignedScaledRootDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def mainValue (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) : DiffRing V :=
  let ur := ι (U beta v)
  let ar := ι (a beta v)
  let cr := ι (c beta v)
  let hr := 3+4*ar
  ur*(ι (X v)+ar*cr)+hr*(ur*ι (v 12)+ι (X v*Y beta v*q beta v)-
    (ι (k v)-AuxGraphNormClientDraft.rank p beta v-1))

/-- Literal 85 main field retains its X*Y*q term. -/
theorem main_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P85QcubeGraph.graph p).A1 v=mainValue p beta v*mainValue p beta v-
      (ι (U beta v)*ι (U beta v))*ι (1+Delta beta v*c beta v*c beta v) := by
  simp [eval,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,mainValue,
    AuxGraphNormClientDraft.rank,q,X,Y,U,k,a,c,Delta,hport,map_add,map_mul,map_one] <;> ring

/-- From a positive 85 own-zero, derive the natural main norm and its exact
subtraction-free carrier balance, without assuming any divisibility of X. -/
theorem norm_and_balance (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    let R := naturalRank beta MC MF v
    let H : V := 3+4*a beta v
    ∃ d : V, d*d=1+Delta beta v*c beta v*c beta v ∧
      U beta v*d+H*k v=U beta v*(X v+a beta v*c beta v)+
        H*(U beta v*v 12+X v*Y beta v*q beta v+R+1) := by
  let R := naturalRank beta MC MF v
  let H : V := 3+4*a beta v
  have hR : AuxGraphNormClientDraft.rank p beta v=ι R :=
    GuardRank85Draft.rank_of_85_zero p beta K MC MF v hport hK hMC hMF (hv 1) (hv 6) hz
  have hq : 0<q beta v := by dsimp [q]; simp
  have hY : 0<Y beta v := by dsimp [Y]; exact mul_pos (mul_pos hq (mul_pos hq hq)) (hv 7)
  have hU : 0<U beta v := by dsimp [U]; exact mul_pos hY (mul_pos hq hq)
  have hk : 0<k v := by dsimp [k]; exact add_pos (hv 9) (hv 10)
  have hY8 : 8≤Y beta v := by
    simpa only [Y,q,AuxGraphNormClientDraft.Y,AuxGraphNormClientDraft.q] using
      QCubeSize84Draft.Y_at_least_eight beta v hbeta (hv 0) (hv 7)
  have hparts : H*k v<U beta v*(X v+a beta v*c beta v)+
      H*(U beta v*v 12+X v*Y beta v*q beta v+R+1) := by
    simpa only [H,a,c,k] using
      main_parts_positive (U beta v) (X v) (Y beta v) (k v) (v 9) (v 12) (q beta v) R hU hY8 hk
  have hlt : ι (H*k v)<ι (U beta v*(X v+a beta v*c beta v)+
      H*(U beta v*v 12+X v*Y beta v*q beta v+R+1)) := ι_lt_ι.mpr hparts
  have hrepr : mainValue p beta v=
      ι (U beta v*(X v+a beta v*c beta v)+H*(U beta v*v 12+X v*Y beta v*q beta v+R+1))-
      ι (H*k v) := by
    simp [mainValue,hR,H,map_add,map_mul,map_one] <;> ring
  have hpos : 0<mainValue p beta v := by rw [hrepr]; exact sub_pos.mpr hlt
  have hm := (ZeroFields8485Draft.fields85 p v hz).2.1
  change eval (P85QcubeGraph.graph p).A1 v=0 at hm
  rw [main_eval p beta v hport] at hm
  obtain ⟨d,hn,hr⟩ := scaled_signed_root (U beta v) (1+Delta beta v*c beta v*c beta v)
    (mainValue p beta v) hU (sub_eq_zero.mp hm)
  have hroot : mainValue p beta v=ι (U beta v*d) := by
    rcases hr with h | h
    · exact h
    · have hnpos : mainValue p beta v≤0 := by rw [h]; exact neg_nonpos.mpr (ι_nonneg _)
      exact False.elim ((not_le_of_gt hpos) hnpos)
  refine ⟨d,hn,?_⟩
  have hroot' : ι (U beta v)*ι d=mainValue p beta v := by simpa only [map_mul] using hroot.symm
  apply ι_injective
  simp only [map_add,map_mul,map_one]
  rw [hroot',hrepr]
  simp only [map_add,map_mul,map_one]
  ring

end DiophantineConsistency.MainBalance85Draft

#print axioms DiophantineConsistency.MainBalance85Draft.norm_and_balance
