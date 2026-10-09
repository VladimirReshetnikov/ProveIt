import GowersSzemeredi.Proofs16CoherentWalkRichness
import GowersSzemeredi.Proofs16CoherentRobustGraph

/-! A coherent frequency family yields a large set that is additively
rich between every two sufficiently dense subsets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentRobustWalkDensity (kappa : Real) : Real := (3*kappa^2/64)^5/16384

def HasCoherentRichSet {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma kappa beta : Real) : Prop :=
  ∃ A : Finset (ZMod N), A ⊆ X ∧ (9*kappa^2/512)*N ≤ (A.card : Real) ∧
    ∀ U V : Finset (ZMod N), U ⊆ A → V ⊆ A → beta*N ≤ (U.card : Real) → beta*N ≤ (V.card : Real) →
      (beta^2*coherentRobustWalkDensity kappa)^2*(N : Real)^3/2 ≤
        ((mixedExactColumnQuadruples U V (fun u => B ∪ Finset.univ.image (fun j => theta j u))
          F (sigma/1296)).card : Real)

theorem CoherentBridgeSystem.rich_set {N ell depth : Nat} [NeZero N] [Fact N.Prime]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta kappa beta : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta) (hdepth : 3 ≤ depth)
    (hfamily : CoherentFrequencyFamily X B theta F sigma Q) (hk : 0 < kappa)
    (hmass : kappa*(N : Real)^3 ≤ Q.card) (hsmall : eta ≤ kappa^2/256)
    (hb : 0 < beta) (herror : 4*eta < (beta^2*coherentRobustWalkDensity kappa)^2) (hN : 2 < N) :
    HasCoherentRichSet X B theta F sigma kappa beta := by
  obtain ⟨E,A,hEX,hE,hsym,hcoh,hAX,hA,hwalk⟩ :=
    h.robust_graph he (by omega) hfamily hk hmass hsmall hN
  refine ⟨A,hAX,hA,?_⟩
  intro U V hU hV hUd hVd
  have hl : 0 < coherentRobustWalkDensity kappa := by unfold coherentRobustWalkDensity; positivity
  have hcoh' : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
      CoherentRelationLevel X B theta F sigma 3 p q := by
    intro p hp q hq hd
    refine ⟨Finset.mem_product.mp (hEX hp),Finset.mem_product.mp (hEX hq),hd,?_⟩
    have hr : coherentRelationRadius sigma 3 = sigma/36 := by norm_num [coherentRelationRadius]
    rw [hr]
    exact hcoh p hp q hq hd
  have hm := h.mixed_quadruples_of_walks (i := 2) he hdepth hb hb hl
    (by simpa only [pow_two] using herror) E U V hUd hVd
    (fun u hu v hv => hwalk u (hU hu) v (hV hv)) hcoh'
  have hr : coherentRelationRadius sigma 5 = sigma/1296 := by norm_num [coherentRelationRadius]
  simpa only [hr,pow_two] using hm

end LeanProofs.GowersSzemeredi
