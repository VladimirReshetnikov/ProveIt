import GowersSzemeredi.Proofs16SelectedDifferencePairs
import GowersSzemeredi.Proofs16GraphEdgeExtraction

/-! A dense symmetric coherent graph and a large robustly connected set,
with explicit polynomial losses in the coherent quadruple density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasCoherentRobustGraph {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma kappa : Real) : Prop :=
  ∃ (E : Finset (ZMod N × ZMod N)) (A : Finset (ZMod N)),
    E ⊆ X ×ˢ X ∧ (3*kappa^2/64)*(N : Real)^2 ≤ E.card ∧
    (∀ p ∈ E, p.swap ∈ E) ∧
    (∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
      ColumnPairIdentity (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (sigma/36) p q) ∧
    A ⊆ X ∧ (9*kappa^2/512)*N ≤ (A.card : Real) ∧
    ∀ u ∈ A, ∀ v ∈ A,
      ((3*kappa^2/64)^5/16384)*(N : Real)^3 ≤
        ((graphFourWalks (fun x y => (x,y) ∈ E) u v).card : Real)

theorem CoherentBridgeSystem.robust_graph {N ell depth : Nat} [NeZero N] [Fact N.Prime]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta kappa : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta) (hdepth : 1 ≤ depth)
    (hfamily : CoherentFrequencyFamily X B theta F sigma Q) (hk : 0 < kappa)
    (hmass : kappa*(N : Real)^3 ≤ Q.card) (hsmall : eta ≤ kappa^2/256) (hN : 2 < N) :
    HasCoherentRobustGraph X B theta F sigma kappa := by
  obtain ⟨P,hPX,hP,hcoh⟩ := h.dense_pairs he hdepth hfamily hk hmass hsmall
  have hr3 : coherentRelationRadius sigma 3 = sigma/36 := by norm_num [coherentRelationRadius]
  obtain ⟨E,hPE,hEX,hsym,hEcoh⟩ := exists_symmetric_coherent_pairs hN X
    (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (sigma/36) P hPX (by
      intro p hp q hq hd
      simpa only [hr3] using (hcoh p hp q hq hd).2.2.2)
  have hE : (3*kappa^2/64)*(N : Real)^2 ≤ E.card := by
    have h : (P.card : Real) ≤ 2*E.card := by exact_mod_cast hPE
    nlinarith only [hP,h]
  have hdelta : 0 < 3*kappa^2/64 := by positivity
  obtain ⟨A,hAX,hA,hwalk⟩ := exists_dense_four_walk_set_on X E hEX hsym hdelta
    (by simpa only [ZMod.card] using hE)
  refine ⟨E,A,hEX,hE,hsym,hEcoh,hAX,?_,?_⟩
  · simp only [ZMod.card] at hA
    nlinarith only [hA]
  · intro u hu v hv
    have h := hwalk u hu v hv
    simp only [ZMod.card] at h
    convert h using 1
    ring

end LeanProofs.GowersSzemeredi
