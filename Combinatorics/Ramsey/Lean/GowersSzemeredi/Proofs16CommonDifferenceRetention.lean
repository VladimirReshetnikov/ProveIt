import GowersSzemeredi.Proofs16GraphCoverRetention

/-! Retain a dense configuration family whose mixed graph differences
are represented by one translated Freiman map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mixed_configurations_common_difference_map {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    (hA : ∀ q ∈ Q, q 0 ∈ A) (hB : ∀ q ∈ Q, q 1 ∈ B)
    (hf : IsFreimanLinearOn A (f 0)) (hg : FreimanHom 8 B (f 1))
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ S ⊆ B, delta*N ≤ (S.card : Real) ∧
      ∃ (theta : ZMod N → ZMod N) (a c : ZMod N) (R : Finset (Fin 4 → ZMod N)),
        IsFreimanLinearOn (fourfoldGraphDomain S) theta ∧ R ⊆ Q ∧
        delta^3*(N : Real)^3 ≤ R.card ∧
        (∀ p : Fin 4 → ZMod N, (∀ i, p i ∈ S) →
          theta (fourfoldGraphIndex p) = fourfoldGraphIndex (f 1 ∘ p)) ∧
        ∀ q ∈ R, q 0-q 1-a ∈ fourfoldGraphDomain S ∧
          f 0 (q 0)-f 1 (q 1) = c+theta (q 0-q 1-a) := by
  have hg2 : IsFreimanLinearOn B (f 1) := fun _ _ _ _ hx hy hz hw he =>
    (IsAddFreimanHom.mono (by decide : 2 ≤ 8) hg).add_eq_add hx hy hz hw he
  obtain ⟨a,c,S,hSB,hS,hagree⟩ :=
    mixed_configurations_dense_overlap A B f Q hQ hA hB hcount
  have hgS : FreimanHom 8 S (f 1) :=
    IsAddFreimanHom.subset hSB hg (Set.mapsTo_univ _ _)
  obtain ⟨theta,htheta,hrepr⟩ := exists_fourfold_graph_map S (f 1) hgS
  obtain ⟨b,d,R,hRQ,hR,hvalue⟩ := common_graph_cover_retained_fibre A B S f Q a c
    hSB hagree hA hB hf hg2 hdelta hS hdelta hcount theta hrepr
  refine ⟨S,hSB,hS,theta,b,d,R,htheta,hRQ,?_,hrepr,hvalue⟩
  convert hR using 1
  ring

end LeanProofs.GowersSzemeredi
