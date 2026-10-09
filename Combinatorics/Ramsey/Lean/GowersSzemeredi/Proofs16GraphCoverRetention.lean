import GowersSzemeredi.Proofs16FourfoldGraphMap

/-! A prescribed dense graph overlap retains a common difference map.
The overlap density and original configuration density are independent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem common_graph_cover_retained_fibre {N : Nat} [NeZero N]
    (A B S : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N)) (a c : ZMod N)
    (hSB : S ⊆ B) (hagree : ∀ s ∈ S, s+a ∈ A ∧ f 0 (s+a) = f 1 s+c)
    (hA : ∀ q ∈ Q, q 0 ∈ A) (hB : ∀ q ∈ Q, q 1 ∈ B)
    (hf : IsFreimanLinearOn A (f 0)) (hg : IsFreimanLinearOn B (f 1))
    {mu delta : Real} (hmu : 0 < mu) (hS : mu*N ≤ (S.card : Real))
    (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card)
    (theta : ZMod N → ZMod N)
    (hrepr : ∀ p : Fin 4 → ZMod N, (∀ i, p i ∈ S) →
      theta (fourfoldGraphIndex p) = fourfoldGraphIndex (f 1 ∘ p)) :
    ∃ (b d : ZMod N) (R : Finset (Fin 4 → ZMod N)), R ⊆ Q ∧
      (mu^2*delta)*(N : Real)^3 ≤ R.card ∧
      ∀ q ∈ R, q 0-q 1-b ∈ fourfoldGraphDomain S ∧
        f 0 (q 0)-f 1 (q 1) = d+theta (q 0-q 1-b) := by
  obtain ⟨J,_,K,_,_,_,hJK,hcover⟩ :=
    common_graph_difference_cover A B S (f 0) (f 1) a c hSB hagree hf hg hmu hS
  have hex (q : Fin 4 → ZMod N) (hq : q ∈ Q) :
      ∃ p ∈ J ×ˢ K, q 0-q 1-(p.1-p.2) ∈ fourfoldGraphDomain S ∧
        f 0 (q 0)-f 1 (q 1) = (f 0 p.1-f 1 p.2)+theta (q 0-q 1-(p.1-p.2)) := by
    obtain ⟨j,hj,k,hk,u,hu,v,hv,w,hw,z,hz,hindex,hvalue⟩ := hcover (q 0) (hA q hq) (q 1) (hB q hq)
    let p : Fin 4 → ZMod N := ![u,v,w,z]
    have hp : ∀ i, p i ∈ S := by intro i; fin_cases i <;> assumption
    have he : q 0-q 1-(j-k) = fourfoldGraphIndex p := by
      dsimp [fourfoldGraphIndex,p]
      linear_combination hindex
    refine ⟨(j,k),Finset.mem_product.mpr ⟨hj,hk⟩,?_,?_⟩
    · rw [he]
      exact Finset.mem_image.mpr ⟨p,by simpa only [Fintype.mem_piFinset] using hp,rfl⟩
    · rw [he,hrepr p hp]
      dsimp [fourfoldGraphIndex,Function.comp_def,p]
      linear_combination hvalue
  let label (q : Fin 4 → ZMod N) := if hq : q ∈ Q then (hex q hq).choose else (0,0)
  have hlabel (q : Fin 4 → ZMod N) (hq : q ∈ Q) : label q ∈ J ×ˢ K ∧
      q 0-q 1-((label q).1-(label q).2) ∈ fourfoldGraphDomain S ∧
      f 0 (q 0)-f 1 (q 1) = (f 0 (label q).1-f 1 (label q).2)+
        theta (q 0-q 1-((label q).1-(label q).2)) := by
    simpa only [label,dif_pos hq] using (hex q hq).choose_spec
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQne : Q.Nonempty := Finset.card_pos.mp (by
    have hpos := lt_of_lt_of_le (mul_pos hdelta (pow_pos hn 3)) hcount
    exact_mod_cast hpos)
  obtain ⟨q0,hq0⟩ := hQne
  have hJKne : (J ×ˢ K).Nonempty := ⟨label q0,(hlabel q0 hq0).1⟩
  have hmass : ((J ×ˢ K).card : Real)*((mu^2*delta)*(N : Real)^3) ≤ Q.card := by
    calc ((J ×ˢ K).card : Real)*((mu^2*delta)*(N : Real)^3)
        = ((J.card : Real)*K.card*mu^2)*(delta*(N : Real)^3) := by
          simp only [Finset.card_product,Nat.cast_mul]; ring
      _ ≤ 1*(delta*(N : Real)^3) := mul_le_mul_of_nonneg_right hJK
        (mul_nonneg hdelta.le (pow_nonneg hn.le 3))
      _ ≤ Q.card := by simpa only [one_mul] using hcount
  obtain ⟨p,_,hp⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := Q) (t := J ×ˢ K) (f := label) (b := (mu^2*delta)*(N : Real)^3)
    (fun q hq => (hlabel q hq).1) hJKne (by simpa only [nsmul_eq_mul] using hmass)
  refine ⟨p.1-p.2,f 0 p.1-f 1 p.2,Q.filter (label · = p),
    Finset.filter_subset _ _,hp,?_⟩
  intro q hq
  obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
  simpa only [he] using (hlabel q hq).2

end LeanProofs.GowersSzemeredi
