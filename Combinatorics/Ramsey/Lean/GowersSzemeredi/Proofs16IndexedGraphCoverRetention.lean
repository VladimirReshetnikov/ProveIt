import GowersSzemeredi.Proofs16FourfoldGraphMap

/-! A prescribed graph overlap retains a common difference map on an
arbitrary indexed family. Multiplicities of its two endpoint projections
are preserved, and the retained mass is explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem indexed_common_graph_cover_retained_fibre {N : Nat} [NeZero N] {X : Type*}
    (A B S : Finset (ZMod N)) (f g : ZMod N → ZMod N)
    (Q : Finset X) (x y : X → ZMod N) (a c : ZMod N)
    (hSB : S ⊆ B) (hagree : ∀ s ∈ S, s+a ∈ A ∧ f (s+a) = g s+c)
    (hA : ∀ q ∈ Q, x q ∈ A) (hB : ∀ q ∈ Q, y q ∈ B)
    (hf : IsFreimanLinearOn A f) (hg : IsFreimanLinearOn B g)
    {mu mass : Real} (hmu : 0 < mu) (hS : mu*N ≤ (S.card : Real))
    (hmass : 0 < mass) (hcount : mass ≤ Q.card)
    (theta : ZMod N → ZMod N)
    (hrepr : ∀ p : Fin 4 → ZMod N, (∀ i, p i ∈ S) →
      theta (fourfoldGraphIndex p) = fourfoldGraphIndex (g ∘ p)) :
    ∃ (b d : ZMod N) (R : Finset X), R ⊆ Q ∧
      mu^2*mass ≤ R.card ∧
      ∀ q ∈ R, x q-y q-b ∈ fourfoldGraphDomain S ∧
        f (x q)-g (y q) = d+theta (x q-y q-b) := by
  obtain ⟨J,_,K,_,_,_,hJK,hcover⟩ :=
    common_graph_difference_cover A B S f g a c hSB hagree hf hg hmu hS
  have hex (q : X) (hq : q ∈ Q) :
      ∃ p ∈ J ×ˢ K, x q-y q-(p.1-p.2) ∈ fourfoldGraphDomain S ∧
        f (x q)-g (y q) = (f p.1-g p.2)+theta (x q-y q-(p.1-p.2)) := by
    obtain ⟨j,hj,k,hk,u,hu,v,hv,w,hw,z,hz,hindex,hvalue⟩ := hcover (x q) (hA q hq) (y q) (hB q hq)
    let p : Fin 4 → ZMod N := ![u,v,w,z]
    have hp : ∀ i, p i ∈ S := by intro i; fin_cases i <;> assumption
    have he : x q-y q-(j-k) = fourfoldGraphIndex p := by
      dsimp [fourfoldGraphIndex,p]
      linear_combination hindex
    refine ⟨(j,k),Finset.mem_product.mpr ⟨hj,hk⟩,?_,?_⟩
    · rw [he]
      exact Finset.mem_image.mpr ⟨p,by simpa only [Fintype.mem_piFinset] using hp,rfl⟩
    · rw [he,hrepr p hp]
      dsimp [fourfoldGraphIndex,Function.comp_def,p]
      linear_combination hvalue
  let label (q : X) := if hq : q ∈ Q then (hex q hq).choose else (0,0)
  have hlabel (q : X) (hq : q ∈ Q) : label q ∈ J ×ˢ K ∧
      x q-y q-((label q).1-(label q).2) ∈ fourfoldGraphDomain S ∧
      f (x q)-g (y q) = (f (label q).1-g (label q).2)+
        theta (x q-y q-((label q).1-(label q).2)) := by
    simpa only [label,dif_pos hq] using (hex q hq).choose_spec
  have hQne : Q.Nonempty := Finset.card_pos.mp (by
    have hpos := lt_of_lt_of_le hmass hcount
    exact_mod_cast hpos)
  obtain ⟨q0,hq0⟩ := hQne
  have hJKne : (J ×ˢ K).Nonempty := ⟨label q0,(hlabel q0 hq0).1⟩
  have hbudget : ((J ×ˢ K).card : Real)*(mu^2*mass) ≤ Q.card := by
    calc ((J ×ˢ K).card : Real)*(mu^2*mass)
        = ((J.card : Real)*K.card*mu^2)*mass := by
          simp only [Finset.card_product,Nat.cast_mul]; ring
      _ ≤ 1*mass := mul_le_mul_of_nonneg_right hJK
        hmass.le
      _ ≤ Q.card := by simpa only [one_mul] using hcount
  obtain ⟨p,_,hp⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := Q) (t := J ×ˢ K) (f := label) (b := mu^2*mass)
    (fun q hq => (hlabel q hq).1) hJKne (by simpa only [nsmul_eq_mul] using hbudget)
  refine ⟨p.1-p.2,f p.1-g p.2,Q.filter (label · = p),
    Finset.filter_subset _ _,hp,?_⟩
  intro q hq
  obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
  simpa only [he] using (hlabel q hq).2

end LeanProofs.GowersSzemeredi
