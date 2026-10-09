import GowersSzemeredi.Proofs16CommonGraphCover

/-! An order-eight Freiman map induces an order-two map on 2S-2S. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def fourfoldGraphIndex {N : Nat} (p : Fin 4 → ZMod N) : ZMod N :=
  (p 0-p 1)-(p 2-p 3)

def fourfoldGraphDomain {N : Nat} [NeZero N] (S : Finset (ZMod N)) : Finset (ZMod N) :=
  (Fintype.piFinset fun _ : Fin 4 => S).image fourfoldGraphIndex

theorem freiman_eight_fourfold_relation {N : Nat}
    (S : Finset (ZMod N)) (f : ZMod N → ZMod N) (hf : FreimanHom 8 S f)
    (p q r t : Fin 4 → ZMod N)
    (hp : ∀ i, p i ∈ S) (hq : ∀ i, q i ∈ S)
    (hr : ∀ i, r i ∈ S) (ht : ∀ i, t i ∈ S)
    (he : fourfoldGraphIndex p+fourfoldGraphIndex q = fourfoldGraphIndex r+fourfoldGraphIndex t) :
    fourfoldGraphIndex (f ∘ p)+fourfoldGraphIndex (f ∘ q) =
      fourfoldGraphIndex (f ∘ r)+fourfoldGraphIndex (f ∘ t) := by
  let U : Multiset (ZMod N) := ↑[p 0,p 3,q 0,q 3,r 1,r 2,t 1,t 2]
  let V : Multiset (ZMod N) := ↑[r 0,r 3,t 0,t 3,p 1,p 2,q 1,q 2]
  have hU : ∀ ⦃x⦄, x ∈ U → x ∈ (S : Set (ZMod N)) := by
    intro x hx
    simp only [U,Multiset.mem_coe,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact hp _ | exact hq _ | exact hr _ | exact ht _
  have hV : ∀ ⦃x⦄, x ∈ V → x ∈ (S : Set (ZMod N)) := by
    intro x hx
    simp only [V,Multiset.mem_coe,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact hp _ | exact hq _ | exact hr _ | exact ht _
  have hsum : U.sum = V.sum := by
    simp [U,V]
    dsimp [fourfoldGraphIndex] at he
    linear_combination he
  have hv := hf.map_sum_eq_map_sum hU hV (by simp [U]) (by simp [V]) hsum
  simp [U,V] at hv
  dsimp [fourfoldGraphIndex,Function.comp_def]
  linear_combination hv

theorem freiman_eight_fourfold_congr {N : Nat}
    (S : Finset (ZMod N)) (f : ZMod N → ZMod N) (hf : FreimanHom 8 S f)
    (p q : Fin 4 → ZMod N) (hp : ∀ i, p i ∈ S) (hq : ∀ i, q i ∈ S)
    (he : fourfoldGraphIndex p = fourfoldGraphIndex q) :
    fourfoldGraphIndex (f ∘ p) = fourfoldGraphIndex (f ∘ q) := by
  have h := freiman_eight_fourfold_relation S f hf p p q p hp hp hq hp (by rw [he])
  exact add_right_cancel h

/-- The value is independent of the chosen four-term representation,
and additive quadruples in the whole difference set are preserved. -/
theorem exists_fourfold_graph_map {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (f : ZMod N → ZMod N) (hf : FreimanHom 8 S f) :
    ∃ theta : ZMod N → ZMod N,
      IsFreimanLinearOn (fourfoldGraphDomain S) theta ∧
      ∀ p : Fin 4 → ZMod N, (∀ i, p i ∈ S) →
        theta (fourfoldGraphIndex p) = fourfoldGraphIndex (f ∘ p) := by
  have hex : ∀ x ∈ fourfoldGraphDomain S, ∃ p : Fin 4 → ZMod N,
      (∀ i, p i ∈ S) ∧ fourfoldGraphIndex p = x := by
    intro x hx
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hx
    exact ⟨p,by simpa only [Fintype.mem_piFinset] using hp,he⟩
  let repr (x : ZMod N) (hx : x ∈ fourfoldGraphDomain S) := (hex x hx).choose
  have hs x hx := (hex x hx).choose_spec
  let theta (x : ZMod N) := if hx : x ∈ fourfoldGraphDomain S then
    fourfoldGraphIndex (f ∘ repr x hx) else 0
  have htheta (p : Fin 4 → ZMod N) (hp : ∀ i, p i ∈ S) :
      theta (fourfoldGraphIndex p) = fourfoldGraphIndex (f ∘ p) := by
    have hmem : fourfoldGraphIndex p ∈ fourfoldGraphDomain S :=
      Finset.mem_image.mpr ⟨p,by simpa only [Fintype.mem_piFinset] using hp,rfl⟩
    dsimp [theta]
    rw [dif_pos hmem]
    exact freiman_eight_fourfold_congr S f hf _ p (hs _ hmem).1 hp (hs _ hmem).2
  refine ⟨theta,?_,htheta⟩
  intro x y z w hx hy hz hw he
  obtain ⟨p,hp,rfl⟩ := hex x hx
  obtain ⟨q,hq,rfl⟩ := hex y hy
  obtain ⟨r,hr,rfl⟩ := hex z hz
  obtain ⟨t,ht,rfl⟩ := hex w hw
  rw [htheta p hp,htheta q hq,htheta r hr,htheta t ht]
  exact freiman_eight_fourfold_relation S f hf p q r t hp hq hr ht he

end LeanProofs.GowersSzemeredi
