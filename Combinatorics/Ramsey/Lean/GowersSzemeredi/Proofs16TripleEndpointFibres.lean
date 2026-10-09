import GowersSzemeredi.Proofs16PopularEndpointFibres

/-! The fixed-index equation bounds each endpoint fibre of a triple
representation by N, rather than N squared. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem columnTriple_first_fibre_card_le {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a x : ZMod N) :
    ((columnTripleRepresentations B T L r a).filter (fun t => t.1 = x)).card ≤ N := by
  have h := Finset.card_le_card_of_injOn
    (s := (columnTripleRepresentations B T L r a).filter (fun t => t.1 = x))
    (t := (Finset.univ : Finset (ZMod N))) (fun t => t.2.1) (by simp) (by
      intro p hp q hq hm
      have hfirst := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      have hpidx := (columnTripleRepresentations_spec B T L r (Finset.mem_filter.mp hp).1).2.2.2.2.1
      have hqidx := (columnTripleRepresentations_spec B T L r (Finset.mem_filter.mp hq).1).2.2.2.2.1
      have hlast : p.2.2 = q.2.2 := by linear_combination -hpidx+hqidx-hfirst+hm
      exact Prod.ext hfirst (Prod.ext hm hlast))
  simpa using h

theorem columnTriple_last_fibre_card_le {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a x : ZMod N) :
    ((columnTripleRepresentations B T L r a).filter (fun t => t.2.2 = x)).card ≤ N := by
  have h := Finset.card_le_card_of_injOn
    (s := (columnTripleRepresentations B T L r a).filter (fun t => t.2.2 = x))
    (t := (Finset.univ : Finset (ZMod N))) (fun t => t.2.1) (by simp) (by
      intro p hp q hq hm
      have hlast := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      have hpidx := (columnTripleRepresentations_spec B T L r (Finset.mem_filter.mp hp).1).2.2.2.2.1
      have hqidx := (columnTripleRepresentations_spec B T L r (Finset.mem_filter.mp hq).1).2.2.2.2.1
      have hfirst : p.1 = q.1 := by linear_combination -hpidx+hqidx+hm-hlast
      exact Prod.ext hfirst (Prod.ext hm hlast))
  simpa using h

/-- Both endpoint directions admit dense popular fibres at the same
threshold. -/
theorem columnTriple_popular_endpoints {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a : ZMod N) {lambda : Real}
    (hl : 0 < lambda) (hcount : lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card) :
    let S := columnTripleRepresentations B T L r a
    let U := popularEndpointFibres S (fun t => t.1) (lambda*N/2)
    let V := popularEndpointFibres S (fun t => t.2.2) (lambda*N/2)
    U ⊆ B ∧ V ⊆ B ∧ lambda*N/2 ≤ (U.card : Real) ∧ lambda*N/2 ≤ (V.card : Real) := by
  classical
  dsimp only
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmass : lambda*Fintype.card (ZMod N)*(N : Real) ≤ (columnTripleRepresentations B T L r a).card := by
    simpa [pow_two, mul_assoc] using hcount
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (popular_endpoint_mem_image _ _ (by positivity) hx)
    exact (columnTripleRepresentations_spec B T L r ht).2.1
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (popular_endpoint_mem_image _ _ (by positivity) hx)
    exact (columnTripleRepresentations_spec B T L r ht).2.2.2.1
  · have h := popular_endpoint_fibres_dense (columnTripleRepresentations B T L r a) (fun t => t.1) hn hl.le
      (fun x => by simpa only [Nat.cast_le] using columnTriple_first_fibre_card_le B T L r a x) hmass
    simpa using h
  · have h := popular_endpoint_fibres_dense (columnTripleRepresentations B T L r a) (fun t => t.2.2) hn hl.le
      (fun x => by simpa only [Nat.cast_le] using columnTriple_last_fibre_card_le B T L r a x) hmass
    simpa using h

end LeanProofs.GowersSzemeredi
