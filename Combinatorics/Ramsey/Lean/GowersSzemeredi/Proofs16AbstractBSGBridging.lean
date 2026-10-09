import GowersSzemeredi.Proofs16AbstractBSGWords
import GowersSzemeredi.Proofs16ThresholdWordDensity

/-! The bridging induction for arbitrary quadruple relations. The same
cubic density recurrence used for exact column maps applies to bounded-image
relations; no model packing or elimination is used. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Convert Claim 4.4's tuple convention to the splice convention. -/
theorem mixedRelationQuadruples_card {N : Nat} [NeZero N]
    (U V : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) :
    (mixedRelationQuadruples U V R).card =
      ((U ×ˢ U ×ˢ V ×ˢ V).filter fun q =>
        q.1 - q.2.1 = q.2.2.1 - q.2.2.2 ∧ R q.1 q.2.1 q.2.2.1 q.2.2.2).card := by
  refine Finset.card_bij (fun q _ => (q 0, q 2, q 3, q 1)) ?_ ?_ ?_
  · intro q hq
    obtain ⟨_, h0, h2, h1, h3, he, hr⟩ := Finset.mem_filter.mp hq
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨h0, h2, h3, h1⟩, by linear_combination he, hr⟩
  · intro q _ p _ he
    simp only [Prod.mk.injEq] at he
    funext i; fin_cases i
    · exact he.1
    · exact he.2.2.2
    · exact he.2.1
    · exact he.2.2.1
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h0, h2, h3, h1⟩, he, hr⟩ := hp
    refine ⟨![p.1, p.2.2.2, p.2.1, p.2.2.1], ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change p.1 ∈ U ∧ p.2.1 ∈ U ∧ p.2.2.2 ∈ V ∧ p.2.2.1 ∈ V ∧
      p.1 + p.2.2.2 = p.2.1 + p.2.2.1 ∧ R p.1 p.2.1 p.2.2.1 p.2.2.2
    exact ⟨h0, h2, h1, h3, by linear_combination he, hr⟩

/-- Fixed additive value bounds a triple's last-endpoint fibre by `N`. -/
theorem relationTriple_last_fibre_card_le {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (a x : ZMod N) :
    ((relationTripleRepresentations B R a).filter fun t => t.2.2 = x).card ≤ N := by
  have h := Finset.card_le_card_of_injOn
    (s := (relationTripleRepresentations B R a).filter fun t => t.2.2 = x)
    (t := (Finset.univ : Finset (ZMod N))) (fun t => t.2.1) (by simp) (by
      intro p hp q hq hm
      have hlast := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      have hpidx := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      have hqidx := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
      have hfirst : p.1 = q.1 := by linear_combination -hpidx + hqidx + hm - hlast
      exact Prod.ext hfirst (Prod.ext hm hlast))
  simpa using h

theorem relationTriple_popular_last {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (a : ZMod N) {lambda : Real} (hl : 0 < lambda)
    (hcount : lambda * (N : Real)^2 ≤ (relationTripleRepresentations B R a).card) :
    let U := popularEndpointFibres (relationTripleRepresentations B R a)
      (fun t => t.2.2) (lambda*N/2)
    U ⊆ B ∧ lambda*N/2 ≤ (U.card : Real) := by
  dsimp only
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp
      (popular_endpoint_mem_image _ _ (by positivity) hx)
    exact (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2).2
  · have hmass : lambda * Fintype.card (ZMod N) * (N : Real) ≤
        (relationTripleRepresentations B R a).card := by
      simpa [pow_two, mul_assoc] using hcount
    have h := popular_endpoint_fibres_dense (relationTripleRepresentations B R a)
      (fun t => t.2.2) hn hl.le
      (fun x => by exact_mod_cast relationTriple_last_fibre_card_le B R a x) hmass
    simpa using h

def ThresholdRelationRichness {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) (beta eta : Real) : Prop :=
  ∀ U V : Finset (ZMod N), U ⊆ B → V ⊆ B →
    ∀ beta1 beta2 : Real, beta ≤ beta1 → beta ≤ beta2 →
      beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
      (beta1*beta2*eta)^2*(N : Real)^3/2 ≤ (mixedRelationQuadruples U V R).card

theorem relation_word_representations_step {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (Rel : ZMod N → ZMod N → ZMod N → ZMod N → Prop) (a b : ZMod N) (as : List (ZMod N))
    {lambda delta eta beta : Real} (hl : 0 < lambda) (hd : 0 < delta)
    (ha : lambda*(N : Real)^2 ≤ (relationTripleRepresentations B Rel a).card)
    (hb : delta*(N : Real)^(3*as.length+2) ≤ (relationWordRepresentations B Rel (b::as)).card)
    (hrich : ThresholdRelationRichness B Rel beta eta)
    (hcutA : beta ≤ lambda/2) (hcutB : beta ≤ delta/2) :
    eta^2*lambda^3*delta^3/128*(N : Real)^(3*as.length+5) ≤
      (relationWordRepresentations B Rel (a::b::as)).card := by
  let S := relationTripleRepresentations B Rel a
  let R := relationWordRepresentations B Rel (b::as)
  let U := popularEndpointFibres S (fun y => y.2.2) (lambda*N/2)
  let V := popularEndpointFibres R (fun z => z.1.1) (delta*(N : Real)^(3*as.length+1)/2)
  have hpopA := relationTriple_popular_last B Rel a hl ha
  have hval : ∀ z ∈ R, columnWordValue z = columnAnchorEval id (b::as) :=
    fun z hz => (relationWordRepresentations_spec B Rel (b::as) z hz).2
  have hpopB := columnWord_popular_first (k := as.length) R B (columnAnchorEval id (b::as)) hd hval
    (fun z hz => (relationWordRepresentations_spec B Rel (b::as) z hz).1.1) hb
  have hUB : U ⊆ B := hpopA.1
  have hVB : V ⊆ B := hpopB.1
  have hU : (lambda/2)*N ≤ (U.card : Real) := by simpa only [div_mul_eq_mul_div] using hpopA.2
  have hV : (delta/2)*N ≤ (V.card : Real) := by simpa only [V, List.length_cons, div_mul_eq_mul_div] using hpopB.2
  let Q := mixedRelationQuadruples U V Rel
  have hQ := hrich U V hUB hVB (lambda/2) (delta/2) hcutA hcutB hU hV
  let D := fibreGluings Q S R (fun y => y.2.2) (fun z => z.1.1) (fun q => q 2) (fun q => q 1)
  have hD : (Q.card : Real)*(lambda*N/2)*(delta*(N : Real)^(3*as.length+1)/2) ≤ (D.card : Real) := by
    apply fibreGluings_card_lower Q S R _ _ _ _ (by positivity)
    · intro q hq
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2.2.1).2
    · intro q hq
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2.2.2.1).2
  have hmass : eta^2*lambda^3*delta^3/128*(N : Real)^(3*as.length+5) ≤ (D.card : Real) := by
    calc _ = ((lambda/2*(delta/2)*eta)^2*(N : Real)^3/2) *
        ((lambda*N/2)*(delta*(N : Real)^(3*as.length+1)/2)) := by
          simp only [pow_add, pow_one]; ring
      _ ≤ (Q.card : Real)*((lambda*N/2)*(delta*(N : Real)^(3*as.length+1)/2)) :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ _ := by simpa only [mul_assoc] using hD
  have hsub : D.image columnWordSplice ⊆ relationWordRepresentations B Rel (a::b::as) := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hprod,hy,hz⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hpair⟩ := Finset.mem_product.mp hprod
    obtain ⟨hyrep,hzrep⟩ := Finset.mem_product.mp hpair
    obtain ⟨_, h0, h2, h1, h3, he, hr⟩ := Finset.mem_filter.mp hq
    have hqB : p.1 ∈ mixedRelationQuadruples B B Rel :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUB h0, hUB h2, hVB h1, hVB h3, he, hr⟩
    exact relationWordSplice_mem B Rel a b as hqB hyrep hzrep hy hz
  have hinj := columnWordSplice_injOn (k := as.length) Q S R a (columnAnchorEval id (b::as))
    (fun y hy => (Finset.mem_filter.mp hy).2.1) hval
  have hcard : D.card ≤ (relationWordRepresentations B Rel (a::b::as)).card := by
    have hi : (D.image columnWordSplice).card = D.card := by
      simpa only [D, List.length_cons] using Finset.card_image_of_injOn hinj
    rw [← hi]
    exact Finset.card_le_card hsub
  exact hmass.trans (Nat.cast_le.mpr hcard)


/-- Every nonempty list of popular anchors has a dense compatible family. -/
theorem relation_word_representations_count {N : Nat} [NeZero N]
    (B P : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) {lambda eta beta : Real}
    (hl : 0 < lambda) (he : 0 < eta)
    (hP : ∀ a ∈ P, lambda*(N : Real)^2 ≤ (relationTripleRepresentations B R a).card)
    (hrich : ThresholdRelationRichness B R beta eta)
    (K : Nat) (hcut : ∀ j ≤ K, beta ≤ thresholdColumnWordDensity lambda eta j/2)
    (a : ZMod N) (as : List (ZMod N)) (has : ∀ x ∈ a::as, x ∈ P) (hsize : as.length ≤ K) :
    thresholdColumnWordDensity lambda eta as.length*(N : Real)^(3*as.length+2) ≤
      (relationWordRepresentations B R (a::as)).card := by
  induction as generalizing a with
  | nil =>
    have hcard : (relationTripleRepresentations B R a).card ≤
        (relationWordRepresentations B R [a]).card := by
      apply Finset.card_le_card_of_injOn (fun t => (t,()))
      · intro t ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
      · intro t _ u _ heq
        exact congrArg Prod.fst heq
    exact (hP a (has a (by simp))).trans (by exact_mod_cast hcard)
  | cons b as ih =>
    have hb := ih b (fun x hx => has x (by simp only [List.mem_cons] at hx ⊢; exact Or.inr hx)) (by simp only [List.length_cons] at hsize; omega)
    have ha := hP a (has a (by simp))
    have h := relation_word_representations_step B R a b as hl
      (thresholdColumnWordDensity_pos hl he as.length) ha hb hrich (hcut 0 (Nat.zero_le _))
      (hcut as.length (by simp only [List.length_cons] at hsize; omega))
    simpa [thresholdColumnWordDensity, Nat.mul_add, Nat.add_assoc] using h

end LeanProofs.GowersSzemeredi
