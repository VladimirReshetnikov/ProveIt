import GowersSzemeredi.Proofs16ColumnWordRepresentations

/-! The induction step for compatible words keeps the two input densities
separate, avoiding a loss from replacing them by their minimum. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem column_word_representations_step {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a b : ZMod N) (as : List (ZMod N))
    {lambda delta eta : Real} (hl : 0 < lambda) (hd : 0 < delta)
    (ha : lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card)
    (hb : delta*(N : Real)^(3*as.length+2) ≤ (columnWordRepresentations B T L r (b::as)).card)
    (hrich : ∀ U V : Finset (ZMod N), U ⊆ B → V ⊆ B →
      ∀ beta1 beta2 : Real, 0 ≤ beta1 → 0 ≤ beta2 →
        beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
        (beta1*beta2*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real)) :
    eta^2*lambda^3*delta^3/64*(N : Real)^(3*as.length+5) ≤
      (columnWordRepresentations B T L r (a::b::as)).card := by
  let S := columnTripleRepresentations B T L r a
  let R := columnWordRepresentations B T L r (b::as)
  let U := popularEndpointFibres S (fun y => y.2.2) (lambda*N/2)
  let V := popularEndpointFibres R (fun z => z.1.1) (delta*(N : Real)^(3*as.length+1)/2)
  have hpopA := columnTriple_popular_endpoints B T L r a hl ha
  have hval : ∀ z ∈ R, columnWordValue z = columnAnchorEval id (b::as) :=
    fun z hz => (columnWordRepresentations_spec B T L r (b::as) z hz).2.1
  have hpopB := columnWord_popular_first (k := as.length) R B (columnAnchorEval id (b::as)) hd hval
    (fun z hz => (columnWordRepresentations_spec B T L r (b::as) z hz).1.1) hb
  have hUB : U ⊆ B := hpopA.2.1
  have hVB : V ⊆ B := hpopB.1
  have hU : (lambda/2)*N ≤ (U.card : Real) := by simpa only [div_mul_eq_mul_div] using hpopA.2.2.2
  have hV : (delta/2)*N ≤ (V.card : Real) := by simpa only [V, List.length_cons, div_mul_eq_mul_div] using hpopB.2
  let Q := mixedExactColumnQuadruples U V T L r
  have hQ := hrich U V hUB hVB (lambda/2) (delta/2) (by positivity) (by positivity) hU hV
  let D := fibreGluings Q S R (fun y => y.2.2) (fun z => z.1.1) (fun q => q 2) (fun q => q 1)
  have hD : (Q.card : Real)*(lambda*N/2)*(delta*(N : Real)^(3*as.length+1)/2) ≤ (D.card : Real) := by
    apply fibreGluings_card_lower Q S R _ _ _ _ (by positivity)
    · intro q hq
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2.2.1).2
    · intro q hq
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2.2.2.1).2
  have hmass : eta^2*lambda^3*delta^3/64*(N : Real)^(3*as.length+5) ≤ (D.card : Real) := by
    calc _ = ((lambda/2*(delta/2)*eta)^2*(N : Real)^3) *
        ((lambda*N/2)*(delta*(N : Real)^(3*as.length+1)/2)) := by
          simp only [pow_add, pow_one]; ring
      _ ≤ (Q.card : Real)*((lambda*N/2)*(delta*(N : Real)^(3*as.length+1)/2)) :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ _ := by simpa only [mul_assoc] using hD
  have hsub : D.image columnWordSplice ⊆ columnWordRepresentations B T L r (a::b::as) := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hprod,hy,hz⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hpair⟩ := Finset.mem_product.mp hprod
    obtain ⟨hyrep,hzrep⟩ := Finset.mem_product.mp hpair
    have hqB := exactColumnQuadruples_mono (Finset.union_subset hUB hVB) T L r (Finset.mem_filter.mp hq).1
    exact columnWordSplice_mem B T L r a b as hqB hyrep hzrep hy hz
  have hinj := columnWordSplice_injOn (k := as.length) Q S R a (columnAnchorEval id (b::as))
    (fun y hy => (columnTripleRepresentations_spec B T L r hy).2.2.2.2.1) hval
  have hcard : D.card ≤ (columnWordRepresentations B T L r (a::b::as)).card := by
    have hi : (D.image columnWordSplice).card = D.card := by
      simpa only [D, List.length_cons] using Finset.card_image_of_injOn hinj
    rw [← hi]
    exact Finset.card_le_card hsub
  exact hmass.trans (Nat.cast_le.mpr hcard)

end LeanProofs.GowersSzemeredi
