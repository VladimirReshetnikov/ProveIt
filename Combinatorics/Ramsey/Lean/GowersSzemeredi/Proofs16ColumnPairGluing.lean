import GowersSzemeredi.Proofs16ColumnPairSplice

/-! Dense triple families and hereditary exact richness give many
compatible six-entry representations of a pair of columns. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem column_pair_representations_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a b : ZMod N) {lambda eta : Real}
    (hl : 0 < lambda)
    (ha : lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card)
    (hb : lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r b).card)
    (hrich : ∀ U V : Finset (ZMod N), U ⊆ B → V ⊆ B →
      ∀ beta1 beta2 : Real, 0 ≤ beta1 → 0 ≤ beta2 →
        beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
        (beta1*beta2*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real)) :
    eta^2*lambda^6/64*(N : Real)^5 ≤ (columnPairRepresentations B T L r a b).card := by
  let S := columnTripleRepresentations B T L r a
  let R := columnTripleRepresentations B T L r b
  let U := popularEndpointFibres S (fun y => y.2.2) (lambda*N/2)
  let V := popularEndpointFibres R (fun z => z.1) (lambda*N/2)
  have hpopA := columnTriple_popular_endpoints B T L r a hl ha
  have hpopB := columnTriple_popular_endpoints B T L r b hl hb
  have hUB : U ⊆ B := hpopA.2.1
  have hVB : V ⊆ B := hpopB.1
  have hU : (lambda/2)*N ≤ (U.card : Real) := by simpa only [div_mul_eq_mul_div] using hpopA.2.2.2
  have hV : (lambda/2)*N ≤ (V.card : Real) := by simpa only [div_mul_eq_mul_div] using hpopB.2.2.1
  let Q := mixedExactColumnQuadruples U V T L r
  have hQ := hrich U V hUB hVB (lambda/2) (lambda/2) (by positivity) (by positivity) hU hV
  let D := fibreGluings Q S R (fun y => y.2.2) (fun z => z.1) (fun q => q 2) (fun q => q 1)
  have hD : (Q.card : Real)*(lambda*N/2)*(lambda*N/2) ≤ (D.card : Real) := by
    apply fibreGluings_card_lower Q S R _ _ _ _ (by positivity)
    · intro q hq
      have hqU := (Finset.mem_filter.mp hq).2.2.1
      exact (Finset.mem_filter.mp hqU).2
    · intro q hq
      have hqV := (Finset.mem_filter.mp hq).2.2.2.1
      exact (Finset.mem_filter.mp hqV).2
  have hmass : eta^2*lambda^6/64*(N : Real)^5 ≤ (D.card : Real) := by
    have h := mul_le_mul_of_nonneg_right hQ (sq_nonneg (lambda*(N : Real)/2))
    nlinarith [hD]
  have hsub : D.image columnPairSplice ⊆ columnPairRepresentations B T L r a b := by
    intro s hs
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hprod,hy,hz⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hpair⟩ := Finset.mem_product.mp hprod
    obtain ⟨hyrep,hzrep⟩ := Finset.mem_product.mp hpair
    have hqB := exactColumnQuadruples_mono (Finset.union_subset hUB hVB) T L r (Finset.mem_filter.mp hq).1
    exact columnPairSplice_mem B T L r a b hqB hyrep hzrep hy hz
  have hcard : D.card ≤ (columnPairRepresentations B T L r a b).card := by
    rw [← Finset.card_image_of_injOn (columnPairSplice_injOn B T L r a b Q)]
    exact Finset.card_le_card hsub
  exact hmass.trans (Nat.cast_le.mpr hcard)

end LeanProofs.GowersSzemeredi
