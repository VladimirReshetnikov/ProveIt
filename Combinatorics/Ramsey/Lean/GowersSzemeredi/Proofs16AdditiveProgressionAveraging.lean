import GowersSzemeredi.Proofs16AdditiveTranslationParameters

/-! Averaging over additive translations localizes an entire quadruple
family. The retention is governed by the additive energy of the target
set, rather than by four independent choices of dense vertex subsets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_additive_translation_energy {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (P : Finset (ZMod N))
    (hQ : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) :
    ∃ t : Fin 4 → ZMod N, t 0+t 1 = t 2+t 3 ∧
      Q.card*(mappedAdditiveQuadruples P id).card ≤ N^3*(localizedQuadruples Q P t).card := by
  let E := Q ×ˢ mappedAdditiveQuadruples P id
  let code := fun p : (Fin 4 → ZMod N) × (Fin 4 → ZMod N) => quadrupleTranslationCode p.1 p.2
  have hsum : (∑ t : Fin 3 → ZMod N, (E.filter fun p => code p = t).card) = E.card := by
    simpa only [Finset.mem_univ,Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter E Finset.univ code
  have hle : (∑ _t : Fin 3 → ZMod N, E.card) ≤
      ∑ t : Fin 3 → ZMod N, Fintype.card (Fin 3 → ZMod N)*(E.filter fun p => code p = t).card := by
    rw [← Finset.mul_sum,hsum]
    simp
  obtain ⟨t,_,ht⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  have hc : (E.filter fun p => code p = t).card ≤
      (localizedQuadruples Q P (additiveTranslationQuadruple t)).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (localized_quadruple_pair_reconstruct Q P hQ t hp).1
    · intro p hp q hq he
      apply Prod.ext he
      have hp' := (localized_quadruple_pair_reconstruct Q P hQ t hp).2
      have hq' := (localized_quadruple_pair_reconstruct Q P hQ t hq).2
      rw [hp',hq',he]
  refine ⟨additiveTranslationQuadruple t,additiveTranslationQuadruple_additive t,?_⟩
  have h := ht.trans (Nat.mul_le_mul_left (Fintype.card (Fin 3 → ZMod N)) hc)
  simpa only [E,Finset.card_product,Fintype.card_fun,Fintype.card_fin,ZMod.card] using h

theorem exists_additive_translation_count {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (P : Finset (ZMod N))
    (hQ : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) :
    ∃ t : Fin 4 → ZMod N, t 0+t 1 = t 2+t 3 ∧
      Q.card*P.card^4 ≤ N^4*(localizedQuadruples Q P t).card := by
  obtain ⟨t,ht,hcount⟩ := exists_additive_translation_energy Q P hQ
  have hP : P.card^4 ≤ (mappedAdditiveQuadruples P id).card*N := by
    simpa only [ZMod.card] using card_four_le_mapped_additive_quadruples P (id : ZMod N → ZMod N)
  refine ⟨t,ht,?_⟩
  calc Q.card*P.card^4 ≤ Q.card*((mappedAdditiveQuadruples P id).card*N) := Nat.mul_le_mul_left _ hP
    _ = (Q.card*(mappedAdditiveQuadruples P id).card)*N := by ring
    _ ≤ (N^3*(localizedQuadruples Q P t).card)*N := Nat.mul_le_mul_right _ hcount
    _ = _ := by ring

theorem exists_dense_additive_translation {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (P : Finset (ZMod N))
    (hQ : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) {kappa p : Real}
    (hp : 0 ≤ p)
    (hQmass : kappa*(N : Real)^3 ≤ Q.card) (hPmass : p*N ≤ (P.card : Real)) :
    ∃ t : Fin 4 → ZMod N, t 0+t 1 = t 2+t 3 ∧
      (kappa*p^4)*(N : Real)^3 ≤ (localizedQuadruples Q P t).card := by
  obtain ⟨t,ht,hcount⟩ := exists_additive_translation_count Q P hQ
  have hc : (Q.card : Real)*(P.card : Real)^4 ≤ (N : Real)^4*(localizedQuadruples Q P t).card := by
    exact_mod_cast hcount
  have hpow := pow_le_pow_left₀ (show 0 ≤ p*(N : Real) by positivity) hPmass 4
  have hprod := mul_le_mul hQmass hpow (by positivity) (by positivity)
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  refine ⟨t,ht,?_⟩
  apply (mul_le_mul_iff_left₀ (pow_pos hn 4)).mp
  nlinarith only [hprod,hc]

end LeanProofs.GowersSzemeredi
