import GowersSzemeredi.Proofs16CoherentFibreClique

/-! Coherent quadruple mass supplies many dense difference graphs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def popularCoherentDifferences {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma kappa : Real) : Finset (ZMod N) := Finset.univ.filter fun a =>
  (kappa/2)*(N : Real)^2 ≤ (coherentDifferenceEdges X B theta F sigma 1 a).card

theorem CoherentFrequencyFamily.density_le_one {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentFrequencyFamily X B theta F sigma Q) (hmass : kappa*(N : Real)^3 ≤ Q.card) :
    kappa ≤ 1 := by
  have hX : (X.card : Real) ≤ N := by exact_mod_cast (show X.card ≤ N by simpa using Finset.card_le_univ X)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hd := (h.point_density hmass).trans hX
  nlinarith

theorem popularCoherentDifferences_dense {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentFrequencyFamily X B theta F sigma Q) (hk : 0 ≤ kappa)
    (hmass : kappa*(N : Real)^3 ≤ Q.card) :
    kappa*N/2 ≤ ((popularCoherentDifferences X B theta F sigma kappa).card : Real) := by
  let D := popularCoherentDifferences X B theta F sigma kappa
  let e := fun a => ((coherentDifferenceEdges X B theta F sigma 1 a).card : Real)
  have he (a : ZMod N) : e a ≤ (N : Real)^2 := by
    dsimp only [e]
    exact_mod_cast (show (coherentDifferenceEdges X B theta F sigma 1 a).card ≤ N^2 by
      simpa only [Fintype.card_prod,ZMod.card,pow_two] using Finset.card_le_univ (coherentDifferenceEdges X B theta F sigma 1 a))
  have hb (a : ZMod N) : e a ≤ (if a ∈ D then (N : Real)^2 else 0)+(kappa/2)*(N : Real)^2 := by
    by_cases ha : a ∈ D
    · rw [if_pos ha]
      exact (he a).trans (le_add_of_nonneg_right (by positivity))
    · rw [if_neg ha,zero_add]
      exact (lt_of_not_ge (fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))).le
  have hsum : (∑ a : ZMod N, e a) = (coherentPairRelations X B theta F sigma 1).card := by
    dsimp only [e]
    exact_mod_cast coherentDifferenceEdges_sum X B theta F sigma 1
  have htotal : (coherentPairRelations X B theta F sigma 1).card ≤
      (D.card : Real)*(N : Real)^2+(N : Real)*((kappa/2)*(N : Real)^2) := by
    rw [← hsum]
    calc _ ≤ ∑ a : ZMod N, ((if a ∈ D then (N : Real)^2 else 0)+(kappa/2)*(N : Real)^2) :=
        Finset.sum_le_sum fun a _ => hb a
      _ = _ := by simp [Finset.sum_add_distrib]
  have hmass' : kappa*(N : Real)^3 ≤ (coherentPairRelations X B theta F sigma 1).card :=
    hmass.trans (Nat.cast_le.mpr h.relation_mass)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
  nlinarith only [hmass',htotal]

end LeanProofs.GowersSzemeredi
