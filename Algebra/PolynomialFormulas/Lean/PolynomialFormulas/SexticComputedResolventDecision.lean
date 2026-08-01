import PolynomialFormulas.SexticRationalRootSearch

/-!
# Executable decisions for irreducible sextic resolvents

This file connects the recursively computed integer coefficient lists to the
degree-15 and degree-10 resolvents in the canonical splitting field.  It then
transfers the finite rational-root search to the exact Galois-theoretic
criterion.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.SexticComputedResolventDecision

open SexticRadicalDecidability
open SexticRadicalDecidability.MonicSextic
open SexticScalarGaloisBridge
open SexticSeparatingInvariants
open SexticEvaluatedResolvents
open SexticComputedResolvents
open SexticSeparatingSearch
open SexticDescriptorGaloisCriterion
open SexticRationalRootSearch

private theorem getD_ofFn_of_lt {α : Type*} {m n : ℕ}
    (v : Fin m → α) (d : α) (hn : n < m) :
    (List.ofFn v).getD n d = v ⟨n, hn⟩ := by
  simp [List.getD, hn]

private theorem getD_ofFn_of_le {α : Type*} {m n : ℕ}
    (v : Fin m → α) (d : α) (hn : m ≤ n) :
    (List.ofFn v).getD n d = d := by
  simp [List.getD, hn]

theorem pairComputedPolynomial_map_eq
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    (toPolynomial (pairComputedCoefficients (f, x))).map
        (Int.castRingHom f.ratPolynomial.SplittingField) =
      pairEvaluatedResolvent x
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree) := by
  ext n
  rw [Polynomial.coeff_map, coeff_toPolynomial]
  by_cases hn : n < 16
  · rw [pairComputedCoefficients, getD_ofFn_of_lt _ _ hn]
    exact pairComputedCoefficient_rootTuple f hp x ⟨n, hn⟩
  · have hle : 16 ≤ n := by omega
    rw [pairComputedCoefficients, getD_ofFn_of_le _ _ hle]
    simp only [map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt <| by
      rw [pairEvaluatedResolvent_natDegree]
      omega).symm

theorem tripleComputedPolynomial_map_eq
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    (toPolynomial (tripleComputedCoefficients (f, x))).map
        (Int.castRingHom f.ratPolynomial.SplittingField) =
      tripleEvaluatedResolvent x
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree) := by
  ext n
  rw [Polynomial.coeff_map, coeff_toPolynomial]
  by_cases hn : n < 11
  · rw [tripleComputedCoefficients, getD_ofFn_of_lt _ _ hn]
    exact tripleComputedCoefficient_rootTuple f hp x ⟨n, hn⟩
  · have hle : 11 ≤ n := by omega
    rw [tripleComputedCoefficients, getD_ofFn_of_le _ _ hle]
    simp only [map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt <| by
      rw [tripleEvaluatedResolvent_natDegree]
      omega).symm

theorem pairComputedPolynomial_monic
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    (toPolynomial (pairComputedCoefficients (f, x))).Monic := by
  apply Polynomial.monic_of_injective
    (Int.castRingHom f.ratPolynomial.SplittingField).injective_int
  rw [pairComputedPolynomial_map_eq f hp x]
  exact pairEvaluatedResolvent_monic _ _

theorem tripleComputedPolynomial_monic
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    (toPolynomial (tripleComputedCoefficients (f, x))).Monic := by
  apply Polynomial.monic_of_injective
    (Int.castRingHom f.ratPolynomial.SplittingField).injective_int
  rw [tripleComputedPolynomial_map_eq f hp x]
  exact tripleEvaluatedResolvent_monic _ _

theorem eval_map_intCast_at_rat {K : Type*} [Field K] [Algebra ℚ K]
    (P : ℤ[X]) (q : ℚ) :
    (P.map (Int.castRingHom K)).eval (algebraMap ℚ K q) =
      algebraMap ℚ K (aeval q P) := by
  have hmap :
      P.map (Int.castRingHom K) =
        (P.map (Int.castRingHom ℚ)).map (algebraMap ℚ K) := by
    rw [Polynomial.map_map]
    congr 1
    exact (RingHom.eq_intCast'
      ((algebraMap ℚ K).comp (Int.castRingHom ℚ))).symm
  rw [hmap, Polynomial.eval_map_algebraMap,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  congr 1
  simpa only [algebraMap_int_eq] using
    (Polynomial.eval_map_algebraMap P q)

theorem hasRationalRoot_iff_map_isRoot {K : Type*}
    [Field K] [Algebra ℚ K] (cs : List ℤ) :
    HasRationalRoot cs ↔
      ∃ q : ℚ, (toPolynomial cs).map (Int.castRingHom K) |>.IsRoot
        (algebraMap ℚ K q) := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [Polynomial.IsRoot.def, eval_map_intCast_at_rat, hq, map_zero]
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [Polynomial.IsRoot.def, eval_map_intCast_at_rat] at hq
    apply (algebraMap ℚ K).injective
    simpa using hq

theorem pairRationalRootSearch_correct
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    rationalRootSearch (pairComputedCoefficients (f, x)) = true ↔
      ∃ q : ℚ,
        (pairEvaluatedResolvent x
          (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)).IsRoot
            (algebraMap ℚ f.ratPolynomial.SplittingField q) := by
  rw [rationalRootSearch_iff _ (pairComputedPolynomial_monic f hp x),
    hasRationalRoot_iff_map_isRoot
      (K := f.ratPolynomial.SplittingField),
    pairComputedPolynomial_map_eq f hp x]

theorem tripleRationalRootSearch_correct
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    rationalRootSearch (tripleComputedCoefficients (f, x)) = true ↔
      ∃ q : ℚ,
        (tripleEvaluatedResolvent x
          (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)).IsRoot
            (algebraMap ℚ f.ratPolynomial.SplittingField q) := by
  rw [rationalRootSearch_iff _ (tripleComputedPolynomial_monic f hp x),
    hasRationalRoot_iff_map_isRoot
      (K := f.ratPolynomial.SplittingField),
    tripleComputedPolynomial_map_eq f hp x]

/-- The executable pair-or-triple resolvent test.  The parameters are supplied
explicitly here; the next layer computes collision-free parameters by an
unbounded recursive search. -/
noncomputable def resolventSolvableB
    (a : MonicSextic × (Fin 2 → ℕ) × (Fin 2 → ℕ)) : Bool :=
  rationalRootSearch (pairComputedCoefficients (a.1, a.2.1)) ||
    rationalRootSearch (tripleComputedCoefficients (a.1, a.2.2))

theorem resolventSolvableB_computable : Computable resolventSolvableB := by
  have hp : Computable fun a : MonicSextic × (Fin 2 → ℕ) × (Fin 2 → ℕ) ↦
      rationalRootSearch (pairComputedCoefficients (a.1, a.2.1)) :=
    rationalRootSearch_primrec.to_comp.comp <|
      pairComputedCoefficients_computable.comp <|
        Computable.pair Computable.fst
          (Computable.fst.comp Computable.snd)
  have ht : Computable fun a : MonicSextic × (Fin 2 → ℕ) × (Fin 2 → ℕ) ↦
      rationalRootSearch (tripleComputedCoefficients (a.1, a.2.2)) :=
    rationalRootSearch_primrec.to_comp.comp <|
      tripleComputedCoefficients_computable.comp <|
        Computable.pair Computable.fst
          (Computable.snd.comp Computable.snd)
  exact (Primrec.or.to_comp.comp hp ht).of_eq fun _ ↦ rfl

theorem resolventSolvableB_correct
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (xp xt : Fin 2 → ℕ)
    (hxp : Function.Injective
      (pairDescriptorValue xp
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)))
    (hxt : Function.Injective
      (tripleDescriptorValue xt
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree))) :
    resolventSolvableB (f, xp, xt) = true ↔
      IsSolvable f.ratPolynomial.Gal := by
  rw [resolventSolvableB, Bool.or_eq_true,
    pairRationalRootSearch_correct f hp xp,
    tripleRationalRootSearch_correct f hp xt]
  exact (gal_isSolvable_iff_separating_resolvents_have_rational_root
    f.ratPolynomial hp f.ratPolynomial_natDegree xp xt hxp hxt).symm

end LeanProofs.PolynomialFormulas.SexticComputedResolventDecision
