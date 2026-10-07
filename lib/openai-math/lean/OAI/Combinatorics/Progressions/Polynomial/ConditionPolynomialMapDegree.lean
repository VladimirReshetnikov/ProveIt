import OAI.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped Classical BigOperators

variable {I J R S : Type*} [CommRing R] [CommRing S]

theorem conditionPolynomial_totalDegree_le (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) :
    (conditionPolynomial f hf v P).totalDegree ≤ P.totalDegree := by
  let u : I → R := fun i => if i ∈ Set.range f then 0 else v i
  have ht : polynomialTranslate u P ∈ weightedSupportLE (1 : I → ℕ) P.totalDegree := by
    apply weightedSupportLE_aeval (1 : I → ℕ) (1 : I → ℕ)
      (fun i => X i + C (u i))
    · intro i
      exact (weightedSupportLE (1 : I → ℕ) 1).add_mem
        (weightedSupportLE_X _ i) (weightedSupportLE_C _ _ _)
    · exact (mem_weightedSupportLE_one_iff P _).mpr le_rfl
  apply (mem_weightedSupportLE_one_iff _ _).mp
  intro a ha
  change a ∈ (conditionPolynomial f hf v P).support at ha
  have hmem : a.mapDomain f ∈ (polynomialTranslate u P).support := by
    simpa only [conditionPolynomial, u, mem_support_iff, coeff_killCompl] using ha
  have h : Finsupp.weight (fun _ : I => 1) (a.mapDomain f) ≤ P.totalDegree := ht hmem
  change Finsupp.weight (fun _ : J => 1) a ≤ P.totalDegree
  simpa only [← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using h

theorem conditionPolynomial_map (φ : R →+* S) (f : J → I)
    (hf : Function.Injective f) (v : I → R) (P : MvPolynomial I R) :
    map φ (conditionPolynomial f hf v P) =
      conditionPolynomial f hf (fun i => φ (v i)) (map φ P) := by
  unfold conditionPolynomial
  rw [← killCompl_map, polynomialTranslate_map_coefficients]
  apply congrArg (fun u : I → S => killCompl hf (polynomialTranslate u (map φ P)))
  funext i
  split_ifs <;> simp

end Erdos3

end

end OAI
