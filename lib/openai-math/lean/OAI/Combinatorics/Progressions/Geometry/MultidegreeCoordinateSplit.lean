import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

omit [DecidableEq σ] in
theorem adapted_coefficient_zero_of_coordinate (i : σ) (hi : bound i ≤ 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : σ →₀ ℕ) (ha : 1 < a i) :
    coefficients p a = 0 := by
  have hn : ¬(fun j => a j) ≤ bound := by
    intro h
    exact (not_le_of_gt (hi.trans_lt ha)) (h i)
  have h := hp a
  simpa only [F.terminal _ hn, Submodule.mem_bot] using h

theorem adapted_coefficient_mem_coordinate (i : σ) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted p) (a : σ →₀ ℕ) (ha : 0 < a i) :
    coefficients p a ∈ F.layer (Pi.single i 1) := by
  apply F.antitone (show Pi.single i 1 ≤ fun j => a j from ?_) (hp a)
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Pi.single_eq_same] using (Nat.succ_le_of_lt ha)
  · simp [hj]

theorem split_substitution_add (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p =
      VectorPolynomial.substitute (splitCoordinatePolynomial i u) p +
      VectorPolynomial.substitute (splitCoordinatePolynomial i v) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p :=
  substitute_update_add _ i u v p (F.adapted_coefficient_zero_of_coordinate i hi hp)

theorem split_substitution_sub_mem_coordinate (i : σ)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a ∈ F.layer (Pi.single i 1) :=
  coefficients_substitute_update_sub_mem (F.layer (Pi.single i 1)) _ i u v p
    (F.adapted_coefficient_mem_coordinate i hp) a

theorem split_substitution_adapted (i : σ) (u : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.ordinary.Adapted (fun _ : Option σ => 1)
      (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) :=
  F.ordinary.adapted_substitute (fun _ => 1) (fun _ => 1) _
    (splitCoordinatePolynomial_support i u hu) (F.adapted_ordinary hp)

theorem split_substitution_zero_weighted (i : σ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.WeightedAdapted (omittedCoordinateWeight i) (fun _ : Option σ => 1)
      (VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) :=
  F.weightedAdapted_substitute _ _ _ (splitCoordinatePolynomial_zero_support i) hp

theorem split_substitution_sub_mem_active (i : σ)
    (u : MvPolynomial (Option σ) ℚ) (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : Option σ →₀ ℕ) :
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a ∈
        F.coordinateActiveLayer i (Finsupp.weight (fun _ : Option σ => 1) a) := by
  refine ⟨F.split_substitution_sub_mem_coordinate i u 0 hp a, ?_⟩
  rw [map_sub, Finsupp.sub_apply]
  exact (F.ordinary.layer _).sub_mem
    ((F.ordinary.adapted_iff_coefficients _ _).mp (F.split_substitution_adapted i u hu hp) a)
    ((F.ordinary.adapted_iff_coefficients _ _).mp
      (F.split_substitution_adapted i 0 (Submodule.zero_mem _) hp) a)

end Erdos3.MultidegreeLieFiltration

end

end OAI
