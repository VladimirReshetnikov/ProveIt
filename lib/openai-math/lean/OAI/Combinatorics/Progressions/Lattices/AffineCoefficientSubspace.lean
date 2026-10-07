import OAI.Combinatorics.Progressions.Estimates.BoundedAmbientModeWitness
import OAI.Combinatorics.Progressions.Estimates.OrderedLayerSplit
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSiteAbsorption

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def integerContractedRow {σ J : Type*}
    (frequency : (σ →₀ ℕ) → J → ℤ) (P : MvPolynomial σ ℤ) : J → ℤ :=
  fun j => ∑ d ∈ P.support, P.coeff d * frequency d j

theorem integerContractedRow_cast {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ)
    (frequency : (σ →₀ ℕ) → J → ℤ) {h : ℕ}
    (hfrequency : ∀ d : σ →₀ ℕ, d.degree = h → ∀ j,
      Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1) = (frequency d j : ℝ))
    {P : MvPolynomial σ ℤ} (hP : P.IsHomogeneous h) (j : J) :
    (integerContractedRow frequency P j : ℝ) = contractedRow Λ (MvPolynomial.map (Int.castRingHom ℝ) P) j := by
  change _ = ((TensorProduct.curry Λ).flip (Pi.single j 1)) (MvPolynomial.map (Int.castRingHom ℝ) P)
  rw [polynomialFunctional_map_expansion]
  simp only [integerContractedRow, Int.cast_sum, Int.cast_mul, Int.coe_castRingHom]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = h := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (MvPolynomial.mem_support_iff.mp hd)
  change _ = ((P.coeff d : ℤ) : ℝ) * Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1)
  rw [hfrequency d hdeg j]

theorem integerContractedRow_coefficientFunctional {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℤ) {P : MvPolynomial σ ℤ} {h : ℕ}
    (hP : P.IsHomogeneous h) (j : J) :
    (integerContractedRow frequency P j : ℝ) = contractedRow
      (coefficientFunctional (fun d j => (frequency d j : ℝ)))
      (MvPolynomial.map (Int.castRingHom ℝ) P) j :=
  integerContractedRow_cast _ frequency (fun d _ j => coefficientFunctional_unit _ d j) hP j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem integer_cube_root_bound {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) {L : ℝ}
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L) :
    ∀ k, |(root k : ℝ)| ≤ L := by
  intro k
  simpa only [affineSite, Finset.sum_empty, add_zero] using hsite ∅ k

theorem integer_cube_difference_bound {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) {L : ℝ}
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L) :
    ∀ i k, |(difference i k : ℝ)| ≤ 2 * L := by
  intro i k
  have he : (difference i k : ℝ) =
      ((affineSite root difference {i} (some k) : ℤ) : ℝ) - (root k : ℝ) := by
    simp [affineSite]
  rw [he]
  have ht := hsite {i} k
  have hr := integer_cube_root_bound root difference hsite k
  exact (abs_sub _ _).trans (by linarith)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem integerCubeWitnessBound_le_polynomial (q : ℕ) {H D : ℝ}
    (hH : 0 ≤ H) (hD : 0 ≤ D) :
    integerCubeWitnessBound q H D ≤
      (q.factorial : ℝ) * (2 + (q : ℝ) * (q + 1)) * (1 + H + D) ^ (q + 2) := by
  let M := 1 + H + D
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hDq : D ^ q ≤ M ^ q := pow_le_pow_left₀ hD (by dsimp [M]; linarith) q
  have hDm : D ^ (q - 1) ≤ M ^ q :=
    (pow_le_pow_left₀ hD (by dsimp [M]; linarith) (q - 1)).trans
      (pow_le_pow_right₀ hM (Nat.sub_le _ _))
  have hHM : 1 + H ≤ M := by dsimp [M]; linarith
  have hA : (q.factorial : ℝ) * D ^ q ≤ (q.factorial : ℝ) * M ^ q :=
    mul_le_mul_of_nonneg_left hDq (Nat.cast_nonneg _)
  have hB : (q : ℝ) * ((q.factorial : ℝ) * D ^ (q - 1) * (1 + H)) ≤
      (q : ℝ) * (q.factorial : ℝ) * M ^ (q + 1) := by
    calc
      _ ≤ (q : ℝ) * ((q.factorial : ℝ) * M ^ q * M) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hfactor : (q : ℝ) * D + 1 ≤ ((q : ℝ) + 1) * M := by
    have hd : D ≤ M := by dsimp [M]; linarith
    nlinarith [show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q]
  have hbase : 2 + H ≤ 2 * M := by dsimp [M]; linarith
  have hpow : M ^ (q + 1) ≤ M ^ (q + 2) := pow_le_pow_right₀ hM (by omega)
  unfold integerCubeWitnessBound integerFormMassBound
  calc
    _ ≤ (q.factorial : ℝ) * M ^ q * (2 * M) +
        (((q : ℝ) + 1) * M) * ((q : ℝ) * (q.factorial : ℝ) * M ^ (q + 1)) := by
      exact add_le_add (mul_le_mul hA hbase (by positivity) (by positivity))
        (mul_le_mul hfactor hB (by positivity) (by positivity))
    _ = 2 * (q.factorial : ℝ) * M ^ (q + 1) +
        ((q : ℝ) * (q + 1) * (q.factorial : ℝ)) * M ^ (q + 2) := by
      simp only [pow_succ]
      ring
    _ ≤ 2 * (q.factorial : ℝ) * M ^ (q + 2) +
        ((q : ℝ) * (q + 1) * (q.factorial : ℝ)) * M ^ (q + 2) := by gcongr
    _ = _ := by dsimp [M]; ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_bounded_integer_mode_witness {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ P : Fin h → MvPolynomial (Option K) ℤ,
      (∀ i, (P i).IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) (P i)) ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, eval (affineSite root difference s) (P i) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, P i) j : ℝ)| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency (∏ i, P i) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨P, hP, hz, hb, w, hw⟩ := exists_bounded_ambient_mode_witness W root difference hlin
    hH hD hC hroot hdiff (VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ)))
    h (VectorPolynomial.coefficientFunctional_rowBound _ hbound) hnonfactor
  have hp : (∏ i, P i).IsHomogeneous h := by
    simpa using IsHomogeneous.prod Finset.univ P (fun _ => 1) (fun i _ => (hP i).1)
  have hcast (j : J) := VectorPolynomial.integerContractedRow_coefficientFunctional frequency hp j
  refine ⟨P, hP, hz, ?_, w, ?_⟩
  · intro j
    rw [hcast j]
    exact hb j
  · simp_rw [hcast]
    exact hw

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem rowPolynomial_homogeneous {σ R : Type*} [Fintype σ] [CommRing R] (a : σ → R) :
    (rowPolynomial a).IsHomogeneous 1 :=
  IsHomogeneous.sum Finset.univ _ 1 (fun i _ => isHomogeneous_C_mul_X (a i) i)

theorem VectorPolynomial.integerContractedRow_apply {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℤ) {P : MvPolynomial σ ℤ} {h : ℕ}
    (hP : P.IsHomogeneous h) (w : J → ℝ) :
    (∑ j, (integerContractedRow frequency P j : ℝ) * w j) =
      coefficientFunctional (fun d j => (frequency d j : ℝ))
        ((MvPolynomial.map (Int.castRingHom ℝ) P) ⊗ₜ[ℝ] w) := by
  simp_rw [integerContractedRow_coefficientFunctional frequency hP]
  exact contractedRow_apply _ _ w

namespace BooleanCubeKernel

theorem exists_bounded_integer_mode_rows {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨P, hP, hz, hb, hw⟩ := exists_bounded_integer_mode_witness W root difference hlin
    hH hD hC hroot hdiff frequency h hbound hnonfactor
  let rows := fun i => polynomialLinearRow (P i)
  have hp (i : Fin h) : rowPolynomial (rows i) = P i :=
    (homogeneous_eq_rowPolynomial _ (hP i).1).symm
  have hprod : (∏ i, rowPolynomial (rows i)) = ∏ i, P i := by simp_rw [hp]
  refine ⟨rows, ?_, ?_, ?_, ?_⟩
  · intro i k
    exact (integer_coefficient_le_mass (P i) (Finsupp.single k 1)).trans (hP i).2
  · intro s
    obtain ⟨i, hi⟩ := hz s
    refine ⟨i, ?_⟩
    change (∑ k, polynomialLinearRow (P i) k * affineSite root difference s k) = 0
    rw [← homogeneous_eval_eq_row _ (hP i).1]
    exact hi
  · rw [hprod]
    exact hb
  · rw [hprod]
    exact hw

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineParameterSubstitution {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (j : I) : MvPolynomial K ℝ :=
  MvPolynomial.C (b none j) + rowPolynomial (fun k => b (some k) j)

theorem dehomogenize_rowPolynomial {K : Type*} [Fintype K] (a : Option K → ℝ) :
    MvPolynomial.aeval dehomogenizingSubstitution (rowPolynomial a) =
      MvPolynomial.C (a none) + rowPolynomial (fun k => a (some k)) := by
  simp [rowPolynomial, dehomogenizingSubstitution, Fintype.sum_option]

theorem affineParameterSubstitution_degree {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (j : I) : (affineParameterSubstitution b j).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  exact max_le (by simp) (rowPolynomial_homogeneous (fun k => b (some k) j)).totalDegree_le

theorem affineParameterSubstitution_eval {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (t : K → ℝ) (j : I) :
    MvPolynomial.aeval t (affineParameterSubstitution b j) =
      b none j + ∑ k, b (some k) j * t k := by
  change MvPolynomial.eval t (affineParameterSubstitution b j) = _
  rw [affineParameterSubstitution, map_add, MvPolynomial.eval_C, rowPolynomial_eval]

noncomputable def affineModeLift {K W : Type*} [AddCommGroup W] [Module ℝ W]
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ :=
  Λ.comp (substitute dehomogenizingSubstitution)

theorem affineModeLift_substitute {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (b : Option K → I → ℝ) :
    affineModeLift Λ (substitute (fun j => rowPolynomial (fun k => b k j)) p) =
      Λ (substitute (affineParameterSubstitution b) p) := by
  rw [affineModeLift, LinearMap.comp_apply, substitute_comp]
  simp only [dehomogenize_rowPolynomial]
  rfl

theorem coefficientModePolynomial_affine_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (b : Option K → I → ℝ) :
    MvPolynomial.eval (fun z => b z.1 z.2) (coefficientModePolynomial (affineModeLift Λ) p) =
      Λ (substitute (affineParameterSubstitution b) p) := by
  rw [coefficientModePolynomial_eval, affineModeLift_substitute]

theorem coefficientModePolynomial_degreeLE {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    {h : ℕ} (hp : DegreeLE (1 : I → ℕ) h p) :
    (coefficientModePolynomial L p).totalDegree ≤ h := by
  unfold coefficientModePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (mapPolynomialCoefficients_degree _ _).trans
  apply parameterPolynomialPullback_degree
  have hb : d.sum (fun _ n => n) ≤ h := by
    simpa only [Finsupp.weight_apply, Pi.one_def, smul_eq_mul, mul_one] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  exact (MvPolynomial.totalDegree_monomial_le d 1).trans hb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem rowPolynomial_integer_site {I K : Type*} [Fintype K]
    (site : K → ℤ) (b : K → I → ℝ) :
    (fun i => MvPolynomial.aeval (fun k => (site k : ℝ)) (rowPolynomial (fun k => b k i))) =
      integerSiteValue site b := by
  funext i
  change MvPolynomial.eval (fun k => (site k : ℝ)) (rowPolynomial (fun k => b k i)) = _
  rw [rowPolynomial_eval]
  change (∑ k, b k i * (site k : ℝ)) = (∑ k, site k • b k) i
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  change b k i * (site k : ℝ) = site k • b k i
  rw [zsmul_eq_mul, mul_comm]

theorem exists_absorbed_integer_site_tests {A I K S : Type*} {W : A → Type*}
    [Fintype A] [Fintype K] [Fintype S] [DecidableEq S]
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℝ (W a)]
    (h : A → ℕ) (site : S → K → ℤ)
    (L : ∀ a, VectorPolynomial K ℝ (W a) →ₗ[ℝ] ℝ)
    (hfactor : ∀ a, ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (h a) q →
        L a q = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (p : ∀ a, VectorPolynomial I ℝ (W a)) (hp : ∀ a, DegreeLE (1 : I → ℕ) (h a) (p a))
    (low : (K → I → ℝ) → ℝ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
      character ((low b + ∑ a, L a (substitute (fun i => rowPolynomial (fun k => b k i)) (p a)) : ℝ) :
        CircleFourier.Circle) * (∏ s, test s (integerSiteValue (site s) b)) =
      character (low b : CircleFourier.Circle) * (∏ s, test' s (integerSiteValue (site s) b)) := by
  have hf (a : A) : ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (h a) q → L a (substitute dehomogenizingSubstitution q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (fun k => (site s k : ℝ))) q) := by
    obtain ⟨M, hM⟩ := hfactor a
    exact ⟨M, (homogeneous_site_factorization_iff (h a)
      (fun s k => (site s k : ℝ)) (L a) M).mpr hM⟩
  obtain ⟨test', ht, he⟩ := exists_absorbed_polynomial_site_tests h
    (fun s k => (site s k : ℝ)) L hf p hp
    (fun (b : K → I → ℝ) i => rowPolynomial (fun k => b k i))
    (fun b i => (rowPolynomial_homogeneous (fun k => b k i)).totalDegree_le) low test htest
  refine ⟨test', ht, ?_⟩
  intro b
  simpa only [rowPolynomial_integer_site] using he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators TensorProduct Classical

def cubeModePolynomialBudget (q : ℕ) (L : ℝ) : ℝ :=
  (q.factorial : ℝ) * (2 + (q : ℝ) * (q + 1)) * (1 + 3 * L) ^ (q + 2)

theorem integerCubeWitnessBound_le_vertex_budget (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    integerCubeWitnessBound q L (2 * L) ≤ cubeModePolynomialBudget q L := by
  have he : 1 + L + 2 * L = 1 + 3 * L := by ring
  simpa only [cubeModePolynomialBudget, he] using
    integerCubeWitnessBound_le_polynomial q hL (show 0 ≤ 2 * L by positivity)

theorem exists_vertex_bounded_integer_mode {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * cubeModePolynomialBudget q L ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨rows, hr, hz, hb, hw⟩ := exists_bounded_integer_mode_rows W root difference hlin
    hL (show 0 ≤ 2 * L by positivity) hC
    (integer_cube_root_bound root difference hsite)
    (integer_cube_difference_bound root difference hsite) frequency h hbound hnonfactor
  have hbudget := integerCubeWitnessBound_le_vertex_budget q hL
  refine ⟨rows, (fun i k => (hr i k).trans hbudget), hz, ?_, hw⟩
  intro j
  exact (hb j).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integerCubeWitnessBound_nonneg q hL (by positivity)) hbudget h) hC)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_dehomogenize {K W : Type*} [AddCommGroup W] [Module ℝ W]
    {h : ℕ} {p : VectorPolynomial (Option K) ℝ W}
    (hp : DegreeLE (1 : Option K → ℕ) h p) :
    DegreeLE (1 : K → ℕ) h (substitute dehomogenizingSubstitution p) := by
  apply degreeLE_substitute_affine _ _ p hp
  intro k
  cases k <;> simp [dehomogenizingSubstitution]

theorem affineModeLift_factorization_iff {K S W : Type*} [AddCommGroup W] [Module ℝ W]
    (h : ℕ) (site : S → K → ℝ) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (M : (S → W) →ₗ[ℝ] ℝ) :
    (∀ q, Homogeneous h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ↔
    (∀ q, DegreeLE (1 : Option K → ℕ) h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) := by
  constructor
  · intro hf q hq
    have ho := (homogeneous_site_factorization_iff h site L M).mp hf
    change L (substitute dehomogenizingSubstitution q) = _
    rw [← siteEvaluation_dehomogenize]
    exact ho _ (degreeLE_dehomogenize hq)
  · intro hf q hq
    exact hf q (homogeneous_degreeLE hq)

theorem affineModeLift_exists_factorization_iff {K S W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (h : ℕ) (site : S → K → ℝ) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) :
    (∃ M : (S → W) →ₗ[ℝ] ℝ, ∀ q, Homogeneous h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ↔
    (∃ M : (S → W) →ₗ[ℝ] ℝ, ∀ q, DegreeLE (1 : Option K → ℕ) h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :=
  exists_congr (fun M => affineModeLift_factorization_iff h site L M)

theorem exists_highest_affine_nonfactor {K S : Type*} {m : ℕ} {W : Fin m → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (site : S → K → ℝ) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (hbad : ∃ i, ¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :
    ∃ i, (¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ∧
      ∀ j, i < j → ∃ M : (S → W j) →ₗ[ℝ] ℝ,
        ∀ q, DegreeLE (1 : Option K → ℕ) (j.val + 1) q → affineModeLift (L j) q =
          M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q) := by
  obtain ⟨i, hi, hh⟩ := exists_highest_exceptional_layer _ hbad
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact (affineModeLift_exists_factorization_iff (j.val + 1) site (L j)).mp (hh j hj)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem exists_absorbed_affine_site_tests {A I K S : Type*} {W : A → Type*}
    [Fintype A] [Fintype K] [Fintype S] [DecidableEq S]
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℝ (W a)]
    (h : A → ℕ) (site : S → K → ℝ)
    (Λ : ∀ a, VectorPolynomial K ℝ (W a) →ₗ[ℝ] ℝ)
    (hfactor : ∀ a, ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (h a) q → affineModeLift (Λ a) q =
        M (siteEvaluation (fun s (i : Option K) => i.elim 1 (site s)) q))
    (p : ∀ a, VectorPolynomial I ℝ (W a)) (hp : ∀ a, DegreeLE (1 : I → ℕ) (h a) (p a))
    (low : (Option K → I → ℝ) → ℝ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
      character ((low b + ∑ a, MvPolynomial.eval (fun z => b z.1 z.2)
        (coefficientModePolynomial (affineModeLift (Λ a)) (p a)) : ℝ) : CircleFourier.Circle) *
        (∏ s, test s (fun i => b none i + ∑ k, b (some k) i * site s k)) =
      character (low b : CircleFourier.Circle) *
        (∏ s, test' s (fun i => b none i + ∑ k, b (some k) i * site s k)) := by
  obtain ⟨test', htest', he⟩ := exists_absorbed_polynomial_site_tests h site Λ hfactor p hp
    affineParameterSubstitution affineParameterSubstitution_degree low test htest
  refine ⟨test', htest', ?_⟩
  intro b
  simpa only [coefficientModePolynomial_affine_eval, affineParameterSubstitution_eval] using he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open CircleFourier MvPolynomial
open scoped BigOperators Classical

def FiniteSitePhaseRemoval {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [AddCommGroup V]
    (site : S → K → ℤ) (rows : Fin h → K → ℤ) : Prop :=
  ∀ (base : K → V) (shift : X → V) (phase : (K → V) → ℝ) (test : S → V → ℂ),
    (∀ s v, ‖test s v‖ ≤ 1) →
    ‖𝔼 x, character (phase (rowShiftedTuple base rows shift x) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character ((additiveBoxDifference h
        (fun x (_ : Unit) => phase (rowShiftedTuple base rows shift x)) u v () : ℝ) : CircleFourier.Circle)‖

theorem finiteSitePhaseRemoval_of_annihilates {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] [AddCommGroup V]
    (hh : 0 < h) (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0) :
    FiniteSitePhaseRemoval (X := X) (V := V) site rows := by
  intro base shift phase test htest
  exact row_shifted_site_phase_cauchySchwarz hh site base rows shift hzero phase test htest

namespace BooleanCubeKernel

theorem exists_vertex_mode_with_phase_removal {K J X V : Type*}
    [Fintype K] [Fintype J] [Fintype X] [Nonempty X] [AddCommGroup V] {q h : ℕ}
    (hh : 0 < h) (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * cubeModePolynomialBudget q L ^ h) ∧
      (∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0) ∧
      FiniteSitePhaseRemoval (X := X) (V := V) (fun s => affineSite root difference s) rows := by
  obtain ⟨rows, hr, hz, hb, hw⟩ := exists_vertex_bounded_integer_mode W root difference hlin
    hL hC hsite frequency h hbound hnonfactor
  exact ⟨rows, hr, hz, hb, hw, finiteSitePhaseRemoval_of_annihilates hh _ rows hz⟩

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem affineModeLift_comp_map {K V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) :
    affineModeLift (L.comp (map f)) = (affineModeLift L).comp (map f) := by
  apply LinearMap.ext
  intro q
  simp only [affineModeLift, LinearMap.comp_apply, map_substitute]

theorem exists_highest_affine_subspace_nonfactor {K S : Type*} {m : ℕ}
    {V : Fin m → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    (U : ∀ j, Submodule ℝ (V j)) (site : S → K → ℝ)
    (L : ∀ j, VectorPolynomial K ℝ (V j) →ₗ[ℝ] ℝ)
    (hbad : ∃ i, ¬∃ M : (S → U i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) (map (U i).subtype q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :
    ∃ i, (¬∃ M : (S → U i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) (map (U i).subtype q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ∧
      ∀ j, i < j → ∃ M : (S → U j) →ₗ[ℝ] ℝ,
        ∀ q, DegreeLE (1 : Option K → ℕ) (j.val + 1) q →
          affineModeLift (L j) (map (U j).subtype q) =
            M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q) := by
  have hh := exists_highest_affine_nonfactor site (fun j => (L j).comp (map (U j).subtype))
    (by simpa only [affineModeLift_comp_map, LinearMap.comp_apply] using hbad)
  simpa only [affineModeLift_comp_map, LinearMap.comp_apply] using hh

end Erdos3.VectorPolynomial

end

end OAI
