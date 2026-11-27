import GRHArticle.SingularModuli.PadicDiskRoots

/-!
# Transport of the sparse polynomial disk bound across field extensions

A norm-preserving field embedding maps the disk and its polynomial roots
into the corresponding target disk. The polynomial support is unchanged.
For p-adic fields, the spectral norm supplies the required norm preservation
on embeddings of algebraic extensions.
-/

namespace GRHArticle.SingularModuli

section NormedFieldEmbedding

variable {K L : Type*} [NormedField K] [NormedField L]

/-- A norm-preserving field embedding does not decrease the number of distinct
roots after mapping the polynomial and disk center to the target field. -/
theorem encard_polynomialDiskRoots_le_map (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (P : Polynomial K) (a : K) (R : ℝ) :
    {x : K | ‖x / a - 1‖ ≤ R ∧ P.eval x = 0}.encard ≤
      {y : L | ‖y / f a - 1‖ ≤ R ∧ (P.map f).eval y = 0}.encard := by
  refine Set.encard_le_encard_of_injOn ?_ f.injective.injOn
  intro x hx
  have hnorm : ‖f x / f a - 1‖ = ‖x / a - 1‖ := by
    simpa only [map_sub, map_div₀, map_one] using hf (x / a - 1)
  change ‖f x / f a - 1‖ ≤ R ∧ (P.map f).eval (f x) = 0
  refine ⟨hnorm ▸ hx.1, ?_⟩
  rw [Polynomial.eval_map_apply, hx.2, map_zero]

end NormedFieldEmbedding

section Padic

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The disk bound descends along a norm-preserving embedding into the p-adic
complex field, with the original polynomial's number of nonzero coefficients. -/
theorem encard_polynomialDiskRoots_le_of_padicComplexEmbedding {K : Type*}
    [NormedField K] (f : K →+* ℂ_[p]) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (P : Polynomial K) (hP : P ≠ 0) (a : K) (ha : a ≠ 0) {r : ℚ}
    (hr : 1 / ((p : ℚ) - 1) < r) :
    {x : K | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ P.eval x = 0}.encard ≤
      sparseDiskRootBound p P.support.card r
        (Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)) hr := by
  have hP' : P.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hP
  have bound := encard_polynomialDiskRoots_le (P.map f) hP' (f a) ((map_ne_zero f).mpr ha) hr
  apply (encard_polynomialDiskRoots_le_map f hf P a _).trans
  simpa only [Polynomial.support_map_of_injective P f.injective] using bound

/-- The disk root bound on the algebraic closure uses the norm induced by the
p-adic rationals. -/
theorem encard_polynomialDiskRoots_le_padicAlgCl
    (P : Polynomial (PadicAlgCl p)) (hP : P ≠ 0) (a : PadicAlgCl p) (ha : a ≠ 0)
    {r : ℚ} (hr : 1 / ((p : ℚ) - 1) < r) :
    {x : PadicAlgCl p | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ P.eval x = 0}.encard ≤
      sparseDiskRootBound p P.support.card r
        (Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)) hr :=
  encard_polynomialDiskRoots_le_of_padicComplexEmbedding (algebraMap (PadicAlgCl p) ℂ_[p])
    (PadicComplex.norm_extends p) P hP a ha hr

/-- Every intermediate field of the p-adic algebraic closure inherits the
bound under its induced norm. -/
theorem encard_polynomialDiskRoots_le_padicIntermediateField
    (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (P : Polynomial E) (hP : P ≠ 0) (a : E) (ha : a ≠ 0)
    {r : ℚ} (hr : 1 / ((p : ℚ) - 1) < r) :
    {x : E | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ P.eval x = 0}.encard ≤
      sparseDiskRootBound p P.support.card r
        (Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)) hr :=
  encard_polynomialDiskRoots_le_of_padicComplexEmbedding
    ((algebraMap (PadicAlgCl p) ℂ_[p]).comp E.val.toRingHom)
    (fun x => PadicComplex.norm_extends p (x : PadicAlgCl p)) P hP a ha hr

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [Algebra.IsAlgebraic ℚ_[p] K]

/-- The norm on an algebraic normed extension agrees with the spectral norm.
Algebra embeddings into the p-adic algebraic closure preserve it. -/
theorem norm_padicAlgCl_algHom (f : K →ₐ[ℚ_[p]] PadicAlgCl p) (x : K) : ‖f x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq p (f x), NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x]
  unfold spectralNorm
  rw [minpoly.algHom_eq f f.injective]

/-- The disk bound holds in every algebraic normed extension of the p-adic
rationals, in particular every finite extension with its extending norm. -/
theorem encard_polynomialDiskRoots_le_padicAlgebraicExtension
    (P : Polynomial K) (hP : P ≠ 0) (a : K) (ha : a ≠ 0) {r : ℚ}
    (hr : 1 / ((p : ℚ) - 1) < r) :
    {x : K | ‖x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ P.eval x = 0}.encard ≤
      sparseDiskRootBound p P.support.card r
        (Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)) hr := by
  let f : K →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
  exact encard_polynomialDiskRoots_le_of_padicComplexEmbedding
    ((algebraMap (PadicAlgCl p) ℂ_[p]).comp f.toRingHom)
    (fun x => (PadicComplex.norm_extends p (f x)).trans (norm_padicAlgCl_algHom f x))
    P hP a ha hr

end Padic

end GRHArticle.SingularModuli
