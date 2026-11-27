import Lib.Adelic.TraceFormula.Convergence
import Lib.Adelic.TraceFormula.CoprimeFactors

/-!
# The geometric side, polynomial by polynomial

The geometric side of the trace formula is the integral over `x ∈ [G]` of the sum of the values
of `k ⊗ φ` at `x⁻¹ γ x`, over the rational points `γ`. For a cusp kernel `k` of large enough order
it is the sum of the parts given by the characteristic polynomials `R` of the `γ`. If moreover `φ`
is cuspidal at one split place and, on its support, `0` is a simple root of the characteristic
polynomial modulo a place `w'`, then the part of an `R` that is not irreducible is `0`.

Notions from other files:
* `Space E n s`: a hermitian space `V` over `E`, with a matrix `V.J` and an adelic point;
  `U V.J` is its group of rational points and `V.ratEmbed` maps that group into `G E s`.
* `G E s`: the adelic unitary group, with factors `GInf E s` at the infinite places and `Gf E n`
  at the finite ones; `V.Γ` is the image of `U V.J` in it and `V.quotMeasure` computes integrals
  over the quotient `[G] = V.Γ \ G E s`.
* `V.polyTerm k φ S γ x`: the value of `k ⊗ φ` at `x⁻¹ γ x` if the characteristic polynomial of
  `γ` lies in `S`, and `0` otherwise.
* `IsCuspKernel B k`: the kernel `k` on `GInf E s` is a minimal idempotent for convolution that is
  reproduced by a compactly supported function and decays to order `B`.
* `IsCuspidalAt hw φ`: at the split place `w` the sums of the translates of `φ` over the unipotent
  radicals of the proper parabolic subgroups over the residue field vanish.

Part of a known result: Comparison of simple trace formulas for unitary groups that differ only at
real places. See `Lib.Adelic.TraceFormula.TraceComparison`.
-/

open MeasureTheory Matrix Polynomial Filter Topology

noncomputable section

namespace New

/-- A monic polynomial that is neither irreducible nor a proper power is a product of two coprime
polynomials of positive degree. -/
lemma exists_isCoprime_mul_of_not_irreducible {F : Type} [Field F] {R : F[X]} (h_monic : R.Monic)
    (h_red : ¬Irreducible R) (h_pow : ∀ (Q : F[X]) (j : ℕ), 1 < j → R ≠ Q ^ j) :
    ∃ A B : F[X], IsCoprime A B ∧ ¬IsUnit A ∧ ¬IsUnit B ∧ R = A * B := by
  have h_not_unit : ¬IsUnit R := fun h_unit ↦
    h_pow 1 2 one_lt_two (by simp [h_monic.isUnit_iff.1 h_unit])
  -- Split off the largest power of a monic irreducible factor `Q`.
  obtain ⟨Q, hQ_monic, hQ_irred, hQ_dvd⟩ := R.exists_monic_irreducible_factor h_not_unit
  obtain ⟨i, A, h_not_dvd, rfl⟩ : ∃ (i : ℕ) (A : F[X]), ¬Q ∣ A ∧ R = Q ^ i * A :=
    WfDvdMonoid.max_power_factor h_monic.ne_zero hQ_irred
  have hi : i ≠ 0 := fun hi ↦ h_not_dvd (by simpa [hi] using hQ_dvd)
  refine ⟨Q ^ i, A, (hQ_irred.coprime_iff_not_dvd.2 h_not_dvd).pow_left,
    mt (isUnit_pow_iff hi).1 hQ_irred.not_isUnit, fun h_unit ↦ ?_, rfl⟩
  obtain rfl : A = 1 := ((hQ_monic.pow i).of_mul_monic_left h_monic).isUnit_iff.1 h_unit
  obtain rfl | hi_gt : i = 1 ∨ 1 < i := by omega
  · exact h_red (by simpa using hQ_irred)
  · exact h_pow Q i hi_gt (mul_one _)

namespace Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  (V : Space E n s) {B : ℕ} {k : GInf E s → ℂ}

/-- Let `γ` be a rational point of the space `V`, embedded by `V.ratEmbed` in the adelic group, and
`x` an adelic point. At a finite place `w`, the characteristic polynomial of the component of
`x⁻¹ γ x` is the image over the completion `LocField w` of the characteristic polynomial of `γ`. -/
lemma charpoly_atPlace_conj_ratEmbed (w : FinPlace E) (γ : U V.J) (x : G E s) :
    ((x⁻¹ * V.ratEmbed γ * x).2.atPlace w).1.charpoly
      = (γ : Matrix n n E).charpoly.map (algebraMap E (LocField w)) := by
  set y : Gf E n := (x⁻¹ * V.ratEmbed γ * x).2
  -- Over the finite adeles, `y` is conjugate to the image of `γ`.
  set z : GL n (𝔸f E) := V.xFin * x.2
  have h_conj : (y : GL n (𝔸f E)) =
      z⁻¹ * GeneralLinearGroup.map (algebraMap E (𝔸f E)) γ.1 * z := by
    change (x.2 : GL n (𝔸f E))⁻¹ * V.embFin γ * x.2 = _
    simp [z, coe_embFin, mul_assoc]
  calc _ = (y : Matrix n n (𝔸f E)).charpoly.map (evalAt w) := charpoly_map _ _
    _ = ((γ : Matrix n n E).map (algebraMap E (𝔸f E))).charpoly.map (evalAt w) := by
      rw [h_conj, Units.val_mul, Units.val_mul, coe_units_inv, charpoly_units_conj']
      rfl
    _ = (γ : Matrix n n E).charpoly.map (algebraMap E (LocField w)) := by
      rw [charpoly_map, Polynomial.map_map]
      rfl

/-- For a set `S` of polynomials, the sum of `V.polyTerm k φ S γ x` over the rational points `γ`,
that is, of the values of `k ⊗ φ` at `x⁻¹ γ x` for the `γ` with characteristic polynomial in `S`,
does not change when `x` is multiplied on the left by a rational point `δ`. -/
lemma tsum_polyTerm_ratEmbed_mul (φ : Gf E n → ℂ) (S : Set E[X]) (δ : U V.J) (x : G E s) :
    ∑' γ : U V.J, V.polyTerm k φ S γ (V.ratEmbed δ * x) = ∑' γ : U V.J, V.polyTerm k φ S γ x := by
  rw [← (MulAut.conj δ).toEquiv.tsum_eq]
  refine tsum_congr fun γ ↦ ?_
  have h_charpoly : ((δ * γ * δ⁻¹ : U V.J) : Matrix n n E).charpoly =
      (γ : Matrix n n E).charpoly := by
    simp
  have h_point : (V.ratEmbed δ * x)⁻¹ * V.ratEmbed (δ * γ * δ⁻¹) * (V.ratEmbed δ * x)
      = x⁻¹ * V.ratEmbed γ * x := by simp [mul_assoc]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, kernelTerm,
    h_charpoly, h_point]

variable [Nonempty n]

omit [Nonempty n] in
/-- For a measurable `k` and a test function `φ`, the sum of the values of `k ⊗ φ` at `x⁻¹ γ x`,
over the rational points `γ` with characteristic polynomial in `S`, is measurable in `x`. -/
lemma measurable_tsum_polyTerm (hk : Measurable k) (φ : TestFunction (Gf E n)) (S : Set E[X]) :
    Measurable fun x : G E s ↦ ∑' γ : U V.J, V.polyTerm k φ S γ x := by
  fun_prop

/-- Let `k` be a cusp kernel of order `B ≥ 13 * card n ^ 3` (`IsCuspKernel`), and `φ` a test
function. The sum of the values of `k ⊗ φ` at `x⁻¹ γ x`, over the rational points `γ` with
characteristic polynomial in `S`, is integrable in `x` over the quotient `[G]` of the adelic
group by the rational points, for the measure `V.quotMeasure`. -/
lemma integrable_tsum_polyTerm (hB : 13 * Fintype.card n ^ 3 ≤ B) (he : IsCuspKernel B k)
    (φ : TestFunction (Gf E n)) (S : Set E[X]) :
    Integrable (fun x : G E s ↦ ∑' γ : U V.J, V.polyTerm k φ S γ x) V.quotMeasure := by
  obtain ⟨D, hD⟩ := V.exists_norm_tsum_polyTerm_le hB φ he
  exact .of_bound (V.measurable_tsum_polyTerm he.continuous.measurable φ S).aestronglyMeasurable D
    (.of_forall fun x ↦ hD x S)

/-- The part of the geometric side given by the polynomials in `S`: the integral over `[G]` of the
sum of the values of `k ⊗ φ` at `x⁻¹ γ x`, over the rational points `γ` whose characteristic
polynomial lies in `S`. Here `k` is a cusp kernel of order `B ≥ 13 * card n ^ 3`, so the sum is
integrable. It is a linear form in the test function `φ : TestFunction (Gf E n)`, which has an
underlying function `φ.1 : Gf E n → ℂ`. -/
def geometricSide (hB : 13 * Fintype.card n ^ 3 ≤ B) (he : IsCuspKernel B k) (S : Set E[X]) :
    TestFunction (Gf E n) →ₗ[ℂ] ℂ where
  toFun φ := ∫ x : G E s, ∑' γ : U V.J, V.polyTerm k φ S γ x ∂V.quotMeasure
  map_add' φ ψ := by
    rw [← integral_add (V.integrable_tsum_polyTerm hB he φ S)
      (V.integrable_tsum_polyTerm hB he ψ S)]
    congr with x
    rw [← (V.summable_polyTerm hB φ he.decay S x).tsum_add (V.summable_polyTerm hB ψ he.decay S x)]
    simp [kernelTerm, mul_add]
  map_smul' c φ := by
    simp [← integral_const_mul, ← tsum_mul_left, kernelTerm, mul_left_comm _ c]

/-- The value of the linear form `geometricSide` at `φ`, as an integral over `[G]`. -/
lemma geometricSide_apply (hB : 13 * Fintype.card n ^ 3 ≤ B) (he : IsCuspKernel B k)
    (S : Set E[X]) (φ : TestFunction (Gf E n)) : V.geometricSide hB he S φ =
      ∫ x : G E s, ∑' γ : U V.J, V.polyTerm k φ S γ x ∂V.quotMeasure := rfl

/-- Let `k` be a cusp kernel of order `B ≥ 13 * card n ^ 3` and `φ` a test function. For a finite
set `F` of polynomials, the part `geometricSide F` of the geometric side, which is the integral
over `[G]` of the sum of the values of `k ⊗ φ` at `x⁻¹ γ x` over the rational points `γ` with
characteristic polynomial in `F`, is the sum of the parts given by the elements of `F`. -/
lemma geometricSide_coe_finset (hB : 13 * Fintype.card n ^ 3 ≤ B) (he : IsCuspKernel B k)
    (F : Finset E[X]) (φ : TestFunction (Gf E n)) :
    V.geometricSide hB he F φ = ∑ R ∈ F, V.geometricSide hB he {R} φ := by
  classical
  simp only [geometricSide_apply]
  rw [← integral_finsetSum F fun R _ ↦ V.integrable_tsum_polyTerm hB he φ {R}]
  congr with x
  change ∑' γ : U V.J, V.polyTerm k φ F γ x = ∑ R ∈ F, ∑' γ : U V.J, V.polyTerm k φ {R} γ x
  rw [← Summable.tsum_finsetSum fun R _ ↦ V.summable_polyTerm hB φ he.decay {R} x]
  exact tsum_congr fun γ ↦ by simp [kernelTerm, Set.indicator_apply]

/-- Let `V` be a hermitian space with a point over the CM field `E`, and let `φ` be a test function
on `G_f`. Let `k` be a cusp kernel of order `B ≥ 13 * card n ^ 3` on `G_∞`: a minimal idempotent for
which `‖x‖^(B+1) k(x)` is integrable, `‖x‖^B k(x)` is bounded, and `α ∗ k = k` for some continuous
compactly supported `α`. The geometric side, which is the integral over `[G]` of the sum of the
values of `k ⊗ φ` at `x⁻¹ γ x` over all rational points `γ`, is the convergent sum over the
polynomials `R` of its parts given by the `γ` with characteristic polynomial `R`. -/
theorem hasSum_geometricSide (hB : 13 * Fintype.card n ^ 3 ≤ B) (he : IsCuspKernel B k)
    (φ : TestFunction (Gf E n)) :
    HasSum (fun R : E[X] ↦ V.geometricSide hB he {R} φ) (V.geometricSide hB he .univ φ) := by
  classical
  -- Let `F` increase through the finite sets of polynomials. The sums over the `γ` with
  -- polynomial in `F` converge at each point and are uniformly bounded.
  have : Countable E[X] := (AddMonoidAlgebra.coeff_injective.comp toFinsupp_injective).countable
  have h_pointwise (x : G E s) :
      Tendsto (fun F : Finset E[X] ↦ ∑' γ : U V.J, V.polyTerm k φ F γ x) atTop
        (𝓝 (∑' γ : U V.J, V.polyTerm k φ .univ γ x)) := by
    refine tendsto_tsum_of_dominated_convergence (V.summable_polyTerm hB φ he.decay .univ x).norm
      (fun γ ↦ tendsto_const_nhds.congr' ?_) (.of_forall fun F γ ↦ ?_)
    · filter_upwards [eventually_finset_mem_atTop (γ : Matrix n n E).charpoly] with F hF
      simp [kernelTerm, hF]
    · -- Each term is dominated by the term for the set of all polynomials.
      simp only [polyTerm, kernelTerm, norm_mul]
      gcongr
      exact norm_indicator_le_of_subset (Set.subset_univ _) 1 _
  obtain ⟨D, hD⟩ := V.exists_norm_tsum_polyTerm_le hB φ he
  have h_limit : Tendsto (fun F : Finset E[X] ↦ V.geometricSide hB he F φ) atTop
      (𝓝 (V.geometricSide hB he .univ φ)) :=
    tendsto_integral_filter_of_norm_le_const
      (.of_forall fun F ↦ (V.integrable_tsum_polyTerm hB he φ F).aestronglyMeasurable)
      ⟨D, .of_forall fun F ↦ .of_forall fun x ↦ hD x F⟩ (.of_forall h_pointwise)
  exact h_limit.congr fun F ↦ V.geometricSide_coe_finset hB he F φ

/-- Let `k` be a cusp kernel of order `B ≥ 13 * card n ^ 3`. Each part `geometricSide S` of the
geometric side, an integral over the quotient of the adelic group by the image `V.Γ` of the rational
points, is invariant under the conjugation `TestFunction.translate (g, g)` of the test function,
`y ↦ φ(g⁻¹ y g)`, by a finite adelic point `g`. The proof is the substitution `x ↦ x * (1, g)`. -/
lemma geometricSide_translate (hB : 13 * Fintype.card n ^ 3 ≤ B) (he : IsCuspKernel B k)
    (S : Set E[X]) (g : Gf E n) (φ : TestFunction (Gf E n)) :
    V.geometricSide hB he S (TestFunction.translate (g, g) φ) = V.geometricSide hB he S φ := by
  have h_term (γ : U V.J) (x : G E s) :
      V.polyTerm k (TestFunction.translate (g, g) φ) S γ x = V.polyTerm k φ S γ (x * (1, g)) := by
    simp [kernelTerm, TestFunction.translate_apply, mul_assoc]
  have : IsScalarTower V.Γ (G E s) (G E s) := ⟨fun δ x y ↦ mul_assoc δ.1 x y⟩
  have h_inv : ∀ (δ : V.Γ) (x : G E s),
      ∑' γ : U V.J, V.polyTerm k φ S γ (δ • x) = ∑' γ : U V.J, V.polyTerm k φ S γ x := by
    rintro ⟨_, δ₀, rfl⟩ x
    exact V.tsum_polyTerm_ratEmbed_mul φ S δ₀ x
  simp only [geometricSide_apply, h_term]
  exact (identDistrib_orbitMeasure_mul_right (X := G E s) (1, g) h_inv
    (V.measurable_tsum_polyTerm he.continuous.measurable φ S)).integral_eq

/-- For a cusp kernel `k` of order `B ≥ 13 * card n ^ 3`, the part of the geometric side given by
the polynomial `R` (the integral of the sum over the rational points with characteristic polynomial
`R`) is `0` if the test function `φ`, with underlying function `φ.1`, vanishes at all finite adelic
points whose component at the finite place `w` has as characteristic polynomial the image of `R`
over the completion `LocField w`. -/
lemma geometricSide_singleton_eq_zero_of_forall (hB : 13 * Fintype.card n ^ 3 ≤ B)
    (he : IsCuspKernel B k) (w : FinPlace E) {R : E[X]}
    {φ : TestFunction (Gf E n)} (h_zero : ∀ y : Gf E n,
      (y.atPlace w).1.charpoly = R.map (algebraMap E (LocField w)) → φ.1 y = 0) :
    V.geometricSide hB he {R} φ = 0 := by
  have h_term (γ : U V.J) (x : G E s) : V.polyTerm k φ {R} γ x = 0 := by
    by_cases hγ : (γ : Matrix n n E).charpoly = R
    · rw [polyTerm, kernelTerm, h_zero _ (by rw [charpoly_atPlace_conj_ratEmbed, hγ])]
      simp
    · simp [kernelTerm, hγ]
  simp [geometricSide_apply, h_term]

/-- Let `k` be a cusp kernel of order `B ≥ 13 * card n ^ 3`. Let the test function `φ` be cuspidal
at the split place `w` (the sums of its translates over the unipotent radicals of the proper
parabolic subgroups over the residue field vanish), and let each point of the support of `φ` be
integral at `w'` with `0` a simple root of its characteristic polynomial modulo `w'`
(`HasSimpleZero`). If the polynomial `R` is not irreducible, then the part of the geometric side
given by `R`, the integral of the sum over the rational points with characteristic polynomial `R`,
is `0`. -/
theorem geometricSide_singleton_eq_zero (hB : 13 * Fintype.card n ^ 3 ≤ B)
    (hk : IsCuspKernel B k) {w w' : FinPlace E} {hw : w.IsSplit} {φ : TestFunction (Gf E n)}
    (h_cusp : IsCuspidalAt hw φ)
    (h_supp : ∀ g : Gf E n, φ.1 g ≠ 0 → HasSimpleZero (g.atPlace w')) {R : E[X]}
    (hR : ¬Irreducible R) : V.geometricSide hB hk {R} φ = 0 := by
  by_contra h_ne
  -- Some point of the support has the image of `R` as its polynomial at `w'`.
  -- Hence `R` is not a proper power.
  obtain ⟨y, hy_charpoly, hy_ne⟩ : ∃ y : Gf E n,
      (y.atPlace w').1.charpoly = R.map (algebraMap E (LocField w')) ∧ φ.1 y ≠ 0 := by
    by_contra! h_zero
    exact h_ne (V.geometricSide_singleton_eq_zero_of_forall hB hk w' h_zero)
  have h_monic : R.Monic := monic_map_iff.1 <| by
    simpa only [hy_charpoly] using charpoly_monic (y.atPlace w' : Matrix n n (LocField w'))
  have h_pow (Q : E[X]) (j : ℕ) (hj : 1 < j) : R ≠ Q ^ j := fun hQ ↦
    (h_supp y hy_ne).charpoly_ne_pow (Q.map (algebraMap E _)) hj (by simp [hy_charpoly, hQ])
  obtain ⟨A, C, h_coprime, hA, hC, rfl⟩ :=
    exists_isCoprime_mul_of_not_irreducible h_monic hR h_pow
  -- The part of `R = A * C` is an invariant linear form that only sees the fibre of `R` at `w`.
  set f : E →+* LocField w := algebraMap E (LocField w)
  have h_fibre (ψ : TestFunction (Gf E n))
      (h_zero : ∀ y : Gf E n, (y.atPlace w).1.charpoly = A.map f * C.map f → ψ.1 y = 0) :
      V.geometricSide hB hk {A * C} ψ = 0 :=
    V.geometricSide_singleton_eq_zero_of_forall hB hk w (by rwa [Polynomial.map_mul])
  exact h_ne (eq_zero_of_coprime_factors hw (h_coprime.map (mapRingHom f))
    (mt (isUnit_map f).1 hA) (mt (isUnit_map f).1 hC) _ (V.geometricSide_translate hB hk _)
    h_fibre h_cusp)

end Space

end New

end
