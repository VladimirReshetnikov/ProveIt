import New.OneLift.ComparisonOperator.DeterminantProducts
import New.UpperBound.Kernels.ThetaLiftGauge

/-!
# Rational equivariance, integrality and size of definite theta kernels

This file studies the theta kernels `New.modKernelStdSpace` of a pair of standard definite spaces
`I_L`, `I_N`, whose real datum is determined by a polynomial `Q`. The kernels are evaluated at
finite points. Moving these points by rational elements acts through the two-sided substitutions
`New.Rows.twoSidedSubst`. Here `p` is a number whose prime divisors in `E` are the places at which
integrality is asked. The file builds the normalising constant `New.Rows.modKernelScale` and bounds
the conjugates of a polynomial `Q` homogeneous of degree `d` on polydiscs.

## Main definitions and results

* `New.Rows.modKernelStdSpace_embFin_mul`: moving the points by rational elements substitutes the
  variables of `Q` (`New.Rows.twoSidedSubst`) and multiplies by determinants.
* `New.Rows.IsModKernelScale`, `New.Rows.exists_ne_zero_isModKernelScale`: after one
  normalising constant, kernels with `p`-integral input are `p`-integral and, under bounds on the
  sizes of the input, their conjugates are bounded.

Notions from other files:
* `New.stdSpace`: the definite space `I_n`, the sum of `n` norms with its standard lattice.
* `New.Gf`, `New.integralAbove`: the finite adelic unitary group, and its subgroup of points whose
  components at all primes above `p` are integral invertible matrices.
* `New.modKernelStdSpace`: the theta kernel of the datum made of a function `Ψ` on matrices modulo
  `𝔪` and the Fock vector of a polynomial `Q`, for the Weil action twisted by two characters of
  `U(1)`.
* `New.Space.jetSeries`, `New.jet`: the Taylor series of a theta function in Fock's coordinates, and
  the pairing `P(∂) F (0)` of a polynomial `P` with a power series `F`.
* `New.Rows.twoSidedSubst`: the substitution `x_τ ↦ c_τᵀ x_τ g_τᵀ` on complex polynomials in the
  entries of `N × L` matrices `x_τ`.
-/

noncomputable section

namespace New.Rows

open Matrix MvPolynomial Real Fintype Finset Space Parameters RingHom NeZero
open NumberField (InfinitePlace)

variable {E L N : Type} [Field E] [CMType E] [WeilData E] [Fintype L] [DecidableEq L] [Fintype N]
  [DecidableEq N]

/-- Let `a`, `b` be automorphic characters of `U(1)` (`AutChar`) with exponents `e`, `e'` at the
infinite places and residue characters `ψ`, `ψ'`. Translating the finite adelic points `g`, `h` by
the finite parts (`embFin`) of rational points `γ`, `γ'` substitutes
`x_τ ↦ (Φ τ γ'⁻¹)ᵀ x_τ (Φ τ γ)ᵀ` in `Q` (`twoSidedSubst`) and multiplies the kernel by
`∏ τ, Φ τ (det γ') ^ (-e τ) * Φ τ (det γ) ^ e' τ`. Here `(1, g)` has trivial real part, and `Φ τ` is
the complex embedding of `E` that the CM type chooses at the place `τ`. -/
lemma modKernelStdSpace_embFin_mul {a b : AutChar E} {e e' : InfinitePlace E → ℤ}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} (ha : a.HasWeight e ψ)
    (hb : b.HasWeight e' ψ') (𝔪 : Modulus E) (Ψ : Matrix N L 𝔪.ResidueRing → ℂ)
    (Q : MvPolynomial (InfinitePlace E × N × L) ℂ) (γ : U (stdSpace E L).J)
    (γ' : U (stdSpace E N).J) (g : Gf E L) (h : Gf E N) :
    modKernelStdSpace (stdSpace E L) a b 𝔪 Ψ Q
        (1, (stdSpace E L).embFin γ * g) ((stdSpace E N).embFin γ' * h) =
      (∏ τ : InfinitePlace E,
          Φ τ (γ' : Matrix N N E).det ^ (-e τ) * Φ τ (γ : Matrix L L E).det ^ e' τ) *
        modKernelStdSpace (stdSpace E L) a b 𝔪 Ψ
          (twoSidedSubst (fun τ : InfinitePlace E ↦ (↑γ'⁻¹ : Matrix N N E).map (Φ τ))
            (fun τ : InfinitePlace E ↦ (γ : Matrix L L E).map (Φ τ)) Q) (1, g) h := by
  -- The kernel is invariant under the rational points `γ⁻¹`, `γ'⁻¹`. They cancel the finite
  -- translations and leave the real point `(x, y)`, which lies in the maximal compact
  -- subgroups (the spaces are definite) and acts on the Fock vector by substitution and a scalar.
  let S : Space E L 1 := stdSpace E L
  let T : Space E N 1 := stdSpace E N
  let x : GInf E (1 : L → ℤˣ) := (S.ratEmbed γ⁻¹).1
  let y : GInf E (1 : N → ℤˣ) := (T.ratEmbed γ'⁻¹).1
  have hx : S.ratEmbed γ⁻¹ * (1, S.embFin γ * g) = (x, g) := by ext1 <;> simp [x, embFin]
  have hy : T.ratEmbed γ'⁻¹ * (1, T.embFin γ' * h) = (y, h) := by ext1 <;> simp [y, embFin]
  have h_inv (f : 𝒮 (S.hom T)) : pairTheta S T a b f ((x, g), y, h) =
      pairTheta S T a b f ((1, S.embFin γ * g), 1, T.embFin γ' * h) := by
    rw [← hx, ← hy]
    exact (pairThetaKer S T a b).rat_mul ⟨γ⁻¹, rfl⟩ ⟨γ'⁻¹, rfl⟩ ..
  -- All signs are `1`: every matrix is block diagonal, and the principal minors are `det` or `1`.
  -- At the place `τ` the points `x`, `y` and `x⁻¹` are the images of `γ⁻¹`, `γ'⁻¹` and `γ`.
  have hx_inv (τ : InfinitePlace E) : (↑(x τ)⁻¹ : GL L ℂ) = (Φ τ).mapMatrix (γ : Matrix L L E) := by
    simp [← stdSpace_ratEmbed_apply γ τ, x, S]
  have h_real : realPairWeil e e' (x, y) (Fock.polyVector (realSigns E (homSigns 1 1)) Q) =
      (∏ τ, Φ τ (γ' : Matrix N N E).det ^ (-e τ) * Φ τ (γ : Matrix L L E).det ^ e' τ) •
        Fock.polyVector _ (twoSidedSubst (fun τ ↦ (↑γ'⁻¹ : Matrix N N E).map (Φ τ))
          (fun τ ↦ (γ : Matrix L L E).map (Φ τ)) Q) := by
    rw [realPairWeil_polyVector e e' (x := x) (y := y) (by simp) (by simp)]
    simp only [hx_inv, x, y, S, T, stdSpace_ratEmbed_apply]
    simp [← map_det, ← mapMatrix_apply, principalMinor_of_forall,
      DiscreteSeries.principalMinor_of_forall_not]
  rw [modKernelStdSpace, modKernel, ← h_inv, pairTheta, modDatum, pairWeil_integrated_all, h_real]
  simp [modKernel, pairTheta, modDatum, pairWeil_integrated_fin, S, T]

omit [WeilData E]
/-- If the finite adelic points `g`, `g'` have integral invertible components at all primes above
`p`, so does their block sum `diag(g, g')`. -/
lemma blockSumOne_mem_integralAbove {p : ℕ} {g : Gf E L} {g' : Gf E N}
    (hg : g ∈ integralAbove L p) (hg' : g' ∈ integralAbove N p) :
    U.blockSumOne (g, g') ∈ integralAbove (L ⊕ N) p := by
  rw [mem_localLevel] at hg hg' ⊢
  simpa [mem_intGL, Gf.atPlace, U.sum, ← map_inv, and_and_and_comm] using
    fun w hw ↦ And.intro (hg w hw) (hg' w hw)

/-- The embedding of rational points into finite adelic points commutes with block sums. -/
lemma stdEmbFin_blockSumOne (γ : U (stdSpace E L).J) (γ' : U (stdSpace E N).J) :
    stdEmbFin (U.blockSumOne (γ, γ')) = U.blockSumOne (stdEmbFin γ, stdEmbFin γ') := by
  refine Subtype.ext ((stdSpace_embFin _).trans ?_)
  ext (i | i) (j | j) <;> simp [U.sum]

/-- Let `γ`, `γ'` be rational unitary points, embedded in the finite adelic groups by `stdEmbFin`,
and let `g`, `g'` be finite adelic points. If `γ g` and `γ' g'` have integral invertible components
at all primes above `p`, so does the product of the block sums `diag(γ, γ')` and `diag(g, g')`. -/
lemma blockSumOne_mul_mem_integralAbove {p : ℕ} {γ : U (stdSpace E L).J} {γ' : U (stdSpace E N).J}
    {g : Gf E L} {g' : Gf E N} (hg : stdEmbFin γ * g ∈ integralAbove L p)
    (hg' : stdEmbFin γ' * g' ∈ integralAbove N p) :
    stdEmbFin (U.blockSumOne (γ, γ')) * U.blockSumOne (g, g') ∈ integralAbove (L ⊕ N) p := by
  simpa [stdEmbFin_blockSumOne, ← map_mul] using blockSumOne_mem_integralAbove hg hg'

/-- The constant that normalises the theta kernels of the standard definite spaces `I_L`, `I_N`
over the field `D.E = P.E s` of the data `D`, where `s = D.towerExp` is its exponent in the tower
over `K = ℚ(√-P.d)`, for polynomials homogeneous of degree `d`. It is built from the principal
level `D.M` (a product of two primes), the number `P.vacuumScale s` that makes the values of the
vacuum of rank one (`Space.vacElem`) integral, and the scale `P.jetScale s` of the Taylor series. -/
noncomputable def modKernelScale (L N : Type) [Fintype L] [Fintype N] {P : Parameters} (D : Data P)
    (d : ℕ) : ℂ :=
  (D.M ^ 2) ^ (2 * Core.numInfPlaces D.E * card (N × L)) *
    P.vacuumScale D.towerExp ^ card (N × L) * (D.M ^ 2 * P.d * P.jetScale D.towerExp) ^ d

variable (L N) in
omit [DecidableEq L] [DecidableEq N] in
lemma modKernelScale_ne_zero {P : Parameters} (D : Data P) (d : ℕ) :
    modKernelScale L N D d ≠ 0 := by
  simp [modKernelScale, NeZero.ne]
/-- Let `Q` be homogeneous of degree `d`. Take `s` times the datum (`vacuumDatum`) that is `Ψ` at
the places dividing `𝔪` and elsewhere the vacuum, and translate it (`pairWeil`) by the adelic points
`(1, g)`, `(1, h)` with trivial real parts and finite parts `g`, `h`. The pairing `Q(∂) F (0)`
(`jet`) of `Q` with the Taylor series `F` of its theta function at scale `t` is `s * t ^ d` times
the theta kernel `modKernelStdSpace`. -/
lemma jet_jetSeries_pairWeil_vacuumDatum {P : Parameters} {D : Data P} {d : ℕ} {a b : AutChar D.E}
    {𝔪 : Modulus D.E} {Ψ : Matrix N L 𝔪.ResidueRing → ℂ}
    {Q : MvPolynomial (InfinitePlace D.E × N × L) ℂ} (hQ : Q.IsHomogeneous d) (g : Gf D.E L)
    (h : Gf D.E N) (s t : ℂ) :
    jet ℂ Q (((stdSpace D.E L).hom (stdSpace D.E N)).jetSeries t
        (pairWeil (stdSpace D.E L) (stdSpace D.E N) a b ((1, g), 1, h)
          (s • (vacuumDatum (stdSpace D.E L) (stdSpace D.E N) 𝔪 Ψ).val))) =
      s * t ^ d * modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h := by
  let V : Space D.E (N × L) (homSigns 1 1) := (stdSpace D.E L).hom (stdSpace D.E N)
  let ω : 𝒮 V →L[ℂ] 𝒮 V := pairWeil (stdSpace D.E L) (stdSpace D.E N) a b ((1, g), 1, h)
  -- The kernel is the theta series of the translated datum integrated against `Q`, since finite
  -- points commute with `integrated`.
  have h_kernel : modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h =
      V.θ (V.integrated (Fock.polyVector _ Q) (ω (vacuumDatum _ _ 𝔪 Ψ).val)) := by
    rw [← pairWeil_integrated_fin, modKernelStdSpace, modKernel, pairTheta]
    rfl
  simp [ω, V, h_kernel, jet_jetSeries_of_isHomogeneous _ hQ, mul_assoc, mul_left_comm s]

/-- Let the automorphic characters `a`, `b` of `U(1)` have exponents `ea`, `eb` at the infinite
places and residue characters `ψ`, `ψ'`, let `𝔪` contain `q * D.M ^ 2`, let the values of `Ψ` be
integral at all primes coprime to `q`, and let `Q` be homogeneous of degree `d`. Let `p` be a prime
coprime to `q`; the instance `PadicPlace p` chooses an embedding `ιₚ : ℂ → ℂ_p`, with valuation ring
`embValRing ⊆ ℂ`. If the finite adelic points `g`, `h` are integral above `p` and `Q` has
coefficients in `embValRing`, then the kernel times `modKernelScale L N D d` has `p`-adic norm at
most `1`. -/
lemma norm_modKernelScale_mul_modKernelStdSpace_le_one {P : Parameters} {D : Data P} {d : ℕ}
    {a b : AutChar D.E} {ea eb : InfinitePlace D.E → ℤ}
    {ψ ψ' : (w : FinPlace D.E) → MulChar (ResField w) ℂ} {𝔪 : Modulus D.E}
    {Ψ : Matrix N L 𝔪.ResidueRing → ℂ} {Q : MvPolynomial (InfinitePlace D.E × N × L) ℂ}
    (ha : a.HasWeight ea ψ) (hb : b.HasWeight eb ψ') {q : ℕ} (hq : ↑(q * D.M ^ 2) ∈ 𝔪.ideal)
    (hΨ : ∀ x : Matrix N L 𝔪.ResidueRing, Ψ x ∈ Seesaw.integralAway q) (hQ : Q.IsHomogeneous d)
    {p : ℕ} [Fact p.Prime] [PadicPlace p] (hp : p.Coprime q) {g : Gf D.E L} {h : Gf D.E N}
    (hg : g ∈ integralAbove L p) (hh : h ∈ integralAbove N p)
    (hQ_int : Q ∈ (MvPolynomial.map embValRing.subtype).range) :
    ‖ιₚ (modKernelScale L N D d * modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h)‖ ≤ 1 := by
  -- Once its denominator `δ ^ denomExp` is cleared, the datum is standard at `p`, and the action
  -- of `g`, `h` keeps it so. The normalised kernel is a jet of its Taylor series.
  obtain ⟨Q₀, hQ₀ : Q₀.map embValRing.subtype = Q⟩ := hQ_int
  let δ : ℕ := D.M ^ 2
  let denomExp : ℕ := 2 * Core.numInfPlaces D.E * card (N × L)
  let V : Space D.E (N × L) (homSigns 1 1) := (stdSpace D.E L).hom (stdSpace D.E N)
  let f : 𝒮 V := ((δ ^ denomExp : ℕ) : ℂ) • P.vacuumScale D.towerExp ^ card (N × L) •
    (vacuumDatum (stdSpace D.E L) (stdSpace D.E N) 𝔪 Ψ).val
  let ω : 𝒮 V →L[ℂ] 𝒮 V := pairWeil (stdSpace D.E L) (stdSpace D.E N) a b ((1, g), 1, h)
  have h_std : f ∈ standardData V δ := smul_vacuumDatum_mem_standardData hq hΨ hp
  -- Since `f` is standard of level `δ`, the scale of its series is `star δ * P.d * jetScale`.
  have jet_eq : jet ℂ Q (V.jetSeries (star (δ : ℂ) * P.d * P.jetScale D.towerExp) (ω f)) =
      modKernelScale L N D d * modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h := by
    simp only [f, ω, V, smul_smul, jet_jetSeries_pairWeil_vacuumDatum hQ]
    simp [modKernelScale, δ, denomExp]
  rw [← jet_eq, ← hQ₀]
  exact norm_jet_jetSeries_le_one (by simp [δ, ne]) (pairWeil_mem_standardData ha hb h_std hg hh) _

/-- Growth of a homogeneous polynomial `Q` of degree `d` under an automorphism `σ` of `ℂ`: a bound
`B` for `‖σ (Q z)‖` on the polydisc `‖σ (z i)‖ ≤ ρ` gives the bound `B * t ^ d` on the polydisc
`‖σ (z i)‖ ≤ t * ρ`. -/
lemma norm_map_eval_le_of_isHomogeneous {ι : Type*} {Q : MvPolynomial ι ℂ} {d : ℕ}
    (hQ : Q.IsHomogeneous d) (σ : ℂ ≃+* ℂ) {ρ B : ℝ}
    (hB : ∀ z : ι → ℂ, (∀ i : ι, ‖σ (z i)‖ ≤ ρ) → ‖σ (Q.eval z)‖ ≤ B) {t : ℝ} (ht : 0 < t)
    {z : ι → ℂ} (hz : ∀ i : ι, ‖σ (z i)‖ ≤ t * ρ) :
    ‖σ (Q.eval z)‖ ≤ B * t ^ d := by
  -- Scale `z` by `u = σ⁻¹ (t⁻¹)`: this divides `σ z` by `t` and `σ (Q z)` by `t ^ d`.
  let u : ℂ := σ.symm (t : ℂ)⁻¹
  have h_eval : Q.eval (fun i ↦ u * z i) = u ^ d * Q.eval z := by
    simpa [aeval_bind₁, aeval_eq_eval, -coe_aeval_eq_eval] using
      congrArg (aeval z) (isHomogeneous_iff_aeval_smul_X.1 hQ u (by simp [u, ht.ne']))
  have h_scaled : ‖σ (Q.eval fun i ↦ u * z i)‖ ≤ B :=
    hB _ fun i ↦ by simpa [u, abs_of_pos ht, inv_mul_le_iff₀ ht] using hz i
  rw [h_eval] at h_scaled
  simpa [u, abs_of_pos ht, inv_mul_le_iff₀ (pow_pos ht d), mul_comm B] using h_scaled

/-- Let `M = D.M` be the principal level of the data `D` and `d ≤ M`. For every automorphism `σ` of
`ℂ`, the number `‖σ (M ^ 2 * P.d)‖ ^ 2 / Ω` times `2 * d + 2` is at most `(M ^ 4) ^ 2`. Here `P.d`
is the prime with `K = ℚ(√-P.d)`, and `Ω = P.bigOmega D.towerExp` is
`exp (γ - Re L'/L(1, χ_K)) * 2π` divided by the root discriminant of the field `D.E` (`γ` is Euler's
constant). -/
lemma norm_map_sq_div_bigOmega_mul_le {P : Parameters} {D : Data P} {d : ℕ} (hd : d ≤ D.M)
    (σ : ℂ ≃+* ℂ) :
    ‖σ (D.M ^ 2 * P.d)‖ ^ 2 / P.bigOmega D.towerExp * (2 * d + 2) ≤ (D.M ^ 4) ^ 2 := by
  have hΩ : 0 < P.bigOmega D.towerExp := bigOmega_pos
  -- `σ` fixes the natural numbers, and the claim follows from the sizes of the logarithms.
  grw [show ‖σ (D.M ^ 2 * P.d)‖ = D.M ^ 2 * P.d by simp, hd]
  exact D.le_of_hasLogBound

/-- The parameters `P` fix a prime `P.d` and `K = ℚ(√-P.d)`; the data `D` fix a field `D.E`, the
step `D.towerExp` of a cyclotomic tower over `K`, and a level `M = D.M`, a product of two primes.
Let `σ` be an automorphism of `ℂ`, and `Q` homogeneous of degree `d ≤ M` with `‖σ (Q z)‖ ≤ B`
whenever all `‖σ (z i)‖ ≤ M ^ 4`. Put `T = ‖σ (M ^ 2 * P.d)‖ ^ 2 / Ω`, where
`Ω = P.bigOmega D.towerExp` is `exp (γ - Re L'/L(1, χ_K)) * 2π` divided by the root discriminant
of `D.E` (`γ` is Euler's constant). Then `HasConjugateGrowth σ Q T d 0 B` holds: for all `z` and
real `R` with `∑ ‖σ (z i)‖ ^ 2 ≤ T * (2 * d + 2) * R`, we have `‖σ (Q z)‖ ≤ B * exp (0 + d * R)`. -/
lemma hasConjugateGrowth_of_isHomogeneous {P : Parameters} {D : Data P} {d : ℕ} {ι : Type*}
    [Fintype ι] {Q : MvPolynomial ι ℂ} (hd : d ≤ D.M) (hQ : Q.IsHomogeneous d) (σ : ℂ ≃+* ℂ) {B : ℝ}
    (hB : ∀ z : ι → ℂ, (∀ i : ι, ‖σ (z i)‖ ≤ D.M ^ 4) → ‖σ (Q.eval z)‖ ≤ B) :
    HasConjugateGrowth σ Q (‖σ (D.M ^ 2 * P.d)‖ ^ 2 / P.bigOmega D.towerExp) d 0 B := by
  -- The hypothesis on `z` puts `σ z` in the polydisc of radius `exp R * M ^ 4`.
  intro z R hz
  have hΩ : 0 < P.bigOmega D.towerExp := bigOmega_pos
  have coord_le (i : ι) : ‖σ (z i)‖ ^ 2 ≤ (exp R * D.M ^ 4) ^ 2 := calc
    _ ≤ ∑ j, ‖σ (z j)‖ ^ 2 := single_le_sum (f := fun j ↦ ‖σ (z j)‖ ^ 2) (by simp) (mem_univ i)
    _ ≤ R * (‖σ (D.M ^ 2 * P.d)‖ ^ 2 / P.bigOmega D.towerExp * (2 * d + 2)) := by rwa [mul_comm R]
    _ ≤ (exp R * D.M ^ 4) ^ 2 := by
      rw [mul_pow]
      gcongr
      · nlinarith [add_one_le_exp R]
      · exact norm_map_sq_div_bigOmega_mul_le hd σ
  rw [zero_add, exp_nat_mul]
  exact norm_map_eval_le_of_isHomogeneous hQ σ hB (exp_pos R)
    fun i ↦ le_of_sq_le_sq (coord_le i) (by positivity)

/-- The constants in the bound for the conjugates of the theta kernel are at most `exp D.x₁`. The
data `D` for the parameters `P` fix a cut-off `D.x₁` (a large integer), a rank `D.r` (a power of
`3`), a level `D.M` and a CM field `D.E = P.E s` with `s = D.towerExp`, generated over
`K = ℚ(√-P.d)` by a root of unity of order `P.q₁ s`; `P.Φ s` is the set of its infinite places, and
`P.constantBound` bounds the constants that depend on `P` only. Let `L`, `N` have at most
`D.gap = 2 * D.r ^ 8` elements, let `d ≤ D.M`, and let the ideal `𝔪` of `𝓞 D.E` contain `D.M ^ 2`.
The three factors are the cleared denominator, the number of matrices over
`𝔪.ResidueRing = 𝓞 D.E / 𝔪`, and the exponential in `Parameters.jetSizeBound`. -/
lemma M_pow_mul_card_mul_exp_le {P : Parameters} {D : Data P} {d : ℕ} {𝔪 : Modulus D.E}
    (hL : card L ≤ D.gap) (hN : card N ≤ D.gap) (hd : d ≤ D.M) (h𝔪 : ↑(D.M ^ 2) ∈ 𝔪.ideal) :
    ((D.M : ℝ) ^ 2) ^ (2 * Core.numInfPlaces D.E * card (N × L)) * card (N × L → 𝔪.ResidueRing) *
        exp (P.constantBound * (P.q₁ D.towerExp * card (N × L) + 1) ^ 2 +
          card (P.Φ D.towerExp × N × L) * log (2 * d + 2)) ≤
      exp D.x₁ := by
  let k : ℕ := 2 * Core.numInfPlaces D.E * card (N × L)
  let e : ℝ := P.constantBound * (P.q₁ D.towerExp * card (N × L) + 1) ^ 2 +
    card (P.Φ D.towerExp × N × L) * log (2 * d + 2)
  have h_card : (card (N × L → 𝔪.ResidueRing) : ℝ) ≤ (D.M ^ 2) ^ k := by
    rw [card_fun, card_eq_nat_card (α := 𝔪.ResidueRing), pow_mul]
    exact_mod_cast Nat.pow_le_pow_left (𝔪.card_residueRing_le h𝔪 one_le) _
  have h_pow : ((D.M : ℝ) ^ 2) ^ k = exp (k * (2 * log D.M)) := by
    simp [exp_nat_mul, two_mul, sq, exp_add, exp_log, NeZero.pos]
  -- Insert the three size bounds; the rest is a comparison of logarithmic sizes.
  have h_log : k * (2 * log D.M) + k * (2 * log D.M) + e ≤ D.x₁ := by
    simp only [k, e, card_prod]
    norm_cast
    grw [le_abs_self P.constantBound, hd, hL, hN]
    exact D.le_of_hasLogBound
  grw [h_card, h_pow, ← exp_add, ← exp_add, h_log]

/-- Let `L`, `N` have at most `D.gap = 2 * D.r ^ 8` elements and let `d ≤ D.M`. Let the automorphic
characters `a`, `b` of `U(1)` have exponents `ea`, `eb` at the infinite places and residue
characters `ψ`, `ψ'` (`HasWeight`), and let `𝔪` contain `D.M ^ 2`. Let all conjugates of the values
of `Ψ` have norm at most the integer `A`, and let `Q` be homogeneous of degree `d` with
`‖σ (Q z)‖ ≤ B` whenever all `‖σ (z i)‖ ≤ D.M ^ 4`. Then the `σ`-conjugate of
`modKernelScale L N D d` times the kernel has norm at most `exp D.x₁ * A * B`. -/
lemma norm_modKernelScale_mul_modKernelStdSpace_le {P : Parameters} {D : Data P} {d : ℕ}
    {a b : AutChar D.E} {ea eb : InfinitePlace D.E → ℤ}
    {ψ ψ' : (w : FinPlace D.E) → MulChar (ResField w) ℂ} {𝔪 : Modulus D.E}
    {Ψ : Matrix N L 𝔪.ResidueRing → ℂ} {Q : MvPolynomial (InfinitePlace D.E × N × L) ℂ}
    (hL : card L ≤ D.gap) (hN : card N ≤ D.gap) (hd : d ≤ D.M) (ha : a.HasWeight ea ψ)
    (hb : b.HasWeight eb ψ') (h𝔪 : ↑(D.M ^ 2) ∈ 𝔪.ideal) {A : ℕ}
    (hA : ∀ (τ : ℂ ≃+* ℂ) (x : Matrix N L 𝔪.ResidueRing), ‖τ (Ψ x)‖ ≤ A) (hQ : Q.IsHomogeneous d)
    (σ : ℂ ≃+* ℂ) {B : ℝ} (hB : ∀ z : InfinitePlace D.E × N × L → ℂ,
      (∀ i : InfinitePlace D.E × N × L, ‖σ (z i)‖ ≤ D.M ^ 4) → ‖σ (Q.eval z)‖ ≤ B)
    (g : Gf D.E L) (h : Gf D.E N) :
    ‖σ (modKernelScale L N D d * modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h)‖ ≤
      exp D.x₁ * A * B := by
  -- The normalised kernel is `(D.M ^ 2) ^ denomExp` times the jet along `Q` of the Taylor series
  -- of `ω f₀`, where `f₀` is a combination of translates of the vacuum with small coefficients. The
  -- conjugates of the jet are bounded by `norm_jet_le_of_isVacuumCombination`, and `exp D.x₁`
  -- absorbs the constants.
  let denomExp : ℕ := 2 * Core.numInfPlaces D.E * card (N × L)
  let V : Space D.E (N × L) (homSigns 1 1) := (stdSpace D.E L).hom (stdSpace D.E N)
  let f₀ : 𝒮 V := P.vacuumScale D.towerExp ^ card (N × L) • (vacuumDatum _ _ 𝔪 Ψ).val
  let ω : 𝒮 V →L[ℂ] 𝒮 V := pairWeil (stdSpace D.E L) (stdSpace D.E N) a b ((1, g), 1, h)
  let J : ℂ := jet ℂ Q (V.jetSeries (D.M ^ 2 * P.d * P.jetScale D.towerExp) (ω f₀))
  have jet_eq : modKernelScale L N D d * modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h =
      (D.M ^ 2) ^ denomExp * J := by
    simp only [J, V, ω, f₀, jet_jetSeries_pairWeil_vacuumDatum hQ]
    simp [modKernelScale, denomExp, mul_assoc]
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  -- The coefficients of `f₀` have total size at most `card (N × L → 𝔪.ResidueRing) * A`; the free
  -- exponent is taken to be `0`, and `ha`, `hb` enter as instance arguments.
  let e : ℝ := P.constantBound * (P.q₁ D.towerExp * card (N × L) + 1) ^ 2 +
    card (P.Φ D.towerExp × N × L) * log (2 * d + 2)
  have h_jet : ‖σ J‖ ≤ card (N × L → 𝔪.ResidueRing) * A * exp e * B := by
    simpa only [jetSizeBound, add_zero] using P.norm_jet_le_of_isVacuumCombination
      (isVacuumCombination_vacuumDatum A hA) g h hB₀ le_rfl
      (hasConjugateGrowth_of_isHomogeneous hd hQ σ hB)
  calc _ = (D.M ^ 2) ^ denomExp * ‖σ J‖ := by simp [jet_eq]
    _ ≤ (D.M ^ 2) ^ denomExp * (card (N × L → 𝔪.ResidueRing) * A * exp e * B) := by gcongr
    _ = (D.M ^ 2) ^ denomExp * card (N × L → 𝔪.ResidueRing) * exp e * A * B := by ring
    _ ≤ exp D.x₁ * A * B := by grw [M_pow_mul_card_mul_exp_le hL hN hd h𝔪]

variable (L N) in
/-- The constant `c` is a scale for the theta kernels `modKernelStdSpace` of the standard definite
spaces `I_L`, `I_N` over the field `D.E` of the data `D`, for polynomials `Q` homogeneous of degree
`d` and characters `a`, `b` with exponents `ea`, `eb` at the infinite places and tame parts `ψ`,
`ψ'` (`HasWeight`): `c` times the kernel is integral at `p` when the input is, and its conjugates
are bounded when `L`, `N`, `d` and the input are. Here the principal level `D.M` is a product of
two primes, `D.gap = 2 * D.r ^ 8` with `D.r` the rank of the target (a power of `3`), and `D.x₁`
is the second cut-off of `D`, a large integer. -/
structure IsModKernelScale {P : Parameters} (D : Data P) (d : ℕ) (c : ℂ) : Prop where
  /-- Let `𝔪` contain `q * D.M ^ 2` and let the values of `Ψ` be integral at the primes coprime
  to `q`. If `p` is such a prime and `g`, `h` and the coefficients of `Q` are integral at `p`, then
  `c` times the kernel has `p`-adic norm at most `1`. -/
  norm_le_one {a b : AutChar D.E} {ea eb : InfinitePlace D.E → ℤ}
    {ψ ψ' : (w : FinPlace D.E) → MulChar (ResField w) ℂ} {𝔪 : Modulus D.E}
    {Ψ : Matrix N L 𝔪.ResidueRing → ℂ} {Q : MvPolynomial (InfinitePlace D.E × N × L) ℂ}
    (ha : a.HasWeight ea ψ) (hb : b.HasWeight eb ψ') {q : ℕ} (hq : ↑(q * D.M ^ 2) ∈ 𝔪.ideal)
    (hΨ : ∀ x : Matrix N L 𝔪.ResidueRing, Ψ x ∈ Seesaw.integralAway q) (hQ : Q.IsHomogeneous d)
    {p : ℕ} [Fact p.Prime] [PadicPlace p] (hp : p.Coprime q) {g : Gf D.E L} {h : Gf D.E N}
    (hg : g ∈ integralAbove L p) (hh : h ∈ integralAbove N p)
    (hQ_int : Q ∈ (MvPolynomial.map embValRing.subtype).range) :
    ‖ιₚ (c * modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h)‖ ≤ 1
  /-- Let `L`, `N` have at most `D.gap` elements, let `d ≤ D.M` and let `𝔪` contain
  `D.M ^ 2`. If `A` bounds all conjugates of the values of `Ψ`, and `B` bounds `σ ∘ Q` on the
  polydisc `‖σ (z i)‖ ≤ D.M ^ 4`, then the `σ`-conjugate of `c` times the kernel has norm at
  most `exp D.x₁ * A * B`. -/
  norm_map_le {a b : AutChar D.E} {ea eb : InfinitePlace D.E → ℤ}
    {ψ ψ' : (w : FinPlace D.E) → MulChar (ResField w) ℂ} {𝔪 : Modulus D.E}
    {Ψ : Matrix N L 𝔪.ResidueRing → ℂ} {Q : MvPolynomial (InfinitePlace D.E × N × L) ℂ}
    (hL : card L ≤ D.gap) (hN : card N ≤ D.gap) (hd : d ≤ D.M) (ha : a.HasWeight ea ψ)
    (hb : b.HasWeight eb ψ') (h𝔪 : ↑(D.M ^ 2) ∈ 𝔪.ideal) {A : ℕ}
    (hA : ∀ (τ : ℂ ≃+* ℂ) (x : Matrix N L 𝔪.ResidueRing), ‖τ (Ψ x)‖ ≤ A) (hQ : Q.IsHomogeneous d)
    (σ : ℂ ≃+* ℂ) {B : ℝ} (hB : ∀ z : InfinitePlace D.E × N × L → ℂ,
      (∀ i : InfinitePlace D.E × N × L, ‖σ (z i)‖ ≤ D.M ^ 4) → ‖σ (Q.eval z)‖ ≤ B)
    (g : Gf D.E L) (h : Gf D.E N) :
    ‖σ (c * modKernelStdSpace (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h)‖ ≤ exp D.x₁ * A * B

/-- Integrality and size of the theta kernels `modKernelStdSpace` of the standard definite spaces
`I_L`, `I_N` over the field `D.E` of the data `D`, built from a function `Ψ` on matrices modulo `𝔪`
and a polynomial `Q` homogeneous of degree `d`. There is a constant `c ≠ 0`, depending only on `L`,
`N`, `D` and `d`, with the two properties of `IsModKernelScale`. If `𝔪` contains `q * D.M ^ 2`, the
values of `Ψ` are integral away from `q`, and the points `g`, `h` and the coefficients of `Q` are
integral at a prime `p` coprime to `q`, then `c` times the kernel is integral at `p`. If `L`, `N`
have at most `D.gap` elements, `d ≤ D.M`, `𝔪` contains `D.M ^ 2`, `A` bounds the conjugates of the
values of `Ψ` and `B` bounds `σ ∘ Q` on the polydisc `‖σ (z i)‖ ≤ D.M ^ 4`, then the `σ`-conjugate
of `c` times the kernel has norm at most `exp D.x₁ * A * B`. -/
lemma exists_ne_zero_isModKernelScale (L N : Type) [Fintype L] [DecidableEq L] [Fintype N]
    [DecidableEq N] {P : Parameters} (D : Data P) (d : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ IsModKernelScale L N D d c :=
  ⟨modKernelScale L N D d, modKernelScale_ne_zero L N D d,
    norm_modKernelScale_mul_modKernelStdSpace_le_one, norm_modKernelScale_mul_modKernelStdSpace_le⟩

end New.Rows

end
