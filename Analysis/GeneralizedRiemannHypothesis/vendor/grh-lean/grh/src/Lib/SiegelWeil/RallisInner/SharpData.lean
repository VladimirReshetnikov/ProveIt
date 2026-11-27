import Lib.General.Algebra.LevelModulus
import Lib.SiegelWeil.RallisInner.Doubling
import Lib.SiegelWeil.UnramifiedSeries.RallisSeries

/-!
# Rallis' inner product formula for sharp data and injectivity of the theta lift

This file proves Rallis' inner product formula for the theta lift `New.Space.lift` from `U(S)` to
`U(T)` when `rk T > 2 rk S`, for data `v ⊗ F` with `F` sharp (`New.SiegelWeil.IsSharp`). It starts
from `New.SiegelWeil.inner_product_formula`. For `v` an edge from type `e`, the lift is injective
on `J`-invariant forms of type `e`. The file then derives `IsSharp` from `New.SiegelWeil.IsSharpFn`,
a condition on a level `J` and a function `Ψ` on matrices modulo 𝔪, if all signs of `S` agree or
𝔪 ≠ (1), with `S₀` the set of places of 𝔪𝔪̄ and the mass `c` the mean of `|Ψ|²` over the index of
`J`. Finally it computes the vacuum sum in rank one as a partial Hecke L-value over a partial
Euler product.

## Main definitions and results

* `New.SiegelWeil.IsSharp.petersson_lift_eq_integral`: for a sharp datum the Petersson product
  (`New.Space.petersson`) of two lifts is a real integral against the series
  `New.SiegelWeil.rallisSeries` of the places off `S₀`. The finite points are cut into cosets in
  `New.SiegelWeil.IsSharp.hasSum_integral_weilMatrixCoeff_mul`.
* `New.SiegelWeil.exists_petersson_formLift_eq_rallisSeries`: for `v` an edge (`New.IsEdge`) from
  type `e`, the lift is injective on `J`-invariant forms of type `e`, and the product of two lifts
  is a multiple of the pairing with the series; `New.SiegelWeil.rallis_inner_product_cosetTerm`
  expands the series.
* `New.SiegelWeil.IsSharpFn.isSharp`: if all signs of `S` agree or 𝔪 ≠ (1), a function on matrices
  modulo 𝔪 that is sharp for a level J (`New.SiegelWeil.IsSharpFn`) gives a finite datum whose
  matrix coefficient is constant on J and zero at the other points integral off 𝔪𝔪̄
  (`New.SiegelWeil.IsSharp`). `New.SiegelWeil.isSharp_vacuumDatum_of_mul_eq_one` is the case of the
  principal level.
* `New.vacuumSum_eq_L_div_eulerProd`: in rank one and for target rank 2k with k > 1, the sum
  `New.SiegelWeil.vacuumSum` of the vacuum coefficient over the cosets at the places off a set and
  its conjugate, where the tame part is trivial, is a partial Hecke L-value at k over the partial
  Euler product of the signs `New.placeSign` (a partial value of ζ_F at 2k if E is unramified
  over its real subfield F).

Notions from other files:
* `New.Space.integrated`: the datum v ⊗ F = ∫ v(y) ϱ(y) F dy, for v in the Fock model and ϱ the
  Heisenberg operators of the real vectors y.
* `New.IsEdge`: what the formula uses of the real vector v and the types e, e'. The vector of the
  joint harmonic of corresponding parameters is an edge between the types of these parameters
  (`New.ParamsCorrespond.isEdge_jointHarmonic`).
* `New.Modulus.liftFn`: a function of vectors modulo 𝔪, read on finite adelic vectors: its value at
  the reduction if the components at the places of 𝔪 are integral, and 0 otherwise.
* `New.SiegelWeil.IsSharp` (from `Lib.SiegelWeil.RallisInner.Doubling`): `F` is a vacuum off a
  set `S₀` of places; at the finite points integral off `S₀` the coefficient `⟨F, ω(g) F⟩` is
  `⟨F, F⟩` on `J ∩ stdLevel E n` and zero otherwise, and `⟨F, F⟩` over the index of
  `J ∩ stdLevel E n` in `stdLevel E n` is the mass `c`.

## Relation to the literature

Rallis inner product formula by doubling. Here the unramified integrals are left as a convergent
sum over cosets. For its sources see `Lib.SiegelWeil.RallisInner.Doubling`.

Non-vanishing of theta lifts in large rank. Here it is proved for unitary groups with target rank
more than twice the source rank, for finite data sharp at a level and without L-functions. If the
lift vanishes, the real matrix coefficient of the datum convolves the form to zero. Source:
S. Rallis, Injectivity properties of liftings associated to Weil representations, Compositio 52
(1984); J.-S. Li, Non-vanishing theorems for the cohomology of certain arithmetic quotients,
Crelle 428 (1992).

Critical Hecke L-values of CM fields as squared norms of theta lifts from U(1). Here the values are
taken at integers k at least 2, and the trivial character of U(1) is lifted to a definite U(2k),
with the tame Hecke character entering through the splitting. The squared norm is an explicit
constant times the L-value, and the lift is integral. Galois conjugates of the lift belong to
conjugate characters. This file contains only the local sum and the Euler product; the norm formula
is `New.LValueData.inner_trivialLift_self_eq_L`. Source: G. Shimura, On some arithmetic properties
of modular forms of one and several variables, Ann. of Math. 102 (1975); method: T. Yang, Theta
liftings and Hecke L-functions, J. reine angew. Math. 485 (1997); Harris, Li, Skinner, The Rallis
inner product formula and p-adic L-functions (2005); Finis, Ann. of Math. 163 (2006).
-/

noncomputable section

/-!
## Rallis' inner product formula for sharp data, and injectivity

Rallis' inner product formula for the theta lift `New.Space.lift` from `U(S)` to `U(T)` in the range
`rk T > 2 rk S`, for data `φ = v ⊗ F` (`New.Space.integrated`) with `v` in the Fock space and `F` a
sharp finite datum (`New.SiegelWeil.IsSharp`): a vacuum off a set `S₀` of places, whose matrix
coefficient at the points integral off `S₀` is supported on `J ∩ stdLevel E n` and constant there,
of mass `c`.

The proofs start from the doubling formula `New.SiegelWeil.inner_product_formula`, an integral over
`U(S)(𝔸)`.
-/

namespace New.SiegelWeil

open MeasureTheory Fock Space Fintype Set

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {a b : AutChar E}
  {S₀ : Set (FinPlace E)} {J : Subgroup (Gf E n)} {c : ℂ} {T : Space E m t} {F : 𝒮 (S.hom T)}
  {γ' : NumberField.InfinitePlace E → ℤ} {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
  {y : G E s → ℂ}

/-- If the finite datum `F` is sharp for the group `J`, then `J` is open. -/
lemma IsSharp.isOpen_level (hF : IsSharp b S₀ F J c) : IsOpen (J : Set (Gf E n)) := by
  -- The matrix coefficient of `F` is continuous, nonzero at `1` and zero on `stdLevel E n` outside
  -- `J`.
  let U : Set (Gf E n) := (stdLevel E n : Set (Gf E n)) ∩ {g | weilMatrixCoeff b F F (1, g) ≠ 0}
  have h_open : IsOpen U := isOpen_stdLevel.inter isOpen_ne.preimage_of_continuous
  have h_one : 1 ∈ U := by simp [U, weilMatrixCoeff, hF.self_ne_zero, Prod.mk_one_one]
  have h_sub : U ⊆ J := fun g ⟨g_int, h_ne⟩ ↦ by_contra fun h_not ↦ h_ne <|
    (hF.weilMatrixCoeff_eq g (stdLevel_le_localLevel g_int)).trans
      (ite_eq_right (mt And.left h_not))
  exact J.isOpen_of_mem_nhds (mem_nhds_iff.2 ⟨U, h_sub, h_open, h_one⟩)

lemma IsSharp.mass_ne_zero (hF : IsSharp b S₀ F J c) : c ≠ 0 := by
  simp [← hF.mass_eq, hF.self_ne_zero, isCompact_stdLevel.relIndex_ne_zero hF.isOpen_level]

open scoped Classical in
/-- For `F` sharp for `J`, of mass `c`, the function equal to `⟨F, F⟩` on `J ⊓ stdLevel E n` and to
zero elsewhere has integral `c` over the finite points, for the Haar measure that gives
`stdLevel E n` volume `1`. -/
lemma IsSharp.integral_ite_eq_mass (hF : IsSharp b S₀ F J c) :
    ∫ g : Gf E n, (if g ∈ J ⊓ stdLevel E n then dataInner (S.hom T) F F else 0) = c := by
  -- As `stdLevel E n` has volume `1`, the volume of `J ⊓ stdLevel E n` is the inverse of its index.
  trans ∫ g, (J ∩ stdLevel E n : Set (Gf E n)).indicator (fun _ ↦ dataInner (S.hom T) F F) g
  · simp [Set.indicator]
  rw [integral_indicator_const _ (hF.isOpen_level.inter isOpen_stdLevel).measurableSet,
    ← hF.mass_eq]
  simp [measure_inter_eq_inv_relIndex isCompact_stdLevel hF.isOpen_level, Measure.real, field]

/-- Let `F` be a finite datum, `v` a vector of the Fock space and `φ = v ⊗ F`. The matrix
coefficient of `φ` at the point `(x, g)` is the real coefficient `⟨v, Ω(x) v⟩` times the finite
coefficient `⟨F, ω(g) F⟩`. Here `Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and
any `γ`. -/
lemma weilMatrixCoeff_integrated [b.HasWeight γ' ψ] (hF : F ∈ finitePart (S.hom T))
    (γ : NumberField.InfinitePlace E → ℤ) (v : PairFock E s t) (x : GInf E s) (g : Gf E n) :
    weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, g) =
      fockInner v (realPairWeil γ γ' (x, 1) v) * weilMatrixCoeff b F F (1, g) := by
  rw [weilMatrixCoeff, pairWeil_integrated_all, dataInner_integrated, ← pairWeil_integrated_fin]
  simp [hF, realPairWeil, Prod.mk_one_one]

open scoped Classical in
/-- The coefficient of a sharp datum. Let `F` be sharp for `J` off `S₀`, `v` a vector of the Fock
space and `φ = v ⊗ F`. For a real point `x`, a finite point `u` supported on `S₀ᶜ` and its conjugate
and a finite point `g` integral off `S₀`, `⟨φ, ω(x u g) φ⟩` is the product of the real coefficient
`⟨v, Ω(x) v⟩`, the coefficient of the vacuum at `u`, and `⟨F, F⟩` times the indicator of
`J ⊓ stdLevel E n` at `g`. Here `Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and
any `γ`. -/
theorem IsSharp.weilMatrixCoeff_integrated_mul (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (γ : NumberField.InfinitePlace E → ℤ) (v : PairFock E s t) (x : GInf E s) {u g : Gf E n}
    (hu : u ∈ Gf.supportedOn n S₀ᶜ) (hg : g ∈ localLevel n S₀ᶜ) :
    weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, u * g) =
      fockInner v (realPairWeil γ γ' (x, 1) v) * vacuumCoeff (card m) b u *
        if g ∈ J ⊓ stdLevel E n then dataInner (S.hom T) F F else 0 := by
  rw [show ((x, u * g) : G E s) = (1, u) * (x, g) by simp,
    weilMatrixCoeff_mul b (hF.vacuum_off S₀ᶜ v disjoint_compl_right) hu hg,
    weilMatrixCoeff_integrated hF.mem_finitePart γ, hF.weilMatrixCoeff_eq g hg, mul_left_comm,
    mul_assoc]

/-- Let `b` have weight `γ'` and tame part `ψ`, and let `F` be sharp for `J` off `S₀` (see
`IsSharp`). Then `J` contains every point of `stdLevel E n`, the stabiliser in `G_f` of `Ô ^ n`,
whose component is 1 at every place outside `S₀ᶜ` and the conjugate places of `S₀ᶜ`. -/
lemma IsSharp.inf_supportedOn_le (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ] :
    stdLevel E n ⊓ Gf.supportedOn n S₀ᶜ ≤ J := by
  -- Compute the coefficient of `vac ⊗ F` at `k = k * 1 = 1 * k` in two ways.
  rintro k ⟨k_int, k_supp⟩
  by_contra h_not
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) vacVector F
  have h_ne : weilMatrixCoeff b φ φ (1, k * 1) ≠ 0 := by
    rw [hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 k_supp (one_mem _)]
    simp [Prod.mk_one_one, vacuumCoeff, finMultiplier_ne_zero, hF.self_ne_zero, Fock.realVac]
  have h_zero : weilMatrixCoeff b φ φ (1, 1 * k) = 0 := by
    rw [hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 (one_mem _) (stdLevel_le_localLevel k_int)]
    simp [h_not]
  exact h_ne (by rw [mul_one, ← h_zero, one_mul])

/-- Let `b` have a weight and a tame part. If `F` is sharp, a vacuum off `S₀`, then `b ∘ det` is
trivial on the integral points supported on the places of `S₀ᶜ` and their conjugates. -/
lemma IsSharp.isUnramifiedOn (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ] :
    IsUnramifiedOn b n S₀ᶜ := by
  -- Compute the coefficient of `vac ⊗ F` at `k = k * 1 = 1 * k` in two ways.
  intro k hk
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) vacVector F
  let realCoeff : ℂ := fockInner (vacVector : PairFock E s t) (realPairWeil 0 γ' (1, 1) vacVector)
  have h_left : weilMatrixCoeff b φ φ (1, k) =
      realCoeff * vacuumCoeff (card m) b k * dataInner (S.hom T) F F := by
    rw [← mul_one k, hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 hk.2 (one_mem _),
      ite_eq_left (one_mem _), mul_one]
  have h_right : weilMatrixCoeff b φ φ (1, k) =
      realCoeff * vacuumCoeff (card m) b (1 : Gf E n) * dataInner (S.hom T) F F := by
    rw [← one_mul k, hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 (one_mem _)
      (stdLevel_le_localLevel hk.1), ite_eq_left ⟨hF.inf_supportedOn_le hk, hk.1⟩]
  have h_real : realCoeff ≠ 0 := by simp [realCoeff, Prod.mk_one_one, Fock.realVac]
  have h_coeff : vacuumCoeff (card m) b k = vacuumCoeff (card m) b (1 : Gf E n) :=
    mul_left_cancel₀ h_real (mul_right_cancel₀ hF.self_ne_zero (h_left.symm.trans h_right))
  simpa [vacuumCoeff, finMultiplier_eq_one_of_mem hk.1, Prod.mk_one_one, ← Circle.coe_inj,
    finMultiplier_eq_one_of_mem (one_mem (stdLevel E n))] using h_coeff

/-- Cutting an integral over a group into cosets. Let `μ` be left invariant on `H`, let `L` be a
measurable subgroup with countably many cosets, represented by the points `r q`. The integral of an
integrable `Φ` is the sum over the cosets `q` of the integrals of `g ↦ Φ (r q * g)` over `L`. -/
lemma _root_.New.hasSum_setIntegral_mul_coset {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableMul H] {μ : Measure H} [μ.IsMulLeftInvariant] {L : Subgroup H} [Countable (H ⧸ L)]
    (hL : MeasurableSet (L : Set H)) {r : H ⧸ L → H} (hr : ∀ q : H ⧸ L, (r q : H ⧸ L) = q)
    {Φ : H → ℂ} (hΦ : Integrable Φ μ) :
    HasSum (fun q : H ⧸ L ↦ ∫ g in (L : Set H), Φ (r q * g) ∂μ) (∫ g, Φ g ∂μ) := by
  let coset (q : H ⧸ L) : Set H := (fun g ↦ (r q)⁻¹ * g) ⁻¹' L
  have mem_coset (q : H ⧸ L) (g : H) : g ∈ coset q ↔ q = (g : H ⧸ L) := by
    rw [Set.mem_preimage, SetLike.mem_coe, ← QuotientGroup.eq, hr]
  have h_disjoint : Pairwise (Function.onFun Disjoint coset) := by
    grind [Pairwise]
  have h_cover : ⋃ q, coset q = Set.univ := by simp [Set.eq_univ_iff_forall, mem_coset]
  have h_coset (q : H ⧸ L) : ∫ g in coset q, Φ g ∂μ = ∫ g in (L : Set H), Φ (r q * g) ∂μ := by
    simpa using (measurePreserving_mul_left μ (r q)⁻¹).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft _) (fun g ↦ Φ (r q * g)) L
  simpa only [h_coset, h_cover, Measure.restrict_univ] using
    hasSum_integral_iUnion (s := coset) (fun q ↦ measurable_const_mul _ hL) h_disjoint hΦ.restrict

/-- Let `F` be sharp for `J` off `S₀`, of mass `c`, let `v` be a vector of the Fock space,
`φ = v ⊗ F` and `x` a real point, and let `P` be a right `J`-invariant function on the finite
points. If `g ↦ ⟨φ, ω(x g) φ⟩ P(g)` is integrable, its integral is the sum, over the cosets `q` of
the points integral off `S₀`, of `c ⟨v, Ω(x) v⟩` times the coefficient of the vacuum and the value
of `P` at `cosetRep q`, the representative of `q` supported on `S₀ᶜ` and its conjugate. Here
`Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and any `γ`. -/
lemma IsSharp.hasSum_integral_weilMatrixCoeff_mul (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (γ : NumberField.InfinitePlace E → ℤ) (v : PairFock E s t) (x : GInf E s) {P : Gf E n → ℂ}
    (hP : ∀ k ∈ J, ∀ g : Gf E n, P (g * k) = P g)
    (h_int : Integrable fun g : Gf E n ↦
      weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, g) * P g) :
    HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦ c * (fockInner v (realPairWeil γ γ' (x, 1) v) *
        (vacuumCoeff (card m) b (cosetRep q).val * P (cosetRep q).val)))
      (∫ g : Gf E n,
        weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, g) * P g) := by
  classical
  -- Cut the finite points into the cosets; on each, `weilMatrixCoeff_integrated_mul` gives the
  -- integrand, a multiple of the function whose integral is the mass.
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) v F
  have h_meas : MeasurableSet (localLevel n S₀ᶜ : Set (Gf E n)) :=
    (isOpen_coe_localLevel S₀ᶜ).measurableSet
  have h_coset (u : Gf E n) (hu : u ∈ Gf.supportedOn n S₀ᶜ) :
      ∫ g in (localLevel n S₀ᶜ : Set (Gf E n)), weilMatrixCoeff b φ φ (x, u * g) * P (u * g) =
      c * (fockInner v (realPairWeil γ γ' (x, 1) v) * (vacuumCoeff (card m) b u * P u)) := by
    rw [← integral_indicator h_meas, ← hF.integral_ite_eq_mass, ← integral_mul_const]
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    by_cases h_level : g ∈ J ⊓ stdLevel E n
    · have hg : g ∈ localLevel n S₀ᶜ := stdLevel_le_localLevel h_level.2
      simp only [φ, Set.indicator_of_mem hg, hF.weilMatrixCoeff_integrated_mul γ v x hu hg,
        ite_eq_left h_level, hP g h_level.1]
      ring
    · simp +contextual only [φ, Set.indicator_apply_eq_zero, SetLike.mem_coe, ite_eq_right h_level,
        hF.weilMatrixCoeff_integrated_mul γ v x hu, mul_zero, zero_mul, implies_true]
  have : Countable (Gf E n ⧸ localLevel n S₀ᶜ) := countable_quotient_localLevel S₀ᶜ
  exact (hasSum_setIntegral_mul_coset h_meas mk_cosetRep h_int).congr_fun
    fun q ↦ (h_coset _ (cosetRep q).property).symm

/-- Inner product formula. Let `2 * card n < card m`, let `F` be sharp for `J` off `S₀` with mass
`c` (see `IsSharp`), let `v` be a Fock-space vector, and let `Θ` be the lift by `v ⊗ F` for the
characters `a`, `b`. Let `y`, `y'` be rapidly decreasing automorphic functions with `y` fixed by
`J`. Let `z = rallisSeries (card m) b S₀ᶜ y` be the series `∑ mc(q) R(q) y` over the cosets `q` of
the finite points integral at `S₀ᶜ`, with `mc` the vacuum coefficient. Then `⟨Θ y', Θ y⟩` equals the
volume of `[U(T)]` times `c` times the absolutely convergent integral of `⟨v, Ω(x) v⟩ ⟨y', R(x) z⟩`
over the real points `x` of `U(S)`. Here `R` is right translation and
`Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and `γ` arbitrary. -/
theorem IsSharp.petersson_lift_eq_integral {S₀ : Set (FinPlace E)} {F : 𝒮 (S.hom T)}
    {J : Subgroup (Gf E n)} {c : ℂ} (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (h_rank : 2 * card n < card m) (a : AutChar E) (γ : NumberField.InfinitePlace E → ℤ)
    (v : PairFock E s t) {y y' : G E s → ℂ} (hy : y ∈ S.rapidFunctions)
    (hy' : y' ∈ S.rapidFunctions) (hJ : HasLevel y J) :
    Integrable (fun x : GInf E s ↦ fockInner v (realPairWeil γ γ' (x, 1) v) *
      S.petersson y' fun g : G E s ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1))) ∧
    T.petersson (lift (pairThetaKer S T a b) (integrated (S.hom T) v F) y')
        (lift (pairThetaKer S T a b) (integrated (S.hom T) v F) y) =
      T.quotMeasure.real Set.univ * c * ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) *
        S.petersson y' fun g : G E s ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1)) := by
  -- `inner_product_formula` gives the product as an absolutely convergent adelic integral;
  -- integrate first over the finite points.
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) v F
  let P (g : G E s) : ℂ := S.petersson y' fun g' ↦ y (g' * g)
  obtain ⟨h_int, h_adelic⟩ : Integrable (fun g : G E s ↦ weilMatrixCoeff b φ φ g * P g) volume ∧
      T.petersson (lift (pairThetaKer S T a b) φ y') (lift (pairThetaKer S T a b) φ y) =
        T.quotMeasure.real Set.univ * ∫ g, weilMatrixCoeff b φ φ g * P g :=
    inner_product_formula h_rank a b (hF.clean v) hy hy'
  obtain ⟨y_aut : S.IsAutomorphic y, y_rapid : S.IsRapid y⟩ := hy
  obtain ⟨y'_aut : S.IsAutomorphic y', y'_rapid : S.IsRapid y'⟩ := hy'
  have y_bdd : IsBoundedMeasurable y := .of_continuous y_rapid.bounded y_aut.continuous
  have y'_int : Integrable y' S.quotMeasure := y'_rapid.integrable y'_aut.continuous
  have h_level (x : GInf E s) (k : Gf E n) (hk : k ∈ J) (g : Gf E n) : P (x, g * k) = P (x, g) := by
    have h_split : ((x, g * k) : G E s) = (x, g) * (1, k) := by simp
    simp only [P, h_split, ← mul_assoc, hJ k hk]
  have h_finite : ∀ᵐ x : GInf E s, ∫ g : Gf E n, weilMatrixCoeff b φ φ (x, g) * P (x, g) =
      c * (fockInner v (realPairWeil γ γ' (x, 1) v) *
        S.petersson y' fun g ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1))) := by
    filter_upwards [h_int.prod_right_ae] with x hx
    have h_series : HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦
        vacuumCoeff (card m) b (cosetRep q).val * P (x, (cosetRep q).val))
        (S.petersson y' fun g ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1))) := by
      simpa [P, mul_assoc] using hasSum_petersson_rallisSeries h_rank b S₀ᶜ y_bdd y'_int (x, 1)
    exact (hF.hasSum_integral_weilMatrixCoeff_mul γ v x (h_level x) hx).unique
      ((h_series.mul_left _).mul_left c)
  refine ⟨(integrable_const_mul_iff hF.mass_ne_zero.isUnit _).1
    (h_int.integral_prod_left.congr h_finite), ?_⟩
  rw [h_adelic, Measure.volume_eq_prod, integral_prod _ h_int, integral_congr_ae h_finite,
    integral_const_mul, mul_assoc]

/-- Let `card m > 2 * card n` and let `F` on `Hom(S, T)` be sharp for `J` off `S₀` with mass `c`
(see `IsSharp`). Let `y` be automorphic, rapidly decreasing and fixed by `J`, let `v` be a
Fock-space vector and let `a`, `b` be characters. If the theta lift of `y` by `v ⊗ F` for
`pairThetaKer S T a b` vanishes and `x ↦ ⟨v, Ω(x) v⟩` is integrable, then its convolution `realConv`
with `y` is zero. Here `Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b`. -/
lemma realConv_eq_zero_of_lift_eq_zero (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (v : PairFock E s t) (hJ : HasLevel y J) (hy : y ∈ S.rapidFunctions)
    (h_rank : 2 * card n < card m)
    (h_lift : lift (pairThetaKer S T a b) (integrated (S.hom T) v F) y = 0)
    (γ : NumberField.InfinitePlace E → ℤ)
    (h_int : Integrable fun x : GInf E s ↦ fockInner v (realPairWeil γ γ' (x, 1) v)) :
    realConv (fun x : GInf E s ↦ fockInner v (realPairWeil γ γ' (x, 1) v)) y = 0 := by
  -- The convolution `y₁` is bounded and fixed by the integral points supported off `S₀`, so it is
  -- enough to show that its series `z` vanishes, that is, `⟨z, z⟩ = 0`.
  set κ : GInf E s → ℂ := fun x ↦ fockInner v (realPairWeil γ γ' (x, 1) v)
  let y₁ : G E s → ℂ := realConv κ y
  let z : G E s → ℂ := rallisSeries (card m) b S₀ᶜ y₁
  have ⟨y_aut, y_rapid⟩ : S.IsAutomorphic y ∧ S.IsRapid y := hy
  have y_bdd : IsBoundedMeasurable y := .of_continuous y_rapid.bounded y_aut.continuous
  obtain ⟨K, hK⟩ := y_aut.exists_level
  obtain ⟨y₁_aut, y₁_bdd⟩ : S.IsAutomorphic y₁ ∧ IsBoundedMeasurable y₁ :=
    isAutomorphic_realConv K y_bdd y_aut.rat_mul hK h_int
  have y₁_level : HasLevel y₁ (stdLevel E n ⊓ Gf.supportedOn n S₀ᶜ) := fun k hk_mem g ↦ by
    have h_comm (x : GInf E s) : g * (1, k) * (x, 1) = g * (x, 1) * (1, k) := by simp [mul_assoc]
    simp only [y₁, realConv, h_comm, hJ k (hF.inf_supportedOn_le hk_mem)]
  refine eq_zero_of_rallisSeries_eq_zero h_rank hF.isUnramifiedOn y₁_bdd.bounded y₁_level ?_
  have z_aut : S.IsAutomorphic z :=
    isAutomorphic_rallisSeries h_rank hF.isUnramifiedOn y₁_aut y₁_bdd.bounded y₁_level
  have series_bdd {φ : G E s → ℂ} (φ_aut : S.IsAutomorphic φ) (φ_bdd : IsBoundedMeasurable φ) :
      IsBoundedMeasurable (rallisSeries (card m) b S₀ᶜ φ) := by
    obtain ⟨B, hB⟩ := φ_bdd.bounded
    exact .of_continuous ⟨_, norm_rallisSeries_le h_rank b S₀ᶜ hB⟩
      (continuous_rallisSeries h_rank b S₀ᶜ φ_aut.continuous φ_bdd.bounded)
  have z_bdd : IsBoundedMeasurable z := series_bdd y₁_aut y₁_bdd
  -- The series commutes with real translations, so by the inner product formula `z` is orthogonal
  -- to every rapidly decreasing `y'`.
  have h_orth {y' : G E s → ℂ} (hy' : y' ∈ S.rapidFunctions) : S.petersson y' z = 0 := by
    obtain ⟨-, h_formula⟩ := hF.petersson_lift_eq_integral h_rank a γ v hy hy' hJ
    have y'_bdd : IsBoundedMeasurable y' := .of_continuous hy'.2.bounded hy'.1.continuous
    rw [← petersson_realConv_right (series_bdd y_aut y_bdd) h_int y'_bdd,
      realConv_rallisSeries h_rank b S₀ᶜ y_bdd h_int, h_lift] at h_formula
    simpa [petersson, hF.mass_ne_zero, measureReal_univ_ne_zero, z, y₁] using h_formula
  -- `z` is a sum of averages of translates of `y`, and the translates are rapidly decreasing.
  have h_translate (x : G E s) : S.petersson z (fun g : G E s ↦ y (g * x)) = 0 := by
    rw [← conj_petersson, h_orth ⟨y_aut.comp_mul_right x, y_rapid.comp_mul_right⟩, map_zero]
  have h_average (u : Gf E n) : S.petersson z (fun g : G E s ↦ y₁ (g * (1, u))) = 0 := by
    have h_conv : (fun g : G E s ↦ y₁ (g * (1, u))) = realConv κ fun g ↦ y (g * (1, u)) :=
      funext fun g ↦ by simp [y₁, realConv, mul_assoc]
    rw [h_conv, petersson_realConv_right (y_bdd.comp (measurable_mul_const (1, u))) h_int z_bdd]
    simp only [mul_assoc, h_translate, mul_zero, integral_zero]
  apply z_aut.eq_zero_of_petersson_self (z_bdd.memLp_top.mono_exponent le_top)
  have z_int : Integrable z S.quotMeasure := z_bdd.memLp_top.integrable le_top
  have h_series : HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦
      vacuumCoeff (card m) b (cosetRep q).val *
        S.petersson z fun g : G E s ↦ y₁ (g * (1, (cosetRep q).val))) (S.petersson z z) := by
    simpa only [mul_one] using hasSum_petersson_rallisSeries (S := S) h_rank b S₀ᶜ y₁_bdd z_int 1
  simpa only [h_average, mul_zero, tsum_zero] using h_series.tsum_eq.symm

/-- Injectivity and norm of the lift, in Weil's range `2 * card n < card m`. Let the vector `v` of
the Fock space be an edge (a real datum that carries type `e` to type `e'`, such as the vector of
the joint harmonic of corresponding parameters) for the weights `γ`, `γ'`. There is `C ≠ 0`,
depending only on these real data and the spaces, with the following property. Let `a`, `b` be
characters of weights `γ`, `γ'`, let the finite datum `F` be sharp for `J`
off `S₀`, of mass `c` (see `IsSharp`), and let `L` be the lift by `v ⊗ F`. On the forms `y` of type
`e` fixed by `J` the lift is injective, and `⟨L y', L y⟩` is `C c` times the Petersson product of
`y'` with the series `rallisSeries` of `y` off `S₀`, for all forms `y'` of type `e`. -/
theorem exists_petersson_formLift_eq_rallisSeries {γ : NumberField.InfinitePlace E → ℤ}
    {v : PairFock E s t} {e : GInf E s → ℂ} {e' : GInf E t → ℂ}
    (h_edge : IsEdge (realPairWeil γ γ') e e' v) (h_rank : 2 * card n < card m) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ (a b : AutChar E) {ψ ψ' : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
      {S₀ : Set (FinPlace E)} {J : Subgroup (Gf E n)} {F : 𝒮 (S.hom T)} {c : ℂ}
      [a.HasWeight γ ψ] [b.HasWeight γ' ψ'], IsSharp b S₀ F J c →
      ∀ y : S.Form e, HasLevel y J →
        let L : S.Form e →ₗ[ℂ] T.Form e' :=
          formLift (pairThetaKer S T a b) e e' ((S.hom T).integrated v F)
        (L y = 0 → y = 0) ∧
        ∀ y' : S.Form e,
          T.petersson (L y') (L y) = C * c * S.petersson y' (rallisSeries (card m) b S₀ᶜ y) := by
  -- The real integral `Z` of `⟨v, Ω(x) v⟩` against the coefficient of the type `e` is not zero for
  -- an edge.
  let Z : ℂ :=
    ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) * (starRingEnd ℂ (e x) / e 1)
  have hZ : Z ≠ 0 := h_edge.zetaIntegral_ne_zero
  refine ⟨T.quotMeasure.real univ * Z, by simp [hZ, measureReal_univ_ne_zero], ?_⟩
  intro a b ψ ψ' S₀ J F c _ _ hF y hJ
  -- Forms of type `e` are rapid, and on them `formLift` is the lift of functions.
  have h_arr : IsArrow (pairThetaKer S T a b) e e' ((S.hom T).integrated v F) :=
    (h_edge.isArrow a b hF.mem_finitePart).1
  simp only [h_arr.coe_formLift]
  -- On forms of type `e`, real translates scale the Petersson product by `conj (e x) / e 1`.
  have h_real (y' z : S.Form e) : ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) *
      S.petersson y' (fun g : G E s ↦ z.val (g * (x, 1))) = Z * S.petersson y' z := by
    simp [y'.property.petersson_real_translate h_edge.isCuspKernel_source z.property, ← mul_assoc,
      Z, integral_mul_const]
  -- The series `z` of `y` is a form of type `e`, so the real integral of the inner product formula
  -- is `h_real` for `z`.
  have y_level : HasLevel y (stdLevel E n ⊓ Gf.supportedOn n S₀ᶜ) :=
    fun k hk ↦ hJ k (hF.inf_supportedOn_le hk)
  obtain ⟨z : S.Form e, -, hz : ⇑z = rallisSeries (card m) b S₀ᶜ y⟩ :=
    exists_form_eq_rallisSeries h_rank hF.isUnramifiedOn le_rfl
      (inf_le_left.trans stdLevel_le_localLevel) y_level
  rw [← hz]
  set Θ : (G E s → ℂ) → G E t → ℂ := lift (pairThetaKer S T a b) ((S.hom T).integrated v F)
  have h_norm (y' : S.Form e) :
      T.petersson (Θ y') (Θ y) = T.quotMeasure.real univ * Z * c * S.petersson y' z := by
    obtain ⟨y_rapid, -⟩ := h_arr y
    obtain ⟨y'_rapid, -⟩ := h_arr y'
    obtain ⟨-, h_integral⟩ := hF.petersson_lift_eq_integral h_rank a γ v y_rapid y'_rapid hJ
    rw [h_integral, ← hz, h_real y' z]
    ring
  refine ⟨fun h_zero ↦ ?_, h_norm⟩
  -- If the lift vanishes, `z` is orthogonal to itself; and the series is injective.
  have h_lift : Θ y = 0 := (h_arr.coe_formLift y).symm.trans (congrArg Subtype.val h_zero)
  have z_zero : z = 0 := by
    have h_inner : T.petersson (Θ z) (Θ y) =
        T.quotMeasure.real univ * Z * c * S.petersson z z := h_norm z
    rw [h_lift, ← inner_eq_petersson] at h_inner
    simpa [petersson, hZ, hF.mass_ne_zero, measureReal_univ_ne_zero] using h_inner
  have h_series : rallisSeries (card m) b S₀ᶜ y = 0 := hz.symm.trans (congrArg Subtype.val z_zero)
  exact Subtype.ext (eq_zero_of_rallisSeries_eq_zero h_rank hF.isUnramifiedOn y.property.bounded
    y_level h_series)

/-- Rallis' inner product formula with the series written out as a sum over cosets. Let
`2 * card n < card m` and let `v` be an edge from type `e` to type `e'` for the weights `γ`, `γ'`.
There is `A ≠ 0`, depending only on the spaces `S`, `T` and the real data, with the following
property. Let `a`, `b` be characters of weights `γ`, `γ'`, let the finite datum `F` be sharp for `J`
off `S₀`, of mass `c`, and let `L` be the lift by `v ⊗ F`. Then `L` is injective on the forms of
type `e` fixed by `J`, and for such a form `y` and any form `y'` of type `e`, `⟨L y', L y⟩` is the
absolutely convergent sum of `A * c` times `cosetTerm` (the vacuum coefficient at `q` times
`⟨y', R(q) y⟩`) over the cosets `q` of the points integral off `S₀`. -/
lemma rallis_inner_product_cosetTerm {γ : NumberField.InfinitePlace E → ℤ} {v : PairFock E s t}
    {e : GInf E s → ℂ} {e' : GInf E t → ℂ} (h_edge : IsEdge (realPairWeil γ γ') e e' v)
    (h_rank : 2 * card n < card m) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ (a b : AutChar E) {ψ ψ' : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
      {S₀ : Set (FinPlace E)} {J : Subgroup (Gf E n)} {F : 𝒮 (S.hom T)} {c : ℂ}
      [a.HasWeight γ ψ] [b.HasWeight γ' ψ'], IsSharp b S₀ F J c →
      ∀ y : S.Form e, HasLevel y J →
        let L : S.Form e →ₗ[ℂ] T.Form e' :=
          formLift (pairThetaKer S T a b) e e' ((S.hom T).integrated v F)
        (L y = 0 → y = 0) ∧
        ∀ y' : S.Form e,
          HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦ A * c * cosetTerm (card m) b S₀ᶜ y' y q)
            (T.petersson (L y') (L y)) := by
  obtain ⟨C, hC, h_rallis⟩ :=
    exists_petersson_formLift_eq_rallisSeries (S := S) (T := T) h_edge h_rank
  refine ⟨C, hC, ?_⟩
  intro a b ψ ψ' S₀ J F c _ _ hF y hJ L
  obtain ⟨h_inj, h_norm⟩ : (L y = 0 → y = 0) ∧ ∀ y' : S.Form e,
      T.petersson (L y') (L y) = C * c * S.petersson y' (rallisSeries (card m) b S₀ᶜ y) :=
    h_rallis a b hF y hJ
  refine ⟨h_inj, fun y' ↦ ?_⟩
  -- Expand the pairing with the series term by term.
  have h_series : HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦
      vacuumCoeff (card m) b (cosetRep q).val *
        S.petersson y' fun g : G E s ↦ y (g * (1, (cosetRep q).val)))
      (S.petersson y' (rallisSeries (card m) b S₀ᶜ y)) := by
    simpa only [mul_one] using hasSum_petersson_rallisSeries h_rank b S₀ᶜ
      y.property.isBoundedMeasurable (y'.property.memLp.integrable one_le_two) 1
  rw [h_norm y']
  exact h_series.mul_left (C * c)

end New.SiegelWeil

/-!
## Sharp data modulo 𝔪 and the vacuum sum in rank one

A modulus 𝔪 (`New.Modulus`) is a nonzero ideal of O_E prime to its conjugate; `𝔪.ResidueRing` is
O_E/𝔪 and `𝔪.places` the set of places dividing 𝔪.
-/

namespace New

open HeckeChar Gf Matrix Fintype Valued Rows Space Modulus SiegelWeil WeilData Finset NumberField
variable {E n m : Type} [Field E] [CMType E] {𝔪 : Modulus E} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} [WeilData E] {w : FinPlace E}
  {ν : AutChar E}

/-- A function `Ψ ≠ 0` on matrices modulo `𝔪` is sharp for a group `J` with `J(𝔪) ≤ J ≤ K₀` if `J`
fixes `Ψ ⊗ vac` and, for a fixed matrix `A`, the matrix `A x` lies in the image of `J` whenever
`Ψ x ≠ 0`. Here `K₀ = stdLevel E n` is the group of integral points, `J(𝔪)` consists of those that
are `1` modulo `𝔪`, and `Ψ ⊗ vac = vacuumDatum S T 𝔪 Ψ`. -/
structure SiegelWeil.IsSharpFn (S : Space E n s) (T : Space E m t) (b : AutChar E) (𝔪 : Modulus E)
    (J : Subgroup (Gf E n)) (Ψ : Matrix m n 𝔪.ResidueRing → ℂ) : Prop where
  /-- The principal level of `𝔪` lies in `J`. -/
  principal_le : 𝔪.levelOfSubgroup ⊥ ≤ J
  /-- The points of `J` are integral. -/
  le_stdLevel : J ≤ stdLevel E n
  /-- The function is not zero. -/
  ne_zero : Ψ ≠ 0
  /-- The group `J` fixes the datum `Ψ ⊗ vac`. -/
  fixes : ∀ k ∈ J, pairWeil S T 1 b ((1, k), 1) (vacuumDatum S T 𝔪 Ψ).1 = (vacuumDatum S T 𝔪 Ψ).1
  /-- On the support of `Ψ` the matrix `A x` is the reduction of a point of `J`. -/
  exists_mul_eq : ∃ A : Matrix n m 𝔪.ResidueRing,
    ∀ x : Matrix m n 𝔪.ResidueRing,
      Ψ x ≠ 0 → ∃ k : stdLevel E n, k.1 ∈ J ∧ (𝔪.reductionGL k).1 = A * x

section IsSharpFn

variable {S : Space E n s} {T : Space E m t} {b : AutChar E} {J : Subgroup (Gf E n)}
  {Ψ : Matrix m n 𝔪.ResidueRing → ℂ}

/-- If `Ψ` is sharp for `J`, then at a place of `𝔪` every matrix in the support of the lift of `Ψ`
to finite adelic vectors is primitive: integral with an integral left inverse. -/
lemma SiegelWeil.IsSharpFn.isPrimitiveMatrix (hΨ : IsSharpFn S T b 𝔪 J Ψ) {w : FinPlace E}
    (hw : w ∈ 𝔪.places) {x : m × n → 𝔸f E} (hx : 𝔪.liftFn (Ψ ∘ vecToMatrix) x ≠ 0) :
    IsPrimitiveMatrix (LocInt w).toSubring ((vecToMatrix x).map (evalAt w)) := by
  obtain ⟨A, hA⟩ := hΨ.exists_mul_eq
  refine isPrimitiveMatrix_of_liftFn_ne_zero (of Prod.mk) (fun y hy ↦ ?_) hw hx
  -- The matrix `A y` is invertible, so `y` has a left inverse modulo `𝔪`.
  obtain ⟨k, -, hk⟩ := hA (vecToMatrix y) hy
  have h_inv : (𝔪.reductionGL k)⁻¹.val * A * vecToMatrix y = (1 : Matrix n n 𝔪.ResidueRing) := by
    rw [Matrix.mul_assoc, ← hk, Units.inv_mul]
  exact ⟨_, h_inv⟩

/-- Let `Ψ` be sharp for `J` and let the integral point `g` lie outside `J`. Then `x` and `x ḡ`,
where `ḡ` is `g` modulo `𝔪`, are not both in the support of `Ψ`. -/
lemma SiegelWeil.IsSharpFn.eq_zero_or_eq_zero (hΨ : IsSharpFn S T b 𝔪 J Ψ) {g : stdLevel E n}
    (hg : g.val ∉ J) (x : Matrix m n 𝔪.ResidueRing) :
    Ψ x = 0 ∨ Ψ (x * (𝔪.reductionGL g).val) = 0 := by
  -- Otherwise `g` would be congruent to `(A x)⁻¹ (A x g)`, a quotient of points of `J`.
  obtain ⟨A, hA⟩ := hΨ.exists_mul_eq
  by_contra! ⟨hx, hxg⟩
  obtain ⟨k₁, hk₁_mem, hk₁⟩ := hA _ hx
  obtain ⟨k₂, hk₂_mem, hk₂⟩ := hA _ hxg
  have red_eq : 𝔪.reductionGL (k₂⁻¹ * (k₁ * g)) = 1 := by
    simp [inv_mul_eq_one, Units.ext_iff, hk₁, hk₂, Matrix.mul_assoc]
  have h_mem : k₂.val⁻¹ * (k₁.val * g.val) ∈ J := hΨ.principal_le ⟨_, red_eq, rfl⟩
  exact hg (by simpa [mul_mem_cancel_left, hk₁_mem, hk₂_mem] using h_mem)

/-- An integral finite point `k` of `U(S)` sends the datum `Ψ ⊗ vac` to `b(det k)⁻¹` times the datum
of `x ↦ Ψ (x k̄)`, where `k̄` is `k` modulo `𝔪`. -/
lemma SiegelWeil.pairWeil_stdLevel_vacuumDatum (S : Space E n s) (T : Space E m t) (b : AutChar E)
    (k : stdLevel E n) (Ψ : Matrix m n 𝔪.ResidueRing → ℂ) :
    pairWeil S T 1 b ((1, k.val), 1) (vacuumDatum S T 𝔪 Ψ).1 = ((b.val (detFin s k.val))⁻¹ : ℂ) •
      (vacuumDatum S T 𝔪 fun x : Matrix m n 𝔪.ResidueRing ↦ Ψ (x * (𝔪.reductionGL k).val)).1 := by
  simpa [vacuumDatum, Prod.mk_one_one] using pairWeil_modDatum_stdLevel S T 1 b 𝔪 k 1 Ψ
    Fock.vacVector

/-- Let `Ψ` be sharp for `J` and let the integral point `g` lie outside `J`. Then the matrix
coefficient at `g` of the datum `Ψ ⊗ vac` is zero. -/
lemma SiegelWeil.IsSharpFn.weilMatrixCoeff_eq_zero_of_mem_stdLevel_of_notMem
    (hΨ : IsSharpFn S T b 𝔪 J Ψ) (g : stdLevel E n) (hg : g.val ∉ J) :
    weilMatrixCoeff b (vacuumDatum S T 𝔪 Ψ).1 (vacuumDatum S T 𝔪 Ψ).1 (1, g.val) = 0 := by
  -- The point `g` acts on `Ψ` through its reduction, up to a scalar.
  have h_sum : star (Ψ ∘ vecToMatrix) ⬝ᵥ (fun x ↦ Ψ (x * (𝔪.reductionGL g).val)) ∘ vecToMatrix =
    0 :=
    sum_eq_zero fun x _ ↦ by simpa using hΨ.eq_zero_or_eq_zero hg (vecToMatrix x)
  rw [weilMatrixCoeff, pairWeil_stdLevel_vacuumDatum]
  simp [vacuumDatum, h_sum, ↓ isConjDisjoint_places, ↓ dataInner_schrodingerOp, ↓ localInner_liftFn]

/-- Let `Ψ` be sharp for `J` and let the finite point `g` be integral off `𝔪 𝔪̄` but not everywhere.
Then the matrix coefficient at `g` of the datum `Ψ ⊗ vac` is zero. -/
lemma SiegelWeil.IsSharpFn.weilMatrixCoeff_eq_zero_of_notMem_stdLevel (hΨ : IsSharpFn S T b 𝔪 J Ψ)
    {g : Gf E n} (g_off : g ∈ localLevel n 𝔪.places.conjClosureᶜ) (hg : g ∉ stdLevel E n) :
    weilMatrixCoeff b (vacuumDatum S T 𝔪 Ψ).1 (vacuumDatum S T 𝔪 Ψ).1 (1, g) = 0 := by
  -- If `x` and `x g` were both primitive at the places of `𝔪`, `g` would be integral there, hence
  -- everywhere.
  have h_supp (x : m × n → 𝔸f E) : 𝔪.liftFn (Ψ ∘ vecToMatrix) x = 0 ∨
      𝔪.liftFn (Ψ ∘ vecToMatrix) (matrixToVec (vecToMatrix x * g.val.val)) = 0 := by
    by_contra! ⟨hx, hxg⟩
    have h_integral (w : FinPlace E) (hw : w ∈ 𝔪.places) : g.atPlace w ∈ localIntGL n w := by
      have h_prod : IsPrimitiveMatrix (LocInt w).toSubring
          ((vecToMatrix x).map (evalAt w) * (g.atPlace w).val) := by
        simpa [Matrix.map_mul] using! hΨ.isPrimitiveMatrix hw hxg
      exact (isPrimitiveMatrix_iff_mem_intGL _).1 ((hΨ.isPrimitiveMatrix hw hx).mul_iff.1 h_prod)
    -- Integrality passes from a place to its conjugate by unitarity.
    grind [mem_stdLevel_iff, atPlace_star_mem_iff, mem_localLevel]
  -- The point `g` translates `Ψ` (`omega_schrodingerOp`), so the matrix coefficient is a multiple
  -- of the integral of `conj (Ψ x) * Ψ (x g)`, whose integrand vanishes.
  let p : G E (homSigns s t) := G.onHom ((1, g), 1)
  have h_local : localInner 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix))
      (fun x ↦ 𝔪.liftFn (Ψ ∘ vecToMatrix) (p.2⁻¹.val.val *ᵥ x)) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x _ ↦ by simpa [p] using h_supp x
  rw [vacuumDatum, weilMatrixCoeff, pairWeil_apply,
    (omega_schrodingerOp 𝔪.isConjDisjoint_places _ p _).2,
    map_smul, dataInner_schrodingerOp 𝔪.isConjDisjoint_places, h_local, zero_mul, smul_zero]

/-- The coefficient of a sharp datum. Let the signs of `S` agree or `𝔪 ≠ (1)`, and let `Ψ` be sharp
for `J` relative to `b` (`IsSharpFn`): `Ψ ≠ 0` is a function on `m × n` matrices modulo `𝔪`,
`J(𝔪) ≤ J ≤ K₀` with `K₀ = stdLevel E n`, `J` fixes `Ψ ⊗ vac`, and for a fixed matrix `A` the matrix
`A x` lies in the image of `J` whenever `Ψ x ≠ 0`. Then `Ψ ⊗ vac` (`vacuumDatum`) satisfies
`IsSharp` for `J` off the places of `𝔪 𝔪̄`: its matrix coefficient at the finite points integral off
`𝔪 𝔪̄` is the mean of `|Ψ|²` times the indicator of `J`, and its mass is this mean divided by the
index `[K₀ : J ∩ K₀]`. -/
lemma SiegelWeil.IsSharpFn.isSharp (hΨ : IsSharpFn S T b 𝔪 J Ψ)
    (hn : (∀ i j : n, s i = s j) ∨ Nonempty 𝔪.places) :
    IsSharp b 𝔪.places.conjClosure (vacuumDatum S T 𝔪 Ψ).1 J
      (star Ψ ⬝ᵥ Ψ / card (m × n → 𝔪.ResidueRing) / stdLevelIndex J) := by
  -- On `J` the datum is fixed. If the coefficient at `g` is not zero, some `x` and `x g` lie in the
  -- support of `Ψ`; this makes `g` integral and then puts it in `J` (the two lemmas above). The
  -- hypothesis `hn` serves only for cleanness.
  -- Sums over matrices are sums over vectors indexed by `m × n`.
  have h_curry : star (Ψ ∘ vecToMatrix) ⬝ᵥ (Ψ ∘ vecToMatrix) = star Ψ ⬝ᵥ Ψ :=
    comp_equiv_dotProduct_comp_equiv (star Ψ) Ψ (Equiv.curry m n 𝔪.ResidueRing)
  have h_norm : dataInner (S.hom T) (vacuumDatum S T 𝔪 Ψ).1 (vacuumDatum S T 𝔪 Ψ).1 =
      star Ψ ⬝ᵥ Ψ / card (m × n → 𝔪.ResidueRing) := by
    simp [vacuumDatum, ← h_curry, ↓ isConjDisjoint_places, ↓ dataInner_schrodingerOp,
      ↓ localInner_liftFn]
  refine ⟨?_, (vacuumDatum S T 𝔪 Ψ).2, fun B v hB ↦ ?_, fun g g_off ↦ ?_, by rw [h_norm],
    fun v ↦ hn.imp_right fun ⟨w⟩ ↦ ?_⟩
  · open scoped ComplexOrder in simp [h_norm, dotProduct_star_self_eq_zero, hΨ.ne_zero]
  · -- a vacuum off `𝔪 𝔪̄`
    simp [vacuumDatum, projOn_schrodingerOp_vacElem, hB]
  · -- the coefficient at a point `g` integral off `𝔪 𝔪̄`
    split_ifs with g_lvl
    · exact congrArg _ (hΨ.fixes g g_lvl.1)
    by_cases g_int : g ∈ stdLevel E n
    · exact hΨ.weilMatrixCoeff_eq_zero_of_mem_stdLevel_of_notMem ⟨g, g_int⟩ fun h_mem ↦
        g_lvl ⟨h_mem, g_int⟩
    · exact hΨ.weilMatrixCoeff_eq_zero_of_notMem_stdLevel g_off g_int
  · -- cleanness: if `𝔪` has a place `w`, primitive matrices have a left inverse there
    refine ⟨𝔪.places, 𝔪.liftFn (Ψ ∘ vecToMatrix), w.val, _, 𝔪.isConjDisjoint_places,
      inferInstance, fun y hy ↦ ?_, integrated_schrodingerOp ..⟩
    exact (hΨ.isPrimitiveMatrix w.property hy).2.imp fun L h ↦ h.2

end IsSharpFn

/-- Let `b` have weight `γ` and tame part `ψ` trivial at every finite place not dividing `𝔪`. Let
`F ≠ 0` be a function on `m × n` matrices modulo `𝔪` with `A * x = 1` whenever `F x ≠ 0`. Then `F`
is sharp (`IsSharpFn`) for the principal level `J(𝔪) = 𝔪.levelOfSubgroup ⊥`, the points of
`stdLevel E n` that are `1` modulo `𝔪`: `J(𝔪)` fixes `F ⊗ vac`, and `A x` lies in the trivial image
of `J(𝔪)` modulo `𝔪` whenever `F x ≠ 0`. Examples are the point datum, which is the indicator of the
matrix with blocks `1` and `0`, and the constant `1` for `𝔪 = (1)`. -/
lemma SiegelWeil.isSharpFn_of_mul_eq_one (S : Space E n s) (T : Space E m t) (b : AutChar E)
    {γ : InfinitePlace E → ℤ} {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ} [hb : b.HasWeight γ ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) {F : Matrix m n 𝔪.ResidueRing → ℂ}
    (hF_ne : F ≠ 0) (A : Matrix n m 𝔪.ResidueRing)
    (hA : ∀ x : Matrix m n 𝔪.ResidueRing, F x ≠ 0 → A * x = 1) :
    IsSharpFn S T b 𝔪 (𝔪.levelOfSubgroup ⊥) F := by
  refine
    { principal_le := le_rfl
      le_stdLevel := Subgroup.map_subtype_le _
      ne_zero := hF_ne
      fixes := ?_
      exists_mul_eq := ⟨A, fun x hx ↦ ⟨1, one_mem _, by simp [hA x hx]⟩⟩ }
  rintro _ ⟨k, hk, rfl⟩
  -- An element `k ≡ 1` modulo `𝔪` acts by the scalar `b (det k)⁻¹ = 1`.
  have h_red : 𝔪.reductionGL k = 1 := by simpa using hk
  change pairWeil S T 1 b ((1, k.val), 1) (vacuumDatum S T 𝔪 F).1 = (vacuumDatum S T 𝔪 F).1
  simp [pairWeil_stdLevel_vacuumDatum, h_red, hb.apply_det_eq_charOfTamePart hψ k]

/-- The case of the principal level. Let the signs of `S` agree or `𝔪 ≠ (1)`, let `b` have trivial
tame part off `𝔪`, and let `F ≠ 0` be supported in `{x | A x = 1}`. Then the datum
`vacuumDatum S T 𝔪 F`, which is `F` at `𝔪` and the vacuum elsewhere, satisfies `IsSharp` for
`J(𝔪)` off the places of `𝔪 𝔪̄`. Its mass is the mean of `|F|²` divided by the order of
`GL_n(𝓞/𝔪)`. -/
lemma SiegelWeil.isSharp_vacuumDatum_of_mul_eq_one {S : Space E n s} (T : Space E m t)
    (b : AutChar E) (hn : (∀ i j : n, s i = s j) ∨ Nonempty 𝔪.places) (A : Matrix n m 𝔪.ResidueRing)
    {F : Matrix m n 𝔪.ResidueRing → ℂ} (hA : ∀ x : Matrix m n 𝔪.ResidueRing, F x ≠ 0 → A * x = 1)
    {γ : InfinitePlace E → ℤ} {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ} [hb : b.HasWeight γ ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) (h_norm : star F ⬝ᵥ F ≠ 0) :
    IsSharp b 𝔪.places.conjClosure (vacuumDatum S T 𝔪 F).1 (𝔪.levelOfSubgroup ⊥)
      (star F ⬝ᵥ F / card (m × n → 𝔪.ResidueRing) / card (GL n 𝔪.ResidueRing)) := by
  simpa [stdLevelIndex_levelOfSubgroup] using
    (isSharpFn_of_mul_eq_one S T b hψ (fun h ↦ h_norm (by simp [h])) A hA).isSharp hn

/-! ### The value of the vacuum coefficient -/

omit [WeilData E] in
/-- Let the character `b` have weight `l` and tame part `ψ` (`New.AutChar.HasWeight`). Then `b` is
trivial at an adelic point `u` of `U(1)` that is `1` at infinity, integral at the finite places,
and `1` at every finite place where `ψ` is not trivial. -/
lemma AutChar.HasWeight.apply_eq_one {b : AutChar E} {l : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} (hb : b.HasWeight l ψ) {u : unitary (𝔸 E)}
    (h_inf : u.val.1 = 1) (h_int : u.val.2 ∈ Ô E)
    (h_fin : ∀ w : FinPlace E, ψ w = 1 ∨ u.val.2 w = 1) : b.val u = 1 := by
  have h_tame (w : FinPlace E) : ψ w (reduceAt w ⟨u.val.2, h_int⟩) = 1 := by
    obtain hψ | hu := h_fin w
    · simp [hψ, MulChar.one_apply]
    · have h_red : reduceAt w ⟨u.val.2, h_int⟩ = 1 :=
        (congrArg (IsLocalRing.residue (LocInt w)) (Subtype.ext hu)).trans (map_one _)
      rw [h_red, map_one]
  ext
  simp [hb.apply_eq u h_int, h_tame, h_inf]

/-- Let the finite unitary point `γ` be supported on the places in `A` and their conjugates, and
let the character `b` have a weight and a tame part `ψ` that is trivial there. Let `y` saturate `γ`,
that is `y Ôⁿ = Ôⁿ ∩ γ⁻¹ Ôⁿ`, and let `c` be an idele of the ideal `𝔣` of `det y` that is `1` at
the other places. Then the vacuum coefficient `(b(det γ) * finMultiplier γ ^ M)⁻¹` is
`χ(c) |c| ^ (M / 2) = χ(𝔣) N𝔣 ^ (-M / 2)`, where `χ = b.spaceChar M` is the splitting character. -/
lemma SiegelWeil.vacuumCoeff_eq_spaceChar (M : ℕ) {b : AutChar E} {l : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} (hb : b.HasWeight l ψ) {A : Set (FinPlace E)}
    (hψ : ∀ w ∈ A.conjClosure, ψ w = 1) {γ : Gf E n} (hγ : γ ∈ supportedOn n A)
    {y : GL n (𝔸f E)} (hy : IsSaturating (Ô E).matrix γ.val y) {c : (𝔸f E)ˣ}
    (hc_val : ∀ w : FinPlace E, v (c.val w) = v (y.val.det w))
    (hc_one : ∀ w ∉ A.conjClosure, c.val w = 1) :
    vacuumCoeff M b γ =
      (b.spaceChar M).val (finIdeleIncl c) * √(ideleAbs (finIdeleIncl c)) ^ M := by
  -- The multiplier of `γ` is `υ(c) |c| ^ (-1 / 2)`. As `γ⁻¹` is the adjoint of `γ`, the ideal of
  -- `det (γ y)` is the conjugate of `𝔣`, so `det γ` is `c̄ / c` times a unit that `b` does not see.
  have h_mult : finMultiplier γ = chiFin c :=
    hy.glMultiplier_eq.trans (chiFin_congr fun w ↦ (hc_val w).symm)
  -- The element `u = det γ * c / c̄` of norm one is a unit, and it is `1` off `A` and its
  -- conjugate.
  let u : unitary (𝔸 E) := detFin 1 γ * divStar (finIdeleIncl c)
  have hu_apply (w : FinPlace E) :
      u.val.2 w = γ.val.val.det w * (c.val w * conjLoc (star_star w) (c.val (star w))⁻¹) := by
    have h_inv : c⁻¹.val (star w) = (c.val (star w))⁻¹ := map_units_inv (evalAt (star w)) c
    rw [← h_inv, ← finAdele_star_apply, Submonoid.coe_mul, Prod.snd_mul, coe_divStar, ← map_inv,
      G.det_snd]
    rfl
  have h_inf : u.val.1 = 1 := by
    rw [Submonoid.coe_mul, Prod.fst_mul, coe_divStar, ← map_inv, det_fst]
    ext
    simp
  have h_int : u.val.2 ∈ Ô E := by
    refine mem_Ô.2 fun w ↦ ?_
    calc v (u.val.2 w)
        = v (γ.val.val.det w) * v (y.val.det w) * (v (y.val.det (star w)))⁻¹ := by
          rw [hu_apply, map_mul, map_mul, v_conjLoc, map_inv₀, hc_val, hc_val, mul_assoc]
      _ = v (y.val.det (star w)) * (v (y.val.det (star w)))⁻¹ := by rw [hy.v_det_mul_v_det]
      _ ≤ 1 := mul_inv_le_one_of_le₀ le_rfl zero_le
  have h_off (w : FinPlace E) (hw : w ∉ A.conjClosure) : u.val.2 w = 1 := by
    obtain ⟨hw_notMem, hw_star⟩ : w ∉ A ∧ star w ∉ A := not_or.1 hw
    have h_det : γ.val.val.det w = 1 := ((evalAt w).map_det γ.val.val).trans
      (show (γ.atPlace w).val.det = 1 by simp [mem_supportedOn.1 hγ w hw_notMem hw_star])
    have h_conj : star w ∉ A.conjClosure := not_or.2 ⟨hw_star, by simpa using hw_notMem⟩
    simp [hu_apply, h_det, hc_one w hw, hc_one _ h_conj]
  have h_char : b.val u = 1 := by
    refine hb.apply_eq_one h_inf h_int fun w ↦ ?_
    by_cases hw : w ∈ A.conjClosure
    · exact .inl (hψ w hw)
    · exact .inr (h_off w hw)
  -- So `b (det γ)⁻¹ = b (c / c̄)`, which is `χ(c) υ(c) ^ M`.
  have h_det : (b.val (detFin 1 γ))⁻¹ = b.baseChange.val (finIdeleIncl c) :=
    inv_eq_of_mul_eq_one_right ((map_mul b.val _ _).symm.trans h_char)
  have h_chi : chiFin c = υ.val (finIdeleIncl c) * (√(ideleAbs (finIdeleIncl c)) : ℂ)⁻¹ := rfl
  have h_space : ((b.spaceChar M).val (finIdeleIncl c) : ℂ) =
      b.baseChange.val (finIdeleIncl c) * ((υ.val (finIdeleIncl c) : ℂ) ^ M)⁻¹ := by
    simp [AutChar.spaceChar]
  calc vacuumCoeff M b γ = b.baseChange.val (finIdeleIncl c) * (chiFin c ^ M)⁻¹ := by
        rw [vacuumCoeff, h_mult, mul_inv, ← Circle.coe_inv, h_det]
    _ = (b.spaceChar M).val (finIdeleIncl c) * √(ideleAbs (finIdeleIncl c)) ^ M := by
        rw [h_chi, h_space, mul_pow, mul_inv, inv_pow, inv_inv, mul_assoc]

/-! ### The vacuum sum in rank one -/

open scoped Classical in
/-- The sign −1 if w precedes w̄ in a fixed well-ordering, else 1: so 1 if w = w̄, and one of
each sign on a split pair. The product over the places w above a place of norm q of the real
subfield F of the factors 1 − ε_w q_w^(−k) is 1 − q^(−2k) if this place is split or inert, an
inverse Euler factor of ζ_F(2k). -/
noncomputable def placeSign (w : FinPlace E) : ℂ := if WellOrderingRel w (star w) then -1 else 1

omit [WeilData E] in
lemma norm_placeSign_le (w : FinPlace E) : ‖placeSign w‖ ≤ 1 := by
  simp [placeSign, apply_ite]

omit [WeilData E] in
/-- At a place `w` that differs from its conjugate `w̄`, the signs `placeSign` of `w` and `w̄`
are opposite, so `(1 - ε_w̄ x) (1 - ε_w x) = 1 - x ^ 2`. -/
lemma placeSign_factor_mul (hw : w.IsSplit) (x : ℂ) :
    (1 - placeSign (star w) * x) * (1 - placeSign w * x) = 1 - x ^ 2 := by
  -- Exactly one of `w`, `star w` precedes the other, so the two coefficients are `1` and `-1`.
  have h_one : WellOrderingRel (star w) w ↔ ¬WellOrderingRel w (star w) :=
    ⟨asymm, fun h ↦ ((trichotomous_of _ w (star w)).resolve_left h).resolve_left (Ne.symm hw)⟩
  grind [placeSign, star_star]

/-- The value of the multiplier `glMultiplier` of the Weil representation at `singleGL w (ϖ_w ^ z)`,
the adelic point that is the power `z` of the uniformiser at `w` and `1` elsewhere: it is
`(υ(ϖ_w) √q_w) ^ (-z)` for `z ≤ 0` and `1` for `z ≥ 0`. -/
lemma glMultiplier_singleGL_uniformizer_zpow (z : ℤ) :
    glMultiplier (singleGL w (diagGL fun _ : Unit ↦ uniformizer w ^ z)) =
      (υ.atUniformizer w * √w.q) ^ (-z).toNat := by
  -- Apply `glMultiplier_eq_pow_of_local` with the denominator `y`: both `y` and
  -- `uniformizer w ^ z * y` are integral, and one of them is `1`.
  let g : GL Unit (LocField w) := diagGL fun _ ↦ uniformizer w ^ z
  let y : GL Unit (LocField w) := diagGL fun _ ↦ uniformizer w ^ (-z).toNat
  have h_pow (i : ℕ) : (uniformizer w).val ^ i ∈ LocInt w :=
    (LocInt w).pow_mem ((v_uniformizer w).trans_le (by decide)) i
  have h_sat : IsSaturating (LocInt w).matrix ((singleGL w g).map (evalAt w)) y := by
    -- The witnesses are `l = y⁻¹ - g` and `m = 1` in `y⁻¹ = l + m g`.
    refine ⟨?_, ?_, _, ?_, 1, ?_, eq_add_of_sub_eq rfl⟩
    all_goals cases z <;> simp [g, y, mem_subring_matrix_iff, sub_mem, h_pow]
  have h_ord : (-(v y.val.det).log).toNat = (-z).toNat := by cases z <;> simp [y]
  rw [glMultiplier_eq_pow_of_local (by simp +contextual [g]) h_sat, h_ord]

omit [WeilData E] in
/-- In rank one a point at `w` lies in the integral level `localIntGL Unit w` exactly when its
determinant has order zero. -/
lemma mem_localIntGL_unit_iff (g : GL Unit (LocField w)) :
    g ∈ localIntGL Unit w ↔ (v g.1.det).log = 0 := by
  have h_ne : v g.1.det ≠ 0 := by simp [-det_unique, GeneralLinearGroup.det_ne_zero]
  rw [← WithZero.exp_eq_one, WithZero.exp_log h_ne]
  exact mem_intGL_iff_det.trans (by aesop)

/-- The vacuum coefficient in rank one at a split place `w`. Here `vacuumCoeff M b g = (b(det g) *
finMultiplier g ^ M)⁻¹` is the factor by which `g` changes the matrix coefficient of a vacuum. Let
`ν` have weight `l` and tame part `ψ`, trivial at `w` and `w̄`. Let `γ = ofSplitPlace (ϖ_w ^ z)` be
the unitary point with component `ϖ_w ^ z` at `w`, its conjugate inverse at `w̄` and `1` elsewhere.
Write `υ` for the splitting character (`upsilonU1` on `U(1)`), and
`ν̃(ϖ_u) = ν.baseChange.atUniformizer u` for the value of the base change of `ν`. Then
`vacuumCoeff (2 k) (ν υ ^ k) γ` is `(ν̃(ϖ_u) / q_u ^ k) ^ |z|`, with `u = w̄` if `z ≥ 0` and `u = w`
otherwise, where `q_u` is the norm of `u`. -/
lemma vacuumCoeff_ofSplitPlace_uniformizer_zpow {l : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} (hν : ν.HasWeight l ψ) (hw : w.IsSplit)
    (hψ : ψ w = 1) (hψ_star : ψ (star w) = 1) (k : ℕ) (z : ℤ) :
    vacuumCoeff (2 * k) (ν * upsilonU1 ^ k)
        (ofSplitPlace hw (diagGL fun _ : Unit ↦ uniformizer w ^ z)) =
      (ν.baseChange.atUniformizer (star w) / (star w).q ^ k) ^ z.toNat *
        (ν.baseChange.atUniformizer w / w.q ^ k) ^ (-z).toNat := by
  set g : GL Unit (LocField w) := diagGL fun _ ↦ uniformizer w ^ z with hg
  let χ : HeckeChar E := (ν * upsilonU1 ^ k).baseChange
  -- The multiplier is the product of the factors at `w` and `w̄`.
  have h_mult : finMultiplier (ofSplitPlace hw g) =
      (υ.atUniformizer w * √w.q) ^ (-z).toNat * starRingEnd ℂ
        ((υ.atUniformizer w * √w.q) ^ z.toNat) := by
    have h_split : finMultiplier (ofSplitPlace hw g) = glMultiplier
      (singleGL w g * star (singleGL w g⁻¹)) :=
      rfl
    rw [h_split, glMultiplier_mul_of_map_evalAt_eq_one
        (by grind [evalAt_star_singleGL, evalAt_singleGL_of_ne]),
      glMultiplier_star]
    simp [hg, ← map_inv, Pi.inv_def, ← _root_.zpow_neg, glMultiplier_singleGL_uniformizer_zpow]
  -- The determinant is `x / x̄` for the idele `x` of `det g` at `w`, where `χ` is unramified.
  have h_idele : detFin 1 (ofSplitPlace hw g) = divStar (locFullIdele w g.det) := by
    simp [G.detFin_of_mem_supportedOn (by simp [hw]) (ofSplitPlace_mem_supportedOn hw g),
      ← coe_singleton, detOn_eq_prod]
  have h_det : ((ν * upsilonU1 ^ k).val (detFin 1 (ofSplitPlace hw g)) : ℂ) = χ.atUniformizer w ^
    z := by
    have h_unram : CharUnramifiedAt χ.finPart w :=
      (hν.mul_upsilonU1_pow k).charUnramifiedAt hψ hψ_star
    rw [h_idele]
    exact (h_unram.apply_locFullIdele g.det).trans (by simp [hg])
  have h_unif : χ.atUniformizer w = ν.baseChange.atUniformizer w * υ.atUniformizer w ^ (2 * k) := by
    simp [χ, HeckeChar.atUniformizer, finPart, pow_mul]
  have h_conj : starRingEnd ℂ (υ.atUniformizer w) = (υ.atUniformizer w)⁻¹ := by
    simp [HeckeChar.atUniformizer, finPart, ← Circle.coe_inv_eq_conj]
  rw [vacuumCoeff, h_det, h_mult, h_unif, hν.atUniformizer_star hψ hψ_star, q_star,
    w.coe_q_eq_sq_sqrt]
  have h_ne : υ.atUniformizer w ≠ 0 := Units.ne_zero _
  -- For either sign of `z` the powers of `υ.atUniformizer w` cancel.
  obtain ⟨i, rfl | rfl⟩ := z.eq_nat_or_neg
  all_goals
    simp [h_conj, mul_pow, div_pow]
    field

open scoped Classical in
/-- Let `ν` have weight `l` and tame part `ψ`, trivial at the place `w` and at its conjugate `w̄`,
and let `k > 1`.
There is a family `r` of finite points of `U(1)` supported at `w` and `w̄` such that (a) `r`
represents the cosets of the points integral at `w`, and (b) the sum over `r` of the vacuum
coefficients `vacuumCoeff (2 k) (ν υ ^ k)` is the product over `u ∈ {w, w̄}` of
`(1 - ε_u q_u ^ (-k)) / (1 - ν̃(ϖ_u)⁻¹ q_u ^ (-k))`, where `ν̃` is the base change `ν.baseChange`.
Here `ε = placeSign` is the sign that is `1` when `u = ū` (inert or ramified), and `-1` for one
place and `1` for the other of a split pair `u ≠ ū` (fixed by a well-ordering); `υ` is the splitting
character, `upsilonU1` its restriction to `U(1)`, and `localLevel Unit {w}` consists of the points
integral at `w`. -/
lemma exists_hasSum_vacuumCoeff_at_place {l : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} {k : ℕ} (hν : ν.HasWeight l ψ) (hψ : ψ w = 1)
    (hψ_star : ψ (star w) = 1) (hk : 1 < k) :
    ∃ (ι : Type) (r : ι → supportedOn Unit {w}),
      (∀ g : Gf E Unit, ∃! γ : ι, (r γ).val⁻¹ * g ∈ localLevel Unit {w}) ∧
      HasSum (fun γ : ι ↦ vacuumCoeff (2 * k) (ν * upsilonU1 ^ k) (r γ).val)
        (∏ u ∈ {w, star w},
          (1 - placeSign u / u.q ^ k) / (1 - (ν.baseChange.atUniformizer u)⁻¹ / u.q ^ k)) := by
  -- The coset of `g` is determined by the valuation of its component at `w`. If `star w = w`
  -- there is one coset; if not, the cosets are those of the powers of the uniformiser, and the sum
  -- over `ℤ` splits into two geometric series.
  by_cases hw : star w = w
  · refine ⟨Unit, 1, fun g ↦ ?_, ?_⟩
    · -- Unitarity makes the valuation equal to its negative.
      have h_log : (v (g.atPlace w).val.det).log = 0 := by
        simpa [self_eq_neg] using congrArg (fun A ↦ (v A.det).log) (g.atPlace_star hw)
      simpa [mem_localIntGL_unit_iff, localLevel] using h_log
    · -- Both sides are `1`: the coefficient at `g = 1`, and the factor, as `placeSign w` and
      -- `ν.baseChange.atUniformizer w` are both `1`.
      have h_value : ν.baseChange.atUniformizer w = 1 := by
        rw [HeckeChar.atUniformizer, hν.baseChange_finPart_locIdele_eq_one hw hψ, Units.val_one]
      simp [vacuumCoeff, finMultiplier_eq_one_of_mem, placeSign, irrefl, hw, h_value,
        hk.ne_zero, w.one_lt_q.ne', Prod.mk_one_one, sub_eq_zero]
  -- Split case: `r z` has the component `uniformizer w ^ z` at `w`.
  let r (z : ℤ) : supportedOn Unit {w} :=
    ⟨_, ofSplitPlace_mem_supportedOn hw (diagGL fun _ ↦ uniformizer w ^ z)⟩
  have h_coset (g : Gf E Unit) (z : ℤ) :
      (r z).val⁻¹ * g ∈ localLevel Unit {w} ↔ z = -(v (g.atPlace w).val.det).log := by
    simp [r, mem_localIntGL_unit_iff, localLevel, add_eq_zero_iff_eq_neg, -det_unique,
      GeneralLinearGroup.det_ne_zero]
  refine ⟨ℤ, r, fun g ↦ by simp only [h_coset, existsUnique_eq], ?_⟩
  -- The ratios of the two geometric series.
  let ξ (u : FinPlace E) : ℂ := ν.baseChange.atUniformizer u / u.q ^ k
  have norm_lt (u : FinPlace E) : ‖ξ u‖ < 1 := by simp [ξ, field, one_lt_pow₀, hk.ne_zero]
  have geometric (u : FinPlace E) : HasSum (fun i : ℕ ↦ ξ u ^ i) (1 - ξ u)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (norm_lt u)
  have at_star : ν.baseChange.atUniformizer (star w) = (ν.baseChange.atUniformizer w)⁻¹ :=
    hν.atUniformizer_star hψ hψ_star
  have h_coeff (z : ℤ) : vacuumCoeff (2 * k) (ν * upsilonU1 ^ k) (r z).val =
      ξ (star w) ^ z.toNat * ξ w ^ (-z).toNat :=
    vacuumCoeff_ofSplitPlace_uniformizer_zpow hν hw hψ hψ_star k z
  -- By `placeSign_factor_mul` the numerators multiply to `1 - x ^ 2` with `x = (w.q ^ k)⁻¹`,
  -- and `x ^ 2` is the product of the two ratios.
  have numerator : (1 - placeSign w / w.q ^ k) *
      (1 - placeSign (star w) / (star w).q ^ k) = 1 - ξ (star w) * ξ w := by
    have h_ne : ν.baseChange.atUniformizer w ≠ 0 := Units.ne_zero _
    rw [mul_comm, q_star, div_eq_mul_inv, div_eq_mul_inv, placeSign_factor_mul hw]
    simp [ξ, at_star, q_star, field]
  have denominator : (1 - (ν.baseChange.atUniformizer w)⁻¹ / w.q ^ k) *
      (1 - (ν.baseChange.atUniformizer (star w))⁻¹ / (star w).q ^ k) = (1 - ξ (star w)) *
        (1 - ξ w) := by
    simp [ξ, at_star, q_star]
  have ne_zero (u : FinPlace E) : 1 - ξ u ≠ 0 := (isUnit_one_sub_of_norm_lt_one (norm_lt u)).ne_zero
  have sum_eq : (1 - ξ (star w) * ξ w) / ((1 - ξ (star w)) * (1 - ξ w)) =
      (1 - ξ (star w))⁻¹ + (1 - ξ w)⁻¹ * ξ w := by
    field_simp [ne_zero]
    ring
  rw [prod_pair (Ne.symm hw), div_mul_div_comm, numerator, denominator, sum_eq, funext h_coeff]
  -- The terms with `z ≥ 0` and those with `z < 0` form one geometric series each.
  refine .of_nat_of_neg_add_one (by simpa using geometric (star w)) ?_
  have h_toNat (i : ℕ) : (-1 + -(i : ℤ)).toNat = 0 := by omega
  simpa [pow_succ, add_nonneg, h_toNat] using (geometric w).mul_right (ξ w)

variable {l : InfinitePlace E → ℤ} {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

open scoped Classical in
/-- The sum of the vacuum coefficients at one place of the real subfield. Let `ν` have weight `l`
and tame part `ψ`, trivial at `w` and `w̄`, and let `k > 1`. In rank one the sum `vacuumSum` at
`{w, w̄}` of the coefficients `vacuumCoeff (2 k) (ν υ ^ k)` is the product over `u ∈ {w, w̄}` of
`(1 - ε_u q_u ^ (-k)) / (1 - ν̃(ϖ_u)⁻¹ q_u ^ (-k))`. Here `υ` is the splitting character
(`upsilonU1` on `U(1)`), `ε` is `placeSign`, `ν̃` is the base change `ν.baseChange`, `ϖ_u` is
the uniformiser at `u` and `q_u` the norm of `u`. -/
lemma vacuumSum_pair {k : ℕ} (hν : ν.HasWeight l ψ) (hψ : ψ w = 1) (hψ_star : ψ (star w) = 1)
    (hk : 1 < k) :
    vacuumSum Unit (2 * k) (ν * upsilonU1 ^ k) {w, star w} =
      ∏ u ∈ {w, star w},
        (1 - placeSign u / u.q ^ k) / (1 - (ν.baseChange.atUniformizer u)⁻¹ / u.q ^ k) := by
  obtain ⟨ι, r, h_rep, h_sum⟩ := exists_hasSum_vacuumCoeff_at_place hν hψ hψ_star hk
  have hψ_pair : ∀ u ∈ ({w, star w} : Set (FinPlace E)).conjClosure, ψ u = 1 := by
    grind [star_star, star_inj]
  have h_unram : IsUnramifiedOn (ν * upsilonU1 ^ k) Unit {w, star w} :=
    (hν.mul_upsilonU1_pow k).isUnramifiedOn hψ_pair
  -- A point is integral at `w̄` if and only if it is integral at `w`.
  have h_level : localLevel Unit ({w, star w} : Set (FinPlace E)) = localLevel Unit {w} :=
    Subgroup.ext fun g ↦ by simp [mem_localLevel]
  rw [vacuumSum_eq_tsum h_unram (2 * k) (r := fun γ : ι ↦ (r γ).val)
    (fun γ ↦ supportedOn_mono (by simp) (r γ).property) (by rwa [h_level]), h_sum.tsum_eq]

omit [DecidableEq m] in
/-- The Euler product in rank one. Let `ν` have weight `l` and tame part `ψ`, trivial off the set
`S` of places, let `D = S ∪ S̄`, and let the second space have rank `card m = 2 k` with `k > 1`. The
sum `vacuumSum` of the coefficients `vacuumCoeff (2 k) (ν υ ^ k)` over the cosets at the places off
`D` is `L^D(k)` divided by the Euler product at `k` of the signs `placeSign` off `D`. Here `υ` is
the splitting character (`upsilonU1` on `U(1)`), and `L^D = ν⁻¹.L S` is the `L`-function of the base
change of `ν⁻¹` without the factors at `D`, equal to `ν.L S` (`New.AutChar.HasWeight.L_inv`). If `E`
is unramified over its real subfield `F` off `D`, the denominator is the value at `2 k` of the zeta
function of `F` without the places below `D`. -/
theorem vacuumSum_eq_L_div_eulerProd {k : ℕ} (hν : ν.HasWeight l ψ) {S : Set (FinPlace E)}
    (hψ : ∀ w : FinPlace E, w ∉ S → ψ w = 1) (h_rank : card m = 2 * k) (hk : 1 < k) :
    vacuumSum Unit (card m) (ν * upsilonU1 ^ k) S.conjClosureᶜ =
      ν⁻¹.L S k / eulerProd (S.conjClosureᶜ.indicator placeSign) k := by
  classical
  -- Both sides are products over the pairs `{w, w̄}` off `D`, and `vacuumSum_pair` compares the
  -- factors.
  let D : Set (FinPlace E) := S.conjClosure
  have hD_star (w : FinPlace E) : star w ∈ Dᶜ ↔ w ∈ Dᶜ := by simp [D, and_comm]
  have hψ_off (w : FinPlace E) (hw : w ∈ Dᶜ) : ψ w = 1 := hψ w fun h ↦ hw (.inl h)
  have hk_real : 1 < (k : ℝ) := by exact_mod_cast hk
  let a : FinPlace E → ℂ := heckeCoeff ν⁻¹.baseChange.finPart D
  let ε : FinPlace E → ℂ := Dᶜ.indicator placeSign
  have ha (w : FinPlace E) : ‖a w‖ ≤ 1 := hν.inv.isHeckeOfType.norm_heckeCoeff_le w
  have hε (w : FinPlace E) : ‖ε w‖ ≤ 1 :=
    (norm_indicator_le_norm_self _ w).trans (norm_placeSign_le w)
  have hζ_ne : eulerProd ε k ≠ 0 := by
    simp [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one hε hk_real]
  let loc (w : FinPlace E) : ℂ :=
    (1 - a w * w.q ^ (-(k : ℝ) : ℂ))⁻¹ / (1 - ε w * w.q ^ (-(k : ℝ) : ℂ))⁻¹
  have h_prod : HasProd loc (ν⁻¹.L S k / eulerProd ε k) :=
    (hasProd_eulerProd ha hk_real).div₀ (hasProd_eulerProd hε hk_real) hζ_ne
  have h_loc_one (w : FinPlace E) (hw : w ∉ Dᶜ) : loc w = 1 := by
    simp [loc, a, ε, heckeCoeff, Set.indicator_of_notMem hw]
  have h_loc_eq (w : FinPlace E) (hw : w ∈ Dᶜ) : loc w =
      (1 - placeSign w / w.q ^ k) / (1 - (ν.baseChange.atUniformizer w)⁻¹ / w.q ^ k) := by
    simp [loc, a, ε, heckeCoeff, Set.indicator_of_mem hw, HeckeChar.atUniformizer, Complex.cpow_neg,
      div_eq_mul_inv, mul_comm]
  have h_unram : IsUnramifiedOn (ν * upsilonU1 ^ k) Unit Dᶜ :=
    (hν.mul_upsilonU1_pow k).isUnramifiedOn fun w hw ↦ hψ_off w (hw.elim id (hD_star w).1)
  refine vacuumSum_eq_of_hasProd (by simp [h_rank, hk]) hD_star h_unram h_prod h_loc_one
    fun w hw ↦ ?_
  have hw_star : star w ∈ Dᶜ := (hD_star w).2 hw
  rw [h_rank, vacuumSum_pair hν (hψ_off w hw) (hψ_off _ hw_star) hk]
  exact prod_congr rfl (by simp [h_loc_eq w hw, h_loc_eq _ hw_star])

end New

end
