import Lib.CM.FormalGroup.PrimeNotation
import Lib.GLn.Dual
import New.UpperBound.Kernels.JetConjugatesAndBounds
import New.UpperBound.Objects.Columns

/-!
# Prime-by-prime divisibility measures; short forms span the ramified source forms

This file defines numbers that measure, prime by prime, how divisible the chain of theta lifts on
source forms must be, and shows that short algebraic forms span. `New.AlgForm` is the space of
algebraic forms of weight (κ, e) on the definite unitary group of `New.stdSpace`, with right
translation `New.algFormRep`. The source forms `New.Data.SourceForm` form its subspace fixed by
`New.Data.levelX` 0. `New.Data.piNPlaces` is the set of the f primes dividing π, where ππ̄ = N and f
is the number of infinite places of E. Short forms span at a free level.

## Main definitions and results

* `New.Data.localPrimeSum`: the exponent asked at p for a height y at an infinite place σ.
* `New.Data.localPrimeSumTotal`, `New.Data.gain`: the sum of these exponents over all infinite
  places, and the total exponent asked of the m lifts.
* `New.IsShort`: the values of a form are p-adically integral, and their conjugates under Aut(ℂ)
  have squared norm at most B.
* `New.span_isShort_eq_top`: at a free level K ≤ `New.stdLevel` the short forms span, for an
  explicit B.
* `New.Data.scalingGenerator`: for w ∣ π a scaling z_w at w (`New.Data.IsScalingAt`) of order N − 1
  modulo w.
* `New.Data.ramifiedSourceForms`: the source forms whose translates by the powers of each z_w have
  mean 0; `New.Data.ramifiedSourceForms_eq_range`: they are the image of ∏_{w∣π} (1 − z_w).
* `New.Data.span_isShort_ramifiedSourceForms_eq_top`: the short ramified source forms span the
  ramified source forms.

Notions from other files:
* `New.Parameters`: The fixed parameters: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a
  prime `d` with `d ≡ q₀/2 - 1 mod q₀`.
* `New.weylGauge`: The gauge of ξ at g: the largest p-adic absolute value of a coordinate of
  g⁻¹·ι(ξ), with g⁻¹ acting in weight (κ, e).
* `New.weylNormSq`: The squared norm ξ* G ξ for the integer Gram matrix G = `New.weylGram`.
* `New.Data.chosenLevel`: The principal congruence subgroup of level `New.Data.piM`, whose prime
  divisors are the chosen places.

## Role in the proof

The exponents are used in `New.UpperBound.Divisibility.LocalDivisibility`, the short forms in
`New.Reduction.ShortAndEnough` and `New.Determinant.AuxiliaryForms.SpanningForms`.
-/

noncomputable section

/-!
## Prime-by-prime measures of the divisibility asked of the lifted map

The infinite places of E form the group (ℤ/q₁)^×, where q₁ = `New.Data.q₁` is a multiple of q₀. The
a-places (`New.Data.aPlaces`) are the places whose class is 1 modulo q₀; the b-places
(`New.Data.bPlaces`) are a set of places of class −1 modulo q₀, part of the data. The numbers m (of
lifts), k, x, x₁, b and the long order a = xb (`New.Data.a`) are those of `New.Data`.

* `New.Data.IsSmallNonsplit`, `New.Data.IsPlusMinusOneModLifts`, `New.Data.IsExceptional`: the
  classes of primes in the local proof; `New.Data.ceilLogLifts`: the base-p logarithm of m, rounded
  up.
-/

namespace New.Data

variable {P : Parameters} (D : Data P) (p : ℕ)

/-- The prime sum s_p(y, σ) = v(π_p) ∑_{e ∈ I_p} (y/p^e − w(u(−p^e) σ))⁺. Here v(π_p) is
`New.piPrimeValuation` (1/2 if p = d, and 1 otherwise), I_p is `New.positivePartnerExponents` (the
odd numbers if p is inert, all e ≥ 1 if p = d, none if p splits), and w is `New.Data.weight` (b on
the set `New.Data.bPlaces`, a/x₁ elsewhere). The infinite places form the group (ℤ/q₁)^×, with
q₁ = `New.Data.q₁`; u(ν) = `New.Data.placeOfInt` ν is the place given by the class of ν if ν is
prime to q₁, and the identity place otherwise. -/
def localPrimeSum (y : ℝ) (σ : D.Φ) : ℝ := piPrimeValuation P.d p *
  ∑' e : ℕ, if e ∈ positivePartnerExponents P.d p then
    (y / p ^ e - D.weight (D.placeOfInt (-p ^ e) * σ))⁺ else 0

/-- The total F(p) = ∑_σ s_p(w(σ), σ) of the prime sums s_p = `New.Data.localPrimeSum` p over the
infinite places σ, with w = `New.Data.weight`. -/
def localPrimeSumTotal : ℝ := ∑ σ : D.Φ, D.localPrimeSum p (D.weight σ) σ

/-- The divisibility asked of the chain of m lifts at p: gain(p) = m(∑_τ s_p(a, τ) + k F(p)). The
sum runs over the a-places τ (`New.Data.aPlaces`, the infinite places of class 1 modulo q₀), s_p is
`New.Data.localPrimeSum` p and F(p) is `New.Data.localPrimeSumTotal` p. -/
def gain : ℝ := D.m * (∑ τ ∈ D.aPlaces, D.localPrimeSum p D.a τ + D.k * D.localPrimeSumTotal p)

/-- The natural number p satisfies p < x₁ and χ_K(p) ≠ 1; for prime p, this says that p is below
x₁ and inert or ramified in the quadratic field of the character χ_K = `New.chiK`. -/
abbrev IsSmallNonsplit : Prop := p < D.x₁ ∧ chiK P.d p ≠ 1

/-- The number m of lifts divides p − 1 (truncated at 0) or p + 1; for a prime p, this says
p ≡ ±1 modulo m. -/
def IsPlusMinusOneModLifts : Prop := D.m ∣ p - 1 ∨ D.m ∣ p + 1

open scoped Classical in
/-- The unit of the allowed losses at a non-split p < x₁: f a (log b)²/p, times m if p ≡ ±1 modulo
m. -/
def loss : ℝ := D.f * D.logB ^ 2 * (D.a / p * (if D.IsPlusMinusOneModLifts p then D.m else 1))

/-- The least natural number 𝔯 with m ≤ p^𝔯 (for p > 1). -/
def ceilLogLifts : ℕ := p.clog D.m

/-- The natural number ν_p = 𝔯f(n_m + 𝔯), with 𝔯 = `New.Data.ceilLogLifts` p and f the number of
infinite places of E. Here n_j = k + j(t + 1) (`New.Data.n`) is the rank of the space X_j of stage
j, and m is the number of lifts. -/
def transferExponent : ℕ := D.ceilLogLifts p * D.f * (D.n D.m + D.ceilLogLifts p)

/-- The natural number j_p = ⌈2mfa/p⌉, with f the number of infinite places of E. -/
def collisionExponent : ℕ := ⌈(D.m * (2 * D.f * D.a / p) : ℝ)⌉₊

/-- The order o₀ in (ℤ/q₀)^× of the class of the infinite place named by −p
(`New.Data.placeOfInt`). The places form the group (ℤ/q₁)^×, where q₁ = q₀ · `New.towerDeg` s and
s = `D.towerExp`, and `New.Parameters.placeClass` reduces modulo the divisor q₀ of q₁. For p prime
to q₀, o₀ is the order of −p in (ℤ/q₀)^×. -/
def o₀ : ℕ := orderOf (P.placeClass ⟨towerDeg D.towerExp, rfl⟩ (D.placeOfInt (-p)))

/-- p is exceptional if χ_K(p) = −1, p is not ±1 modulo the number m of lifts, and the order
o₀ = `New.Data.o₀` p is odd and at most 𝔯 = `New.Data.ceilLogLifts` p. Then, for e = o₀, the
infinite place named by −p^e is an a-place. -/
def IsExceptional : Prop :=
  chiK P.d p = -1 ∧ ¬D.IsPlusMinusOneModLifts p ∧ Odd (D.o₀ p) ∧ D.o₀ p ≤ D.ceilLogLifts p

/-- A collision outside ev: e lies in I_p = `New.positivePartnerExponents`, and both τ and its
product with the place named by −p^e are a-places not in ev. -/
def IsCollision (ev : Finset D.Φ) (τ : D.Φ) (e : ℕ) : Prop :=
  e ∈ positivePartnerExponents P.d p ∧ τ ∈ D.aPlaces \ ev ∧
    D.placeOfInt (-p ^ e) * τ ∈ D.aPlaces \ ev

open scoped Classical in
/-- The sum of a/p^e over all pairs (τ, e) that are collisions outside ev
(`New.Data.IsCollision`). -/
def collisionSum (ev : Finset D.Φ) : ℝ :=
  ∑ τ : D.Φ, ∑' e : ℕ, if D.IsCollision p ev τ e then (D.a / p ^ e : ℝ) else 0

end New.Data

/-!
## Short forms and the ramified source forms

* `New.Data.finrank_ker_ramifyingOp_le`: the kernel of ∏_{w∈s} (1 − z_w) has dimension at most
  #s/(N − 1) times the dimension of the source forms.
* `New.Data.isShort_ramifyingOp`: ∏_{w∈s} (1 − z_w) keeps integrality and at most multiplies the
  squared-norm bound by 4^#s.
-/

namespace New

open NumberField Matrix Finset Fintype Submodule Space Rows Norms.L2Operator MvPolynomial

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {κ : InfinitePlace E → ℕ → ℕ} {e : InfinitePlace E → ℤ}

/-! ### Short forms -/

/-- A form φ is B-short if each value φ(g) is integral for Weyl's lattice at g at every p-adic
embedding, and all conjugates of φ(g) under Aut(ℂ) have squared norm at most B. -/
def IsShort (B : ℝ) (φ : AlgForm n κ e) : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], GaugeLe 1 1 φ) ∧
  ∀ (σ : ℂ ≃+* ℂ) (g : Gf E n), weylNormSq (σ ∘ φ.val g) ≤ B

/-- Let G_f = `Gf E n` be the unitary group of the form ∑ xᵢx̄ᵢ over the finite adeles of the CM
field E, and φ an algebraic form on G_f of weight (κ, e): at the infinite place τ the Young diagram
has κ τ h columns of height h, and e τ is the power of the determinant. Let φ be B-short, and let
k ∈ G_f have integral entries (`New.stdLevel`). Then φ minus its right translate by k is
4B-short. -/
lemma IsShort.sub_translate {B : ℝ} {k : Gf E n} {φ : AlgForm n κ e} (hφ : IsShort B φ)
    (hk : k ∈ stdLevel E n) :
    IsShort (4 * B) (φ - algFormRep κ e k φ) := by
  obtain ⟨h_int, h_norm⟩ := hφ
  refine ⟨fun p _ _ ↦ ?_, fun σ g ↦ ?_⟩
  · -- The integral forms are a module, and the gauge is unchanged under g ↦ g * k.
    have translate_int : GaugeLe 1 1 (algFormRep κ e k φ) :=
      fun g ↦ by simpa [weylGauge_mul_of_mem_integralAbove, stdLevel_le_localLevel hk] using h_int p
                   (g * k)
    have h_sub : φ - algFormRep κ e k φ ∈ integralFormsAt (p := p) ⊤ 1 :=
      sub_mem (Submodule.mem_inf.2 ⟨mem_top, h_int p⟩)
        (Submodule.mem_inf.2 ⟨mem_top, translate_int⟩)
    exact (Submodule.mem_inf.1 h_sub).2
  · -- Parallelogram law: `‖a - b‖² = 2 ‖a‖² + 2 ‖b‖² - ‖a + b‖² ≤ 4 B`.
    have parallelogram :
        weylNormSq (σ ∘ (φ.val g - φ.val (g * k))) + weylNormSq (σ ∘ (φ.val g + φ.val (g * k))) =
          2 * weylNormSq (σ ∘ φ.val g) + 2 * weylNormSq (σ ∘ φ.val (g * k)) := by
      simp [weylNormSq, mulVec_sub, mulVec_add]
      ring
    change weylNormSq (σ ∘ (φ.val g - φ.val (g * k))) ≤ 4 * B
    linarith [h_norm σ g, h_norm σ (g * k), weylNormSq_nonneg (σ ∘ (φ.val g + φ.val (g * k)))]

/-- Let y be an array over ℂ_p with entries of absolute value at most 1. The evaluation vector
`New.weylEval` at y has norm at most 1: its coordinates are the values at y of the products of
minors `New.nablaBasis`, which are polynomials with integer coefficients. -/
lemma norm_weylEval_le_one_of_integral {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {y : (Σ _ : InfinitePlace E, n) × ℕ → ℂ_[p]}
    (hy : ∀ x : (Σ _ : InfinitePlace E, n) × ℕ, ‖y x‖ ≤ 1) :
    ‖weylEval (fun _ : InfinitePlace E ↦ n) κ y‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_
  rw [weylEval, ← map_nablaBasis (Int.castRingHom ℂ_[p]), eval_map]
  change eval₂ (Int.castRingHom ℂ_[p]) y (nablaBasis ℤ (fun _ ↦ n) κ i) ∈
    NormedField.valuation.integer
  exact eval₂_mem (by simp) hy

/-- The product of the actions of `G` in weight (κ, e) and of `Z` in weight (κ, 0) is the product
of the powers `(det G_τ) ^ e_τ` times the Schur matrix of `G Z`. The Schur matrix `schur κ z` is the
map that a family `z` of matrices induces on the Weyl module of the diagram with `κ τ h` columns
of height `h` at `τ`. -/
lemma weylRep_mul_weylRep_zero {R : Type} [CommRing R] (G Z : InfinitePlace E → GL n R) :
    weylRep κ e G * weylRep κ 0 Z =
      (∏ τ : InfinitePlace E, (G τ).det ^ e τ) •
        schur κ (fun τ : InfinitePlace E ↦ (G τ).val * (Z τ).val) := by
  simp [weylRep]

/-- Let g lie in G_f = `Gf E n`, the unitary group of rank n over the finite adeles of the CM field
E. A family h of invertible matrices h_τ, indexed by the infinite places τ, acts in weight (κ, e)
(`New.weylRep`) by ∏_τ det(h_τ)^(e_τ) times its action on the Weyl module whose Young diagram at τ
has κ τ h columns of height h.

Let Y₀ and Y_τ be invertible matrices over E such that g⁻¹Y₀ and each g^(−e_τ)Y_τ are integral
(entries in Ô), and let the entries of y be integral elements of ℂ_p. Act on the evaluation vector
at y by Y₀ in weight (κ, 0), multiply by ∏_τ det Y_τ, and act by g⁻¹ in weight (κ, e): the result
has coordinates of absolute value at most 1. Here E goes to ℂ_p by `New.weightEmbedding` at τ, for
the chosen embedding ιₚ of ℂ, and its finite adeles by the extension `New.adeleExtension` of that
map. -/
lemma norm_weylRep_mulVec_det_smul_weylEval_le_one {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {g : Gf E n} {Y₀ : GL n E} {Y : InfinitePlace E → GL n E}
    (hY₀ : IsIntMatrix (Ô E) (g⁻¹.val.val * Y₀.val.map (algebraMap E (𝔸f E))))
    (hY : ∀ τ : InfinitePlace E,
      IsIntMatrix (Ô E) ((g ^ e τ)⁻¹.val.val * (Y τ).val.map (algebraMap E (𝔸f E))))
    {y : (Σ _ : InfinitePlace E, n) × ℕ → ℂ_[p]}
    (hy : ∀ x : ((_ : InfinitePlace E) × n) × ℕ, ‖y x‖ ≤ 1) :
    ‖weylRep κ e
        (fun τ : InfinitePlace E ↦
          GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) g⁻¹.val) *ᵥ
      ((∏ τ : InfinitePlace E, ((Y τ).map (weightEmbedding ιₚ τ)).det) •
          weylRep κ 0 fun τ : InfinitePlace E ↦ Y₀.map (weightEmbedding ιₚ τ)) *ᵥ
        weylEval (fun _ : InfinitePlace E ↦ n) κ y‖ ≤ 1 := by
  -- The vector is a product of determinants of integral matrices times the Schur matrix of
  -- integral matrices applied to the values at `y` of polynomials with integer coefficients.
  set gInv : InfinitePlace E → GL n ℂ_[p] :=
    fun τ ↦ GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) g⁻¹.val
  set Y₀p : InfinitePlace E → GL n ℂ_[p] := fun τ ↦ Y₀.map (weightEmbedding ιₚ τ)
  let d (τ : InfinitePlace E) : ℂ_[p]ˣ :=
    ((Y τ).map (weightEmbedding ιₚ τ)).det * (gInv τ).det ^ e τ
  have h_det (τ : InfinitePlace E) : ‖(d τ).val‖ ≤ 1 := by
    have gInv_pow : gInv τ ^ e τ =
        GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) (g ^ e τ)⁻¹.val := by
      rw [← map_zpow, ← SubgroupClass.coe_zpow, _root_.inv_zpow]
    have det_gInv_pow : ((gInv τ).det ^ e τ).val =
        adeleExtension (weightEmbedding ιₚ τ) (g ^ e τ)⁻¹.val.val.det := by
      rw [← map_zpow, gInv_pow, RingHom.map_det]
      rfl
    have det_Y : ((Y τ).map (weightEmbedding ιₚ τ)).det.val =
        adeleExtension (weightEmbedding ιₚ τ) ((Y τ).val.map (algebraMap E (𝔸f E))).det := by
      simp [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [Units.val_mul, det_gInv_pow, det_Y, ← map_mul, mul_comm, ← det_mul]
    exact norm_adeleExtension_le_one _ (hY τ).det_mem
  have h_entry (τ : InfinitePlace E) (i j : n) : ‖((gInv τ).val * (Y₀p τ).val) i j‖ ≤ 1 := by
    -- Without `map_inv` the inverse of `g` stays inside the image under the embedding.
    simpa [gInv, Y₀p, mul_apply, -map_inv] using
      norm_adeleExtension_le_one (weightEmbedding ιₚ τ) (hY₀ i j)
  have h_prod : ∏ τ, ‖(d τ).val‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun τ _ ↦ norm_nonneg _) fun τ _ ↦ h_det τ
  have h_schur : ‖schur κ (fun τ ↦ (gInv τ).val * (Y₀p τ).val) *ᵥ weylEval _ κ y‖ ≤ 1 :=
    (norm_schur_mulVec_le .refl h_entry _).trans (norm_weylEval_le_one_of_integral hy)
  -- Acting with `g⁻¹` after `Y₀` gives the determinants `d τ` times the Schur matrix of `g⁻¹ Y₀`.
  calc
    _ = ‖(∏ τ, (d τ).val) •
          (schur κ (fun τ ↦ (gInv τ).val * (Y₀p τ).val) *ᵥ weylEval _ κ y)‖ := by
      rw [mulVec_mulVec, Matrix.mul_smul, weylRep_mul_weylRep_zero, smul_smul, ← prod_mul_distrib,
        smul_mulVec, Units.smul_def, Units.coe_prod]
    _ = (∏ τ, ‖(d τ).val‖) *
          ‖schur κ (fun τ ↦ (gInv τ).val * (Y₀p τ).val) *ᵥ weylEval _ κ y‖ := by
      rw [norm_smul, norm_prod]
    _ ≤ 1 := (mul_le_of_le_one_left (norm_nonneg _) h_prod).trans h_schur

/-- Consider the Weyl module whose Young diagram at the infinite place τ of E has κ τ h columns of
height h. A family Y₀ of invertible matrices indexed by the infinite places acts on it by
`New.weylRep` κ 0 Y₀.

Let R be at least the rank n, let the complex matrices of the families Y₀ and Y have entries of
absolute value at most R, and let y have entries of absolute value at most 1. Let M be at least n·f
plus the number of boxes of κ in columns of height below n (`New.boxes`), where f is the number of
infinite places, and let R^(6M) ≤ B. Then ∏_τ det Y_τ times the image under Y₀ of the evaluation
vector at y has squared norm at most B. -/
lemma weylNormSq_det_smul_weylRep_mulVec_weylEval_le [Nonempty n] {R B : ℝ} {M : ℕ}
    (hn_le : Fintype.card n ≤ R)
    (hM : Fintype.card n * Fintype.card (InfinitePlace E) + boxes κ (Fintype.card n) ≤ M)
    (hB : R ^ (6 * M) ≤ B) {Y₀ Y : InfinitePlace E → GL n ℂ}
    (hY₀ : ∀ (τ : InfinitePlace E) (i j : n), ‖(Y₀ τ).val i j‖ ≤ R)
    (hY : ∀ (τ : InfinitePlace E) (i j : n), ‖(Y τ).val i j‖ ≤ R)
    {y : ((_ : InfinitePlace E) × n) × ℕ → ℂ}
    (hy : ∀ x : ((_ : InfinitePlace E) × n) × ℕ, ‖y x‖ ≤ 1) :
    weylNormSq (((∏ τ : InfinitePlace E, (Y τ).det) • weylRep κ 0 Y₀) *ᵥ
      weylEval (fun _ : InfinitePlace E ↦ n) κ y) ≤ B := by
  -- The evaluation vector at `y` is `schur κ` of the square frame of `y` applied to a unit vector,
  -- so the action of `Y₀` gives `schur κ z` of that unit vector.
  have one_le : 1 ≤ R := (Nat.one_le_cast.2 Fintype.card_pos).trans hn_le
  let z (τ : InfinitePlace E) : Matrix n n ℂ :=
    (Y₀ τ).val * GL.squarePart (GL.rowEquivFin fun _ : InfinitePlace E ↦ n) y τ
  let u : WeylIndex n κ → ℂ := weylEval _ κ (permArray fun τ a ↦ GL.rowEquivFin (fun _ ↦ n) τ a)
  have h_ev : weylRep κ 0 Y₀ *ᵥ weylEval (fun _ : InfinitePlace E ↦ n) κ y = schur κ z *ᵥ u := by
    simp [weylRep, z, u, ← GL.schur_squarePart_mulVec (GL.rowEquivFin _) y]
  -- `schur κ z` multiplies the squared norm by at most `∏ ρ τ i ^ λ(τ, i)`, where `∑ i, ρ τ i` is
  -- at most the sum of the squared entries of `z τ`, each at most `(n R)²`.
  obtain ⟨ρ, hρ, schur_le⟩ := weylNormSq_schur_le (κ := κ) .refl z
  have ρ_le (τ : InfinitePlace E) (i : Fin (card n)) : ρ τ i ≤ R ^ 6 :=
    calc (ρ τ i : ℝ) ≤ ∑ a, ∑ b, ‖z τ a b‖ ^ 2 :=
        (NNReal.coe_mono (single_le_sum_of_canonicallyOrdered (by simp))).trans (hρ τ)
      _ ≤ ∑ _ : n, ∑ _ : n, (∑ _ : n, R * 1) ^ 2 := by
        gcongr
        exact norm_sum_le_of_le _ fun k _ ↦ norm_mul_le_of_le (hY₀ τ _ k) (hy _)
      _ = card n ^ 4 * R ^ 2 := by simp [field]
      _ ≤ R ^ 6 := by grw [hn_le, ← pow_add]
  -- `|det Y| ≤ ‖Y‖ ^ n ≤ (n² R) ^ n ≤ (R ^ 3) ^ n`.
  have det_le (τ : InfinitePlace E) : ‖(Y τ).val.det‖ ^ 2 ≤ (R ^ 6) ^ card n := by
    grw [norm_det_le_norm_pow, l2_opNorm_le_of_apply (hY τ), ← sq, hn_le]
    exact le_of_eq (by ring)
  have h_dets : ‖∏ τ, (Y τ).val.det‖ ^ 2 ≤ (R ^ 6) ^ (card n * card (InfinitePlace E)) := by
    simpa [← pow_mul, ← prod_pow, mul_assoc] using
      prod_le_prod₀ (s := univ) (by simp) fun τ _ ↦ det_le τ
  -- The exponents λ(τ, i) add up to the number of boxes.
  have h_schur : weylNormSq (schur κ z *ᵥ u) ≤ (R ^ 6) ^ boxes κ (card n) := by
    grw [schur_le, GL.weylNormSq_weylEval_permArray]
    rw [← FitsRanks.refl.sum_diagramWeight_eq_boxes, ← prod_pow_eq_pow_sum, prod_prod_type, mul_one]
    simp only [NNReal.coe_prod, NNReal.coe_pow, prod_range]
    gcongr
    exact ρ_le _ _
  rw [smul_mulVec, h_ev, Units.smul_def, weylNormSq_smul, Units.coe_prod]
  calc
    _ ≤ (R ^ 6) ^ (card n * card (InfinitePlace E)) * (R ^ 6) ^ boxes κ (card n) :=
      mul_le_mul h_dets h_schur (weylNormSq_nonneg _) (by positivity)
    _ ≤ R ^ (6 * M) := by grw [← pow_add, ← pow_mul, hM]
    _ ≤ B := hB

/-- Let K be a level of the finite adelic unitary group G_f that is free: Γ ∩ gKg⁻¹ is trivial for
every g, where Γ is the group of rational points. Let x be in G_f and let v be a coordinate vector
of weight (κ, e). Suppose that for every prime p and every embedding ι of ℂ in ℂ_p the coordinates
of x⁻¹·ι(v) have absolute value at most 1 (`New.weylGauge`), and that every conjugate of v under
Aut(ℂ) has squared norm at most B (`New.weylNormSq`). Then the delta form at x made from v is
B-short (`New.IsShort`): its values are integral at every p-adic embedding and their conjugates have
squared norm at most B. The delta form is supported on ΓxK, and its value at y is the sum of γ⁻¹·v
over the rational γ with x⁻¹γy ∈ K. -/
lemma isShort_deltaForm {K : Subgroup (Gf E n)} [IsLevel K]
    (free : ∀ g : Gf E n, classAut stdRatPoints K g = ⊥) {B : ℝ} {x : Gf E n}
    {v : WeylIndex n κ → ℂ}
    (h_int : ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], weylGauge (p := p) κ e x v ≤ 1)
    (h_norm : ∀ σ : ℂ ≃+* ℂ, weylNormSq (σ ∘ v) ≤ B) :
    IsShort B (deltaForm stdEmbFin ((stdSpace E n).weightRep κ e) (1 : K →* ℂ) x v).val := by
  set φ : AlgForm n κ e :=
    (deltaForm stdEmbFin ((stdSpace E n).weightRep κ e) (1 : K →* ℂ) x v).val
  have h_order (k : K) : IsOfFinOrder ((1 : K →* ℂ) k) := by simp
  refine ⟨fun p _ _ g ↦ ?_, fun σ g ↦ ?_⟩
  · calc weylGauge κ e (g * 1) (φ.val g) = weylGauge κ e g (φ.val g) := by rw [mul_one]
      _ ≤ weylGauge κ e x v := weylGauge_deltaForm_le h_order
      _ ≤ 1 := h_int p
  · -- At a free level the stabiliser of the coset `x K` is trivial.
    have h_card : Nat.card (classAut stdEmbFin.range K x) = 1 := Subgroup.card_eq_one.2 (free x)
    calc weylNormSq (σ ∘ φ.val g)
        ≤ (Nat.card (classAut stdEmbFin.range K x) : ℝ) ^ 2 * weylNormSq (σ ∘ v) :=
          weylNormSq_deltaForm_le h_order σ x v g
      _ = weylNormSq (σ ∘ v) := by rw [h_card, Nat.cast_one, one_pow, one_mul]
      _ ≤ B := h_norm σ

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Consider algebraic forms on the finite adelic unitary group G_f of rank n over E, of weight (κ,
e): at the infinite place τ the Young diagram has κ τ h columns of height h, and e τ is the power of
the determinant. Let K be a level that is free: Γ ∩ gKg⁻¹ is trivial for every g, where Γ is the
group of rational points. Let N ≠ 0 be a natural number in the different of E, f the number of
infinite places, and M at least n·f plus the number of boxes of κ in columns of height below n. If
B ≥ C^(6M), where C = 6N(fn)² is `New.Space.shortBasisConst` E n N, the forms fixed by K are spanned
by the B-short ones. -/
lemma span_isShort_eq_top {K : Subgroup (Gf E n)} [IsLevel K] [Nonempty n]
    (free : ∀ g : Gf E n, classAut stdRatPoints K g = ⊥)
    {N M : ℕ} [NeZero N] (hN_diff : ↑N ∈ differentIdeal ℤ (𝓞 E))
    (hM : Fintype.card n * Fintype.card (InfinitePlace E) + boxes κ (Fintype.card n) ≤ M) {B : ℝ}
    (hB : (shortBasisConst E n N : ℝ) ^ (6 * M) ≤ B) :
    span ℂ {φ : levelSpace (algFormRep κ e) K | IsShort B φ.val} = ⊤ := by
  -- At a free level a form is a sum of delta forms, one for each class `c`. So it suffices to
  -- find, for each `c`, a spanning set of vectors that are integral at `c` and short.
  refine top_unique fun φ _ ↦ ?_
  rw [← (freeLevelEquiv _ _ 1 free Quot.out_eq).left_inv φ]
  refine sum_mem fun c _ ↦ ?_
  -- `Y g` is a short basis of the lattice of `g`: `g⁻¹ * Y g` is integral, the entries are small.
  choose Y hY_int hY_le using exists_short_basis_stdSpace (E := E) (n := n) hN_diff
  -- The vectors are `A *ᵥ weylEval n κ y`, all entries of `y` roots of unity. `A` is the action of
  -- `Y c` (through the embeddings `weightEmbedding`) in weight `κ`, times the determinants of short
  -- bases for the powers `c ^ e τ`, which absorb the determinant part of the weight; `A f` is its
  -- image under `f`.
  let A {R : Type} [NormedField R] (f : ℂ →+* R) :
      Matrix (WeylIndexFamily (fun _ ↦ n) κ) (WeylIndexFamily (fun _ ↦ n) κ) R :=
    (∏ τ, ((Y (c.out ^ e τ)).map (weightEmbedding f τ)).det) •
      weylRep κ 0 fun τ ↦ (Y c.out).map (weightEmbedding f τ)
  have map_A {R : Type} [NormedField R] (f : ℂ →+* R) (y : (Σ _ : InfinitePlace E, n) × ℕ → ℂ) :
      f ∘ (A (.id _) *ᵥ weylEval _ κ y) = A f *ᵥ weylEval _ κ (f ∘ y) := by
    simp [funext_iff, A, Units.smul_def, f.map_det, weylRep_map, weylEval, mulVec_apply_eq_sum,
      map_eval]
  -- Integral: `c⁻¹` moves the vector to `weylRep κ 0 (c⁻¹ * Y c)` applied to integer polynomials in
  -- `y`, times the determinants of the integral matrices `(c ^ e τ)⁻¹ * Y (c ^ e τ)`.
  have ev_int (p : ℕ) [Fact p.Prime] [PadicPlace p] (y : (Σ _ : InfinitePlace E, n) × ℕ → ℂ)
      (hy : ∀ x, ‖(ιₚ (y x) : ℂ_[p])‖ ≤ 1) :
      weylGauge κ e c.out (A (.id _) *ᵥ weylEval _ κ y) ≤ 1 := by
    rw [weylGauge, map_A]
    exact norm_weylRep_mulVec_det_smul_weylEval_le_one (hY_int _) (fun τ ↦ hY_int _) hy
  -- Short, as all entries of all conjugates of `Y` are at most the constant of the short bases.
  have h_card : Fintype.card n ≤ shortBasisConst E n N := by
    refine Nat.le_of_dvd (Nat.pos_of_neZero _) ?_
    exact dvd_mul_of_dvd_right (dvd_pow (dvd_mul_left _ _) two_ne_zero) _
  have ev_le (σ : ℂ →+* ℂ) (y : (Σ _ : InfinitePlace E, n) × ℕ → ℂ) (hy : ∀ x, ‖σ (y x)‖ ≤ 1) :
      weylNormSq (σ ∘ (A (.id _) *ᵥ weylEval _ κ y)) ≤ B := by
    rw [map_A]
    exact weylNormSq_det_smul_weylRep_mulVec_weylEval_le (Nat.cast_le.2 h_card) hM hB
      (fun τ ↦ hY_le _ (weightEmbedding σ τ)) (fun τ ↦ hY_le _ (weightEmbedding σ τ)) hy
  -- The evaluation vectors span (`GL.ext_weylEval`), and their images under `A` are short.
  have h_zero : (mkQ (span ℂ {φ : levelSpace (algFormRep κ e) K | IsShort B φ.val}) ∘ₗ
      deltaForm stdEmbFin ((stdSpace E n).weightRep κ e) (1 : K →* ℂ) c.out) ∘ₗ
      (A (.id _)).mulVecLin = 0 := by
    -- For each `k > 0` some complex number has order `k`.
    have infinite : {z : ℂ | 0 < orderOf z}.Infinite := (Set.Ioi_infinite 0).preimage
      fun k hk ↦ ⟨_, (Complex.isPrimitiveRoot_exp k hk.ne').eq_orderOf.symm⟩
    refine GL.ext_weylEval 0 (fun y hy _ ↦ ?_) infinite
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, mkQ_apply, Quotient.mk_eq_zero]
    -- The entries of y are roots of unity, hence of absolute value 1 in every normed field.
    have norm_le {R : Type} [NormedField R] (f : ℂ →+* R) (x : (Σ _ : InfinitePlace E, n) × ℕ) :
        ‖f (y x)‖ ≤ 1 := (f.isOfFinOrder (by simpa using hy x)).norm_eq_one.le
    exact subset_span <| isShort_deltaForm free (fun p _ _ ↦ ev_int p y (norm_le _))
      fun σ ↦ ev_le σ y (norm_le _)
  -- As `A` is invertible, every delta form at `c` lies in the span of the short forms.
  have h_unit : IsUnit (A (.id ℂ)) := ((Group.isUnit _).map _).smul _
  have h_surj : Function.Surjective (A (.id ℂ)).mulVecLin :=
    mulVec_surjective_iff_isUnit.2 h_unit
  rw [← LinearMap.zero_comp (A (.id _)).mulVecLin, LinearMap.cancel_right h_surj] at h_zero
  exact (Quotient.mk_eq_zero _).1 (LinearMap.congr_fun h_zero _)

/-- The representation of the norm-one finite adeles, acting by translation by scalar matrices,
on algebraic forms of weight (κ, e) on which J acts through χ. -/
def algFormCentralRep {J : Subgroup (Gf E n)} {χ : J →* ℂ} :
    Representation ℂ (unitary (𝔸f E)) (levelSpace (algFormRep κ e) J χ) :=
  Representation.subrepresentation ((algFormRep κ e).comp (scalarFin n))
    (levelSpace (algFormRep κ e) J χ) fun _ _ hφ ↦ map_mem_levelSpace_of_commute hφ fun k ↦
      (Seesaw.commute_scalarFin k.1).symm.map (algFormRep κ e)

/-- For `φ` in the level space of `algFormRep κ e` for `J` and `χ`, the form underlying
`algFormCentralRep z φ` is `φ` right-translated by the scalar matrix `scalarFin n z` under
`algFormRep κ e`. -/
lemma coe_algFormCentralRep_apply {J : Subgroup (Gf E n)} {χ : J →* ℂ} (z : unitary (𝔸f E))
    (φ : levelSpace (algFormRep κ e) J χ) :
    (algFormCentralRep z φ).val = algFormRep κ e (scalarFin n z) φ.val :=
  rfl

/-- Let `T` be an endomorphism of a complex vector space with `T ^ r = 1`, where `r ≠ 0`. The
vectors `T ^ i φ`, `0 ≤ i < r`, have sum `0` if and only if `φ = ψ - T ψ` for some vector `ψ`. -/
lemma sum_pow_apply_eq_zero_iff_exists_eq_sub {V : Type*} [AddCommGroup V] [Module ℂ V]
    {T : Module.End ℂ V} {r : ℕ} (hr : (r : ℂ) ≠ 0) (hT : T ^ r = 1) (φ : V) :
    ∑ i ∈ range r, (T ^ i) φ = 0 ↔ ∃ ψ : V, φ = ψ - T ψ := by
  rw [← LinearMap.sum_apply]
  constructor
  · intro h_sum
    -- The operator `r - ∑ T ^ i` is the scalar `r` on `φ`, and `1 - T` divides it.
    obtain ⟨S, hS⟩ : ∃ S : Module.End ℂ V, ∑ i ∈ range r, (1 - T ^ i) = (1 - T) * S :=
      dvd_sum fun i _ ↦ one_sub_dvd_one_sub_pow T i
    have h_scalar : (r : ℂ) • φ = S φ - T (S φ) :=
      calc
        (r : ℂ) • φ = (∑ i ∈ range r, (1 - T ^ i)) φ := by simp [h_sum, Nat.cast_smul_eq_nsmul]
        _ = S φ - T (S φ) := by simp [hS]
    refine ⟨(r : ℂ)⁻¹ • S φ, ?_⟩
    rw [map_smul, ← smul_sub, ← h_scalar, inv_smul_smul₀ hr]
  · rintro ⟨ψ, rfl⟩
    calc
      (∑ i ∈ range r, T ^ i) (ψ - T ψ) = ((∑ i ∈ range r, T ^ i) * (1 - T)) ψ := by simp
      _ = 0 := by rw [geom_sum_mul_neg, hT, sub_self, LinearMap.zero_apply]

/-- Let `π` be a complex representation of a commutative group and `z w` a finite family of
elements with `π (z w) ^ r = 1`, where `r ≠ 0`. The vectors whose translates by `z w ^ i`,
`0 ≤ i < r`, have sum `0` for each `w` are the image of the product of the operators `1 - z w`. -/
lemma iInf_ker_sum_pow_eq_range {G V ι : Type*} [CommGroup G] [AddCommGroup V] [Module ℂ V]
    [Fintype ι] (π : Representation ℂ G V) (z : ι → G) {r : ℕ} (hr : (r : ℂ) ≠ 0)
    (hz : ∀ w : ι, π (z w) ^ r = 1) :
    ⨅ w : ι, LinearMap.ker (∑ i ∈ range r, π (z w) ^ i) =
      (π.asAlgebraHom (∏ w : ι, (1 - .of ℂ G (z w)))).range := by
  classical
  -- Compute in the commutative group algebra, with `σ w = ∑ i < r, z w ^ i`.
  let ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V := π.asAlgebraHom
  let y (w : ι) : MonoidAlgebra ℂ G := .of ℂ G (z w)
  let σ (w : ι) : MonoidAlgebra ℂ G := ∑ i ∈ range r, y w ^ i
  have h_mem (φ : V) :
      φ ∈ ⨅ w : ι, LinearMap.ker (∑ i ∈ range r, π (z w) ^ i) ↔ ∀ w, ρ (σ w) φ = 0 := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, ρ, σ, y, map_sum, map_pow,
      Representation.asAlgebraHom_of]
  change _ = (ρ (∏ w, (1 - y w))).range
  refine le_antisymm (fun φ hφ ↦ ?_) ?_
  · -- On a vector killed by `σ w` the element `r - σ w` is the scalar `r`; `1 - z w` divides it.
    have h_scalar (s : Finset ι) : ρ (∏ w ∈ s, (↑r - σ w)) φ = (r : ℂ) ^ #s • φ := by
      induction s using cons_induction with
      | empty => simp
      | cons w s hw ih =>
        have h_factor : ρ (↑r - σ w) φ = (r : ℂ) • φ := by
          simp [(h_mem φ).1 hφ w, Nat.cast_smul_eq_nsmul]
        simp only [prod_cons, map_mul, Module.End.mul_apply, ih, map_smul, h_factor, card_cons,
          pow_succ, mul_smul]
    have h_dvd (w : ι) : 1 - y w ∣ ↑r - σ w := by
      have h_sum : ↑r - σ w = ∑ i ∈ range r, (1 - y w ^ i) := by simp [σ]
      rw [h_sum]
      exact dvd_sum fun i _ ↦ one_sub_dvd_one_sub_pow (y w) i
    obtain ⟨q, hq⟩ : ∏ w, (1 - y w) ∣ ∏ w, (↑r - σ w) :=
      prod_dvd_prod_of_dvd _ _ fun w _ ↦ h_dvd w
    rw [← smul_mem_iff _ (pow_ne_zero _ hr), ← h_scalar univ, hq, map_mul]
    exact ⟨ρ q φ, (Module.End.mul_apply _ _ φ).symm⟩
  · -- `σ w * (1 - z w) = 1 - z w ^ r` acts as `0`.
    rintro _ ⟨ψ, rfl⟩
    refine (h_mem _).2 fun w ↦ ?_
    have h_zero : ρ (σ w * (1 - y w)) = 0 := by
      rw [geom_sum_mul_neg, map_sub, map_one, map_pow, Representation.asAlgebraHom_of, hz,
        sub_self]
    rw [← Module.End.mul_apply, ← map_mul, prod_eq_mul_prod_compl w, ← mul_assoc, map_mul, h_zero,
      zero_mul, LinearMap.zero_apply]

/-- For levels `K' ≤ K` such that `classAut stdRatPoints K g` and `classAut stdRatPoints K' g` are
trivial for every `g`, the dimension of `levelSpace (algFormRep κ e) K'` is `[K : K']` times the
dimension of `levelSpace (algFormRep κ e) K`. -/
lemma relIndex_mul_finrank_levelSpace {K K' : Subgroup (Gf E n)} [IsLevel K] [IsLevel K']
    (h_le : K' ≤ K) (K_free : ∀ g : Gf E n, classAut stdRatPoints K g = ⊥)
    (K'_free : ∀ g : Gf E n, classAut stdRatPoints K' g = ⊥) :
    (K'.relIndex K : ℝ) * Module.finrank ℂ (levelSpace (algFormRep κ e) K) =
      Module.finrank ℂ (levelSpace (algFormRep κ e) K') := by
  -- At a free level the dimension is the number of classes times the dimension of the weight,
  -- and the number of classes is multiplied by the index (`classSum_one_of_le`).
  simp only [finrank_levelSpace_smoothFormRep K_free, finrank_levelSpace_smoothFormRep K'_free,
    Nat.cast_mul, mul_assoc, card_classes_eq_classSum K_free, card_classes_eq_classSum K'_free,
    classSum_one_of_le h_le]

/-- If a set `S` spans a vector space and an endomorphism `f` with image `W` maps `S` into `T`,
then the elements of `W` that lie in `T` span `W`. -/
lemma span_setOf_mem_eq_top_of_eq_range {V : Type*} [AddCommGroup V] [Module ℂ V]
    {f : Module.End ℂ V} {W : Submodule ℂ V} (hW : W = f.range) {S T : Set V}
    (hS : span ℂ S = ⊤) (h_maps : Set.MapsTo f S T) :
    span ℂ {φ : W | φ.val ∈ T} = ⊤ := by
  subst hW
  have h_image : span ℂ (f.rangeRestrict '' S) = ⊤ := by
    rw [span_image, hS, Submodule.map_top, LinearMap.range_rangeRestrict]
  refine eq_top_mono (span_mono ?_) h_image
  rintro _ ⟨φ, hφ, rfl⟩
  exact h_maps hφ

namespace Data

open Representation Module Valued Subgroup

/-! ### The levels and the scaling generators at the primes dividing `D.piN` -/

/-- Neither a place `w` above the prime `D.N` nor its conjugate is a chosen place
(`New.Data.IsChosen`), as the chosen places lie above the smaller primes `D.levelPrime i`. -/
lemma not_isChosen_of_N_mem {P : Parameters} (D : Data P) {w : FinPlace D.E}
    (hw : ↑D.N ∈ w.asIdeal) :
    ¬D.IsChosen w ∧ ¬D.IsChosen (star w) := by
  -- A chosen place has norm a prime `D.levelPrime i < D.N`; `w` and `star w` have norm `D.N`.
  have h_norm : w.q = D.N := P.q_eq_of_modEq_one D.N_modEq_one hw
  have h_not_chosen (u : FinPlace D.E) (hu : u.q = D.N) (h_chosen : D.IsChosen u) : False := by
    obtain ⟨i, -, h_above⟩ := D.isChosen_iff.1 h_chosen
    have h_lt : D.levelPrime i < D.N := Nat.cast_lt.1 (D.levelPrime_mem_Ioo i).2
    have h_eq : D.levelPrime i = D.N := by rw [← D.q_eq_levelPrime h_above, hu]
    exact h_lt.ne h_eq
  exact ⟨h_not_chosen w h_norm, h_not_chosen (star w) (by rw [q_star, h_norm])⟩

/-- Let `D` be admissible data, with CM field `E = D.E` and integer `π = D.piN` of `E` with `π π̄`
prime. The chain of theta lifts passes through hermitian spaces `X_j` of rank `D.n j`, with basis
indexed by `D.X j` and last index `Sum.inr ()`. An element `k` of the finite adelic unitary group
`Gf D.E (D.X j)` of `X_j` lies in the level `D.levelX j` if and only if it lies in `D.chosenLevel`
and, at every prime `w` dividing `π`, the last row of `k_w - 1` vanishes modulo `w`. Here
`k_w = k.atPlace w` is the component of `k` at `w`, and `v` is the valuation of the completion
`E_w`, which gives a uniformizer the value `exp (-1)`. -/
lemma mem_levelX {P : Parameters} (D : Data P) {j : ℕ} {k : Gf D.E (D.X j)} :
    k ∈ D.levelX j ↔
      k ∈ D.chosenLevel ∧
      ∀ w ∈ D.piNPlaces, ∀ b : D.X j,
        v (((k.atPlace w).val - 1) (Sum.inr ()) b) ≤ WithZero.exp (-1) := by
  rw [levelX, Subgroup.mem_inf]
  refine and_congr_right fun hk ↦ ?_
  have h_int : k ∈ stdLevel D.E (D.X j) := levelOf_le_stdLevel hk
  -- Besides integrality, membership says that each entry of the last row of `k - 1` lies in `(π)`.
  have h_cong : k.val ∈ congruenceGL (Ô D.E ∙ algebraMap (𝓞 D.E) (𝔸f D.E) D.piN) Sum.inr ↔
      ∀ b : D.X j, (k.val.val - 1) (Sum.inr ()) b ∈ Ô D.E ∙ algebraMap (𝓞 D.E) (𝔸f D.E) D.piN :=
    ⟨fun h b ↦ h.2 () b, fun h ↦ ⟨h_int, fun _ ↦ h⟩⟩
  have h_entry (b : D.X j) :
      (k.val.val - 1) (Sum.inr ()) b ∈ Ô D.E ∙ algebraMap (𝓞 D.E) (𝔸f D.E) D.piN ↔
        ∀ w ∈ D.piNPlaces, v (((k.atPlace w).val - 1) (Sum.inr ()) b) ≤ WithZero.exp (-1) := by
    rw [sub_one_mem_span_iff_atPlace h_int]
    simp +contextual only [D.mem_piNPlaces, D.intValuation_piN]
  rw [Subgroup.mem_subgroupOf, h_cong, forall_congr' h_entry]
  tauto

/-- Let `S` be a set of places above `N`, and take the finite adelic unitary group of the space
`X_j` of stage `j`. An integral element (`stdLevel`) with component `1` off `S` and its conjugates
lies in the principal congruence subgroup `D.chosenLevel`. -/
lemma inf_supportedOn_le_chosenLevel {P : Parameters} (D : Data P) {j : ℕ}
    {S : Set (FinPlace D.E)} (hS : ∀ w ∈ S, ↑D.N ∈ w.asIdeal) :
    stdLevel D.E (D.X j) ⊓ Gf.supportedOn (D.X j) S ≤ D.chosenLevel :=
  (inf_supportedOn_le_principalLevel fun w hw ↦ D.not_isChosen_of_N_mem (hS w hw)).trans
    (D.principalLevel_le_chosenLevel dvd_rfl)

/-- The scalings at a prime `w` dividing `π = D.piN`: the integral ideles of norm one that are `1`
off `w` and its conjugate. -/
def IsScalingAt {P : Parameters} (D : Data P) (w : D.piNPlaces) (z : unitary (𝔸f D.E)) : Prop :=
  z.val ∈ Ô D.E ∧ ∀ u : FinPlace D.E, u ≠ w.val → star u ≠ w.val → z.val u = 1

/-- Let `D` be admissible data, with CM field `E = D.E`, prime `N = D.N` and integer `π = D.piN` of
`E` with `π π̄ = N`. Let `w` be a prime of `E` dividing `π`; its residue field has `N` elements.
There is a scaling `z` at `w` whose component `z_w` generates the units of the residue field:
`z_w ^ i` is congruent to `1` modulo `w` if and only if `N - 1` divides `i`. -/
lemma exists_isScalingAt_valuation_pow_iff {P : Parameters} (D : Data P) (w : D.piNPlaces) :
    ∃ z : unitary (𝔸f D.E),
      D.IsScalingAt w z ∧ ∀ i : ℕ, v (z.val w ^ i - 1) < 1 ↔ D.N - 1 ∣ i := by
  -- Let `x` be a local unit at `w` that generates the cyclic group of units of the residue field,
  -- which has `D.N - 1` elements; take the idele of `x` divided by its conjugate.
  obtain ⟨x, hx⟩ : ∃ x : (LocInt w.val).unitGroup,
      orderOf ((LocInt w.val).unitGroupToResidueFieldUnits x) = Nat.card (ResField w.val)ˣ :=
    (LocInt w.val).surjective_unitGroupToResidueFieldUnits.exists.1
      IsCyclic.exists_ofOrder_eq_natCard
  have h_split : star w.val ≠ w :=
    (ne_of_mem_of_not_mem w.property (D.isSplitLevel_piNPlaces.star_notMem w w.property)).symm
  have h_order (i : ℕ) : v (((x : (LocField w.val)ˣ) : LocField w.val) ^ i - 1) < 1 ↔
      D.N - 1 ∣ i := by
    rw [← D.isSplitLevel_piNPlaces.q_eq w w.property, ← card_ResField, ← Nat.card_units, ← hx,
      orderOf_dvd_iff_pow_eq_one]
    exact ⟨fun h ↦ Units.ext (residue_eq_iff_valuation_sub_lt_one.2 h),
      fun h ↦ residue_eq_iff_valuation_sub_lt_one.1 (Units.ext_iff.1 h)⟩
  have h_idele {y : (LocField w.val)ˣ} (hy : v y.val = 1) (u : FinPlace D.E) :
      v ((locIdele w.val y).val u) = 1 :=
    mem_idelesUnitOff.1 (locIdele_mem_idelesUnitOff (S := ∅) hy) u (Set.notMem_empty u)
  refine ⟨divStar (locIdele w x), ⟨?_, fun u hu hu_star ↦ ?_⟩, fun i ↦ ?_⟩
  · simp [coe_divStar, ← map_inv, mem_Ô, h_idele, (v.mem_unitGroup_iff _ _).1 x.property]
  · simp [coe_divStar, ← map_inv, hu, hu_star]
  · -- As `w` splits, the component at `w` is `x`.
    simpa [coe_divStar, ← map_inv, h_split, ← WithZero.exp_add] using h_order i

/-- A chosen scaling `z_w` at a prime `w` dividing `π`: it is integral, it is `1` off `w` and its
conjugate, and its component at `w` has order `N - 1` modulo `w`, so it reduces to a generator of
the units of the residue field. -/
def scalingGenerator {P : Parameters} (D : Data P) (w : D.piNPlaces) : unitary (𝔸f D.E) :=
  (D.exists_isScalingAt_valuation_pow_iff w).choose

lemma isScalingAt_scalingGenerator {P : Parameters} (D : Data P) (w : D.piNPlaces) :
    D.IsScalingAt w (D.scalingGenerator w) :=
  (D.exists_isScalingAt_valuation_pow_iff w).choose_spec.1

/-- The `i`-th power of the component at `w` of the chosen scaling `z_w = D.scalingGenerator w` is
congruent to `1` modulo `w` if and only if `N - 1` divides `i`. -/
lemma valuation_scalingGenerator_pow_sub_one_lt_one_iff {P : Parameters} (D : Data P)
    (w : D.piNPlaces) (i : ℕ) :
    v ((D.scalingGenerator w).val w ^ i - 1) < 1 ↔ D.N - 1 ∣ i :=
  (D.exists_isScalingAt_valuation_pow_iff w).choose_spec.2 i

/-- The scalar matrix of a scaling `z` at `w` (integral, and `1` off `w` and its conjugate) lies in
the maximal compact subgroup at `w`. -/
lemma scalarFin_mem_maxCompactAt_of_isScalingAt {P : Parameters} (D : Data P) (w : D.piNPlaces)
    (ι : Type) [Fintype ι] [DecidableEq ι] {z : unitary (𝔸f D.E)} (hz : D.IsScalingAt w z) :
    scalarFin ι z ∈ maxCompactAt ι w := by
  obtain ⟨h_int, h_supp⟩ := hz
  refine ⟨mem_stdLevel.2 fun i j ↦ ?_, Gf.mem_supportedOn.2 fun u hu hu_star ↦ Units.ext ?_⟩
  · simp [scalarFin, diagonal_apply, ite_mem, h_int]
  · rw [scalarFin_atPlace, h_supp u hu hu_star]
    exact diagonal_one

/-- The scalar matrix of the chosen scaling `z_w = D.scalingGenerator w` lies in the maximal compact
subgroup at `w`. -/
lemma scalarFin_scalingGenerator_mem_maxCompactAt {P : Parameters} (D : Data P) (w : D.piNPlaces)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    scalarFin ι (D.scalingGenerator w) ∈ maxCompactAt ι w :=
  D.scalarFin_mem_maxCompactAt_of_isScalingAt w ι (D.isScalingAt_scalingGenerator w)

/-- The scalar matrix, of size `D.X j`, of the chosen scaling `z_w = D.scalingGenerator w` lies in
the principal congruence subgroup `D.chosenLevel`. -/
lemma scalarFin_scalingGenerator_mem_chosenLevel {P : Parameters} (D : Data P) {j : ℕ}
    (w : D.piNPlaces) :
    scalarFin (D.X j) (D.scalingGenerator w) ∈ D.chosenLevel :=
  D.inf_supportedOn_le_chosenLevel (by simp [D.isSplitLevel_piNPlaces.natCast_level_mem])
    (D.scalarFin_scalingGenerator_mem_maxCompactAt w _)

/-- Let `D` be admissible data (`New.Data`), with CM field `E = D.E`, prime `N = D.N` and integer
`π = D.piN` of `E` with `π π̄ = N`, and let `w` be a prime dividing `π`. The chosen scaling
`z_w = D.scalingGenerator w` is an integral finite idele with `z_w z̄_w = 1` that is `1` off `w` and
its conjugate and has order `N - 1` modulo `w`; `scalarFin (D.X j) z_w` is its scalar matrix with
rows indexed by `D.X j`. The `i`-th power of this matrix lies in the level `D.levelX j` if and only
if `N - 1` divides `i`. -/
lemma scalarFin_scalingGenerator_pow_mem_levelX_iff {P : Parameters} (D : Data P) {j : ℕ}
    (w : D.piNPlaces) (i : ℕ) :
    scalarFin (D.X j) (D.scalingGenerator w) ^ i ∈ D.levelX j ↔ D.N - 1 ∣ i := by
  rw [← D.valuation_scalingGenerator_pow_sub_one_lt_one_iff w i, mem_levelX,
    and_iff_right (pow_mem (D.scalarFin_scalingGenerator_mem_chosenLevel w) i)]
  have h_lt (x : WithZero (Multiplicative ℤ)) : x < 1 ↔ x ≤ .exp (-1) := by
    simp [← WithZero.lt_mul_exp_iff_le, ← WithZero.exp_add]
  -- At a place `u` the matrix `z_w ^ i - 1` is the scalar `(z_w u) ^ i - 1`.
  have h_entry (u : FinPlace D.E) :
      ((scalarFin (D.X j) (D.scalingGenerator w) ^ i).atPlace u).val - 1 =
        Matrix.diagonal fun _ ↦ (D.scalingGenerator w).val u ^ i - 1 := by
    simp [← map_pow, scalarFin_atPlace, ← diagonal_one, diagonal_sub]
  simp only [h_entry, h_lt]
  -- The congruence at `w` is the condition on the right; at the other `u ∣ π` the scaling is `1`.
  refine ⟨fun h_cong ↦ ?_, fun h_cong u hu b ↦ ?_⟩
  · simpa only [diagonal_apply_eq] using h_cong w w.property (.inr ())
  obtain rfl | hne := eq_or_ne u w
  · cases b <;> simp [h_cong]
  · have h_star : star u ≠ w := fun h_eq ↦
      D.isSplitLevel_piNPlaces.star_notMem u hu (by simpa only [h_eq] using w.property)
    simp [(D.isScalingAt_scalingGenerator w).2 u hne h_star]

/-! ### Ramified source forms -/

/-- The representation of the norm-one finite adeles U(1)(𝔸_f) on source forms, by right translation
by scalar matrices. -/
def centralRep {P : Parameters} (D : Data P) : Representation ℂ (unitary (𝔸f D.E)) D.SourceForm :=
  algFormCentralRep

/-- On the underlying forms, `z` acts by right translation by its scalar matrix. -/
lemma coe_centralRep_apply {P : Parameters} (D : Data P) (z : unitary (𝔸f D.E)) (φ : D.SourceForm) :
    (D.centralRep z φ).val = algFormRep D.columnCount (D.lastEntry 0) (scalarFin (D.X 0) z) φ.val :=
  rfl

/-- Let `D` be admissible data for the parameters `P`, with CM field `E = D.E`, prime `N = D.N` and
integer `π = D.piN` of `E` with `π π̄ = N`, and let `w` be a prime dividing `π`. The finite adelic
unitary group of `X_j` acts by right translation (`algFormRep`) on the algebraic forms whose weight
at each infinite place `τ` has `D.columnCount τ h` columns of height `h` and last entry
`D.lastEntry j τ`; `levelSpace` is the subspace fixed by the level `D.levelX j`. On it a finite
idele `z` with `z z̄ = 1` acts by translation by its scalar matrix (`algFormCentralRep`). For
`z = D.scalingGenerator w`, which is `1` off `w` and its conjugate and has order `N - 1` modulo `w`,
the `(N - 1)`-th power of this operator is the identity. -/
lemma algFormCentralRep_scalingGenerator_pow {P : Parameters} (D : Data P) {j : ℕ}
    (w : D.piNPlaces) :
    (algFormCentralRep (D.scalingGenerator w) :
      End ℂ (levelSpace (algFormRep D.columnCount (D.lastEntry j)) (D.levelX j))) ^ (D.N - 1) =
        1 := by
  refine LinearMap.ext fun φ ↦ Subtype.ext ?_
  have h_mem : scalarFin (D.X j) (D.scalingGenerator w) ^ (D.N - 1) ∈ D.levelX j :=
    (D.scalarFin_scalingGenerator_pow_mem_levelX_iff w (D.N - 1)).2 dvd_rfl
  rw [← map_pow] at h_mem ⊢
  rw [coe_algFormCentralRep_apply]
  simpa using mem_levelSpace.1 φ.property ⟨_, h_mem⟩

lemma centralRep_scalingGenerator_pow_eq_one {P : Parameters} (D : Data P) (w : D.piNPlaces) :
    D.centralRep (D.scalingGenerator w) ^ (D.N - 1) = 1 :=
  D.algFormCentralRep_scalingGenerator_pow w

/-- The ramified source forms: those for which, at each `w ∣ π`, the translates by the powers
`z_w ^ i`, `0 ≤ i < N - 1`, of the chosen scaling `z_w = D.scalingGenerator w` have sum `0`. -/
def ramifiedSourceForms {P : Parameters} (D : Data P) : Submodule ℂ D.SourceForm :=
  ⨅ w : D.piNPlaces, LinearMap.ker (∑ i ∈ range (D.N - 1), D.centralRep (D.scalingGenerator w) ^ i)

lemma cast_N_sub_one_ne_zero {P : Parameters} (D : Data P) : (↑(D.N - 1) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.sub_ne_zero_of_lt D.N_prime.one_lt)

/-- The product over `w ∈ s` of the operators `1 - z_w` on source forms, where
`z_w = D.scalingGenerator w` acts through `D.centralRep`. -/
def ramifyingOp {P : Parameters} (D : Data P) (s : Finset D.piNPlaces) :
    Module.End ℂ D.SourceForm :=
  D.centralRep.asAlgebraHom (∏ w ∈ s, (1 - .of ℂ _ (D.scalingGenerator w)))

/-- For admissible data `D`, let `π = D.piN` be the integer of `E` with `π π̄ = N`, the prime `D.N`.
For each prime `w` dividing `π` the chosen scaling `z_w = D.scalingGenerator w` acts on source forms
by right translation by its scalar matrix. The ramified source forms, those whose translates by
`z_w ^ i`, `0 ≤ i < N - 1`, have sum `0` for each `w`, are the image of `D.ramifyingOp univ`, the
product of the operators `1 - z_w` over all `w` dividing `π`. -/
lemma ramifiedSourceForms_eq_range {P : Parameters} (D : Data P) :
    D.ramifiedSourceForms = (D.ramifyingOp univ).range :=
  iInf_ker_sum_pow_eq_range D.centralRep D.scalingGenerator D.cast_N_sub_one_ne_zero
    D.centralRep_scalingGenerator_pow_eq_one

/-- Let `D` be admissible data for the parameters `P`, with CM field `E = D.E`, prime `N = D.N` and
integer `π = D.piN` of `E` with `π π̄ = N`, and let `w` be a prime dividing `π`. The finite adelic
unitary group of `X_j` acts by right translation (`algFormRep`) on the algebraic forms whose weight
at each infinite place `τ` has `D.columnCount τ h` columns of height `h` and last entry
`D.lastEntry j τ`. Let `φ` lie in the subspace (`levelSpace`) fixed by the level `D.levelX j`. The
finite idele `z_w = D.scalingGenerator w` is `1` off `w` and its conjugate, has order `N - 1` modulo
`w`, and acts through its scalar matrix (`scalarFin`). The translates of `φ` by `z_w ^ i`,
`0 ≤ i < N - 1`, have sum `0` if and only if `φ = ψ - z_w ψ` for a form `ψ` of the same weight and
level. -/
theorem sum_scalingGenerator_pow_eq_zero_iff_exists_eq_sub {P : Parameters} (D : Data P) {j : ℕ}
    (w : D.piNPlaces) (φ : levelSpace (algFormRep D.columnCount (D.lastEntry j)) (D.levelX j)) :
    ∑ i ∈ range (D.N - 1), algFormRep D.columnCount (D.lastEntry j)
        (scalarFin (D.X j) (D.scalingGenerator w) ^ i) φ.val = 0 ↔
      ∃ ψ : levelSpace (algFormRep D.columnCount (D.lastEntry j)) (D.levelX j),
        φ.val = ψ.val - algFormRep D.columnCount (D.lastEntry j)
          (scalarFin (D.X j) (D.scalingGenerator w)) ψ.val := by
  -- The operator `T` of `z_w` on the forms of this level has `T ^ (N - 1) = 1`.
  let T : End ℂ (levelSpace (algFormRep D.columnCount (D.lastEntry j)) (D.levelX j)) :=
    algFormCentralRep (D.scalingGenerator w)
  have h_iff : ∑ i ∈ range (D.N - 1), (T ^ i) φ = 0 ↔
      ∃ ψ : levelSpace (algFormRep D.columnCount (D.lastEntry j)) (D.levelX j), φ = ψ - T ψ :=
    sum_pow_apply_eq_zero_iff_exists_eq_sub D.cast_N_sub_one_ne_zero
      (D.algFormCentralRep_scalingGenerator_pow w) φ
  simpa only [T, Subtype.ext_iff, Submodule.coe_sum, Submodule.coe_sub, Submodule.coe_zero,
    ← map_pow, coe_algFormCentralRep_apply] using h_iff

/-- For admissible data `D`, let `π = D.piN` be the integer of `E` with `π π̄ = N`, the prime `D.N`.
The source forms `D.SourceForm` are the algebraic forms on the unitary group of `X_0`, of the weight
of `X_0`, fixed by the level `D.levelX 0`. For a prime `u` dividing `π` the chosen scaling
`z_u = D.scalingGenerator u` acts on them by right translation by its scalar matrix. Let `φ` be a
ramified source form: for each `u` its translates by `z_u ^ i`, `0 ≤ i < N - 1`, have sum `0`. Then
for each prime `w` dividing `π` there is a source form `ψ` with `φ = ψ - z_w ψ`. -/
lemma exists_eq_sub_scalingGenerator {P : Parameters} (D : Data P) (w : D.piNPlaces)
    {φ : D.SourceForm} (hφ : φ ∈ D.ramifiedSourceForms) :
    ∃ ψ : D.SourceForm,
      φ.val = ψ.val - algFormRep D.columnCount (D.lastEntry 0)
        (scalarFin (D.X 0) (D.scalingGenerator w)) ψ.val := by
  have h_sum : (∑ i ∈ range (D.N - 1), D.centralRep (D.scalingGenerator w) ^ i) φ = 0 :=
    (Submodule.mem_iInf _).1 hφ w
  refine (D.sum_scalingGenerator_pow_eq_zero_iff_exists_eq_sub w φ).1 ?_
  simpa only [Subtype.ext_iff, LinearMap.sum_apply, Submodule.coe_sum, Submodule.coe_zero,
    ← map_pow, coe_centralRep_apply] using h_sum

/-- At each infinite place `τ`, the sum over heights `h` below the rank of `X_0` of
`h * D.columnCount τ h` is at most `a = D.a`. Here `D.columnCount τ h` counts the columns of height
`h` in the Young diagram of the weight of `D`. So that diagram has at most `a` boxes in those
columns. -/
lemma sum_height_mul_columnCount_le {P : Parameters} (D : Data P) (τ : D.Φ) :
    ∑ h ∈ range (Fintype.card (D.X 0)), h * D.columnCount τ h ≤ D.a := by
  -- The rank is `k`, and below height `k` only columns of height `1` occur, at most `a` of them.
  have h_zero (h : ℕ) (h_lt : h ∈ range D.k) (h_ne : h ≠ 1) : h * D.columnCount τ h = 0 := by
    grind [columnCount]
  rw [card_X, n, zero_mul, add_zero, sum_eq_ite 1 h_zero]
  grind [columnCount]

/-- If a level `K` contains the scalar matrix of the chosen scaling `z_w = D.scalingGenerator w`,
then the index in `K` of its intersection with the level `D.levelX 0` is at least `N - 1`. -/
lemma N_sub_one_le_relIndex_levelX {P : Parameters} (D : Data P) (w : D.piNPlaces)
    {K : Subgroup (Gf D.E (D.X 0))} [hK : IsLevel K]
    (h_mem : scalarFin (D.X 0) (D.scalingGenerator w) ∈ K) :
    D.N - 1 ≤ (D.levelX 0).relIndex K := by
  -- Some power `z_w ^ i` with `0 < i ≤ index` lies in `levelX 0`, and then `N - 1 ∣ i`.
  obtain ⟨i, hi_pos, hi_le, hi_mem, -⟩ := exists_pow_mem_of_relIndex_ne_zero
    (hK.isCompact.relIndex_ne_zero D.isLevel_levelX.isOpen) h_mem
  exact (Nat.le_of_dvd hi_pos
    ((D.scalarFin_scalingGenerator_pow_mem_levelX_iff w i).1 hi_mem)).trans hi_le

/-- For admissible data `D`, a source form `φ` fixed by the norm-one finite idele `z` under
`D.centralRep` is fixed by right translation by the group generated by `D.levelX 0` and the scalar
matrix `scalarFin (D.X 0) z`. -/
lemma coe_mem_levelSpace_sup_zpowers {P : Parameters} (D : Data P) {z : unitary (𝔸f D.E)}
    {φ : D.SourceForm} (hφ : D.centralRep z φ = φ) :
    φ.val ∈ levelSpace (algFormRep D.columnCount (D.lastEntry 0))
      (D.levelX 0 ⊔ zpowers (scalarFin (D.X 0) z)) := by
  let F : Gf D.E (D.X 0) → WeylIndex (D.X 0) D.columnCount → ℂ := φ.val
  have h_level : D.levelX 0 ≤ rightStabilizer F := fun k hk g ↦ by
    simpa using levelSpace_smoothFormRep_apply φ.property 1 g ⟨k, hk⟩
  have h_fixed : algFormRep D.columnCount (D.lastEntry 0) (scalarFin (D.X 0) z) φ.val = φ.val := by
    rw [← coe_centralRep_apply, hφ]
  have h_scalar : scalarFin (D.X 0) z ∈ rightStabilizer F := fun g ↦ by
    have h_apply :
        (algFormRep D.columnCount (D.lastEntry 0) (scalarFin (D.X 0) z) φ.val).val g = F g := by
      rw [h_fixed]
    simpa using h_apply
  refine mem_levelSpace.2 fun k ↦ ?_
  ext g a
  have h_eq : F (g * k) = F g := sup_le h_level (zpowers_le.2 h_scalar) k.property g
  simpa using congrFun h_eq a

/-- For admissible data `D`, let `w` be a prime of `E` dividing `π = D.piN`, where `π π̄ = N` is the
prime `D.N`. The chosen scaling `z_w = D.scalingGenerator w` acts on the space `D.SourceForm` of
source forms through `D.centralRep`, by right translation by its scalar matrix. The source forms
fixed by `z_w` form a subspace of dimension at most `1 / (N - 1)` times the dimension of all source
forms. -/
lemma finrank_ker_one_sub_scalingGenerator_le {P : Parameters} (D : Data P) (w : D.piNPlaces) :
    finrank ℂ (1 - D.centralRep (D.scalingGenerator w)).ker ≤
      (D.N - 1 : ℝ)⁻¹ * finrank ℂ D.SourceForm := by
  classical
  -- The kernel is fixed by the level `K` generated by `levelX 0` and the scalar matrix of
  -- `z_w = D.scalingGenerator w`. Both levels are free, so the dimensions differ by the factor
  -- `[K : levelX 0]`, which is at least `N - 1`.
  let K : Subgroup (Gf D.E (D.X 0)) :=
    D.levelX 0 ⊔ zpowers (scalarFin (D.X 0) (D.scalingGenerator w))
  have hK : K ≤ D.chosenLevel :=
    sup_le inf_le_left (zpowers_le.2 (D.scalarFin_scalingGenerator_mem_chosenLevel w))
  have K_level : IsLevel K :=
    ⟨hK.trans levelOf_le_stdLevel, isOpen_mono le_sup_left D.isLevel_levelX.isOpen⟩
  have index_ge : D.N - 1 ≤ (D.levelX 0).relIndex K :=
    D.N_sub_one_le_relIndex_levelX w (zpowers_le.1 le_sup_right)
  have h_ker : finrank ℂ (1 - D.centralRep (D.scalingGenerator w)).ker ≤
      finrank ℂ (levelSpace (algFormRep D.columnCount (D.lastEntry 0)) K) := by
    rw [← finrank_map_subtype_eq]
    refine finrank_mono (map_le_iff_le_comap.2 fun φ hφ ↦ ?_)
    have h_fixed : D.centralRep (D.scalingGenerator w) φ = φ :=
      (sub_eq_zero.1 (LinearMap.mem_ker.1 hφ)).symm
    exact D.coe_mem_levelSpace_sup_zpowers h_fixed
  have h_rank : Fintype.card (D.X 0) ≤ 2 * D.n D.m := by
    rw [card_X]
    exact (D.n_mono D.m.zero_le).trans (Nat.le_mul_of_pos_left _ two_pos)
  have K_free : ∀ g : Gf D.E (D.X 0), classAut stdRatPoints K g = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel hK h_rank
  have h_dim : ((D.levelX 0).relIndex K : ℝ) *
      finrank ℂ (levelSpace (algFormRep D.columnCount (D.lastEntry 0)) K) =
        finrank ℂ D.SourceForm :=
    relIndex_mul_finrank_levelSpace le_sup_left K_free D.classAut_levelX_zero_eq_bot
  have N_pos : (0 : ℝ) < D.N - 1 := sub_pos.2 (Nat.one_lt_cast.2 D.N_prime.one_lt)
  have cast_index_ge : (D.N - 1 : ℝ) ≤ (D.levelX 0).relIndex K :=
    (Nat.cast_pred D.N_prime.pos).symm.trans_le (Nat.cast_le.2 index_ge)
  refine (le_inv_mul_iff₀ N_pos).2 ?_
  calc (D.N - 1 : ℝ) * finrank ℂ (1 - D.centralRep (D.scalingGenerator w)).ker
      ≤ (D.levelX 0).relIndex K *
          finrank ℂ (levelSpace (algFormRep D.columnCount (D.lastEntry 0)) K) :=
        mul_le_mul cast_index_ge (Nat.cast_le.2 h_ker) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = finrank ℂ D.SourceForm := h_dim

/-- The kernel of a product of two endomorphisms of a finite-dimensional space has dimension at most
the sum of the dimensions of the two kernels. -/
lemma _root_.New.finrank_ker_mul_le {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f g : End ℂ V) : finrank ℂ (f * g).ker ≤ finrank ℂ f.ker + finrank ℂ g.ker := by
  have h_rank : Module.rank ℂ (f.ker.comap g) ≤ Module.rank ℂ f.ker + Module.rank ℂ g.ker := by
    simpa only [Cardinal.lift_id] using g.lift_rank_comap_le f.ker
  simp only [← finrank_eq_rank] at h_rank
  rw [End.mul_eq_comp, LinearMap.ker_comp]
  exact_mod_cast h_rank

lemma ramifyingOp_empty {P : Parameters} (D : Data P) : D.ramifyingOp ∅ = 1 := by
  simp [ramifyingOp]

/-- Adding a prime `w ∉ s` to `s` multiplies `D.ramifyingOp s` on the left by `1 - z_w`, where
`z_w = D.scalingGenerator w` acts on source forms through `D.centralRep`. -/
lemma ramifyingOp_cons {P : Parameters} (D : Data P) (w : D.piNPlaces) {s : Finset D.piNPlaces}
    (hw : w ∉ s) :
    D.ramifyingOp (cons w s hw) = (1 - D.centralRep (D.scalingGenerator w)) * D.ramifyingOp s := by
  simp [ramifyingOp]

/-- For admissible data `D`, let `s` be a finite set of primes of `E` dividing `π = D.piN`, where
`π π̄ = N` is the prime `D.N`. For `w ∈ s` the chosen scaling `z_w = D.scalingGenerator w` acts on
the space `D.SourceForm` of source forms by right translation by its scalar matrix. The kernel of
`D.ramifyingOp s`, the product of the operators `1 - z_w` over `w ∈ s`, has dimension at most
`#s / (N - 1)` times the dimension of all source forms. -/
lemma finrank_ker_ramifyingOp_le {P : Parameters} (D : Data P) (s : Finset D.piNPlaces) :
    finrank ℂ (D.ramifyingOp s).ker ≤ #s * ((D.N - 1 : ℝ)⁻¹ * finrank ℂ D.SourceForm) := by
  induction s using cons_induction with
  | empty => simp [ramifyingOp_empty, End.one_eq_id]
  | cons w s hw ih =>
    have h_ker : finrank ℂ (D.ramifyingOp (cons w s hw)).ker ≤
        finrank ℂ (1 - D.centralRep (D.scalingGenerator w)).ker +
          finrank ℂ (D.ramifyingOp s).ker := by
      rw [D.ramifyingOp_cons w hw]
      exact finrank_ker_mul_le _ _
    calc (finrank ℂ (D.ramifyingOp (cons w s hw)).ker : ℝ)
        ≤ finrank ℂ (1 - D.centralRep (D.scalingGenerator w)).ker +
            finrank ℂ (D.ramifyingOp s).ker := by exact_mod_cast h_ker
      _ ≤ (D.N - 1 : ℝ)⁻¹ * finrank ℂ D.SourceForm +
            #s * ((D.N - 1 : ℝ)⁻¹ * finrank ℂ D.SourceForm) :=
          add_le_add (D.finrank_ker_one_sub_scalingGenerator_le w) ih
      _ = #(cons w s hw) * ((D.N - 1 : ℝ)⁻¹ * finrank ℂ D.SourceForm) := by
          rw [card_cons, Nat.cast_succ, add_one_mul, add_comm]

/-- The ramified source forms have dimension at least `1 - f / (N - 1)` times the dimension of all
source forms, where `f` is the number of infinite places of `E`. -/
lemma le_finrank_ramifiedSourceForms {P : Parameters} (D : Data P) :
    (1 - D.f / (D.N - 1 : ℝ)) * finrank ℂ D.SourceForm ≤ finrank ℂ D.ramifiedSourceForms := by
  have h_rank : (finrank ℂ D.ramifiedSourceForms + finrank ℂ (D.ramifyingOp univ).ker : ℝ) =
      finrank ℂ D.SourceForm := by
    rw [ramifiedSourceForms_eq_range, ← Nat.cast_add, LinearMap.finrank_range_add_finrank_ker]
  have h_ker : finrank ℂ (D.ramifyingOp univ).ker ≤
      D.f / (D.N - 1 : ℝ) * finrank ℂ D.SourceForm := by
    simpa [card_piNPlaces, div_eq_mul_inv, mul_assoc] using D.finrank_ker_ramifyingOp_le univ
  linarith

/-- The proportion `f / (N - 1)` is at most `b⁻⁸`, because `f ≤ b` and `b⁹ + 1 ≤ N`. -/
lemma f_div_N_sub_one_le {P : Parameters} (D : Data P) : D.f / (D.N - 1 : ℝ) ≤ (D.b ^ 8)⁻¹ := by
  have hb : 0 < D.b := HasLogBound.pos D
  have hf : D.f ≤ D.b := D.le_of_hasLogBound
  have hN : D.b ^ 9 ≤ D.N - 1 := le_sub_iff_add_le.2 D.le_of_hasLogBound
  calc D.f / (D.N - 1 : ℝ) ≤ D.b / D.b ^ 9 := by gcongr
    _ = (D.b ^ 8)⁻¹ := by field

/-- If the source form `φ` is `B`-short, then `D.ramifyingOp s φ`, its image under the product of
the operators `1 - z_w` over `w ∈ s`, with `z_w = D.scalingGenerator w` acting by its scalar matrix,
is `4 ^ #s * B`-short. -/
lemma isShort_ramifyingOp {P : Parameters} (D : Data P) (s : Finset D.piNPlaces) {B : ℝ}
    {φ : D.SourceForm} (hφ : IsShort B φ.val) :
    IsShort (4 ^ #s * B) (D.ramifyingOp s φ).val := by
  induction s using cons_induction with
  | empty => simpa [ramifyingOp_empty] using hφ
  | cons w s hw ih =>
    rw [card_cons, pow_succ', mul_assoc]
    simpa [ramifyingOp_cons, coe_centralRep_apply] using
      ih.sub_translate (mem_of_le_of_mem inf_le_left
        (D.scalarFin_scalingGenerator_mem_maxCompactAt w (D.X 0)))

/-- For admissible data `D` (`New.Data`), let `f = D.f` be the number of infinite places of the
field `D.E`, let `x` and `b` be the scales of `D` and `a = x b`, so that
`D.errorUnit = f a (log b)³`. The source forms are spanned by those that are `B`-short for
`B = exp D.errorUnit / 4 ^ f`: their values are `p`-adically integral for every `p`, and all
conjugates of the values have squared norm at most `B`. -/
lemma span_isShort_eq_top {P : Parameters} (D : Data P) :
    span ℂ {φ : D.SourceForm | IsShort (D.errorUnit.exp / 4 ^ D.f) φ.val} = ⊤ := by
  have h_boxes : boxes D.columnCount (Fintype.card (D.X 0)) ≤ D.f * D.a := by
    simpa using sum_le_card_nsmul univ _ D.a fun τ _ ↦ D.sum_height_mul_columnCount_le τ
  -- The base in `h_bound` is `shortBasisConst` for the rank `D.k` of `X_0` and the natural number
  -- `D.q₁ * P.d`, which lies in the different of `E`; `D.errorUnit` bounds its logarithm.
  have h_const : (shortBasisConst D.E (D.X 0) (D.q₁ * P.d) : ℝ) =
      6 * (D.q₁ * P.d) * (D.f * D.k) ^ 2 := by
    simp [n]
  have h_bound : 4 ^ D.f * (6 * (D.q₁ * P.d) * (D.f * D.k) ^ 2 : ℝ) ^
      (6 * (D.k * D.f + D.f * D.a)) ≤ D.errorUnit.exp :=
    Real.le_exp_of_log_le D.le_of_hasLogBound
  have h_rank : Fintype.card (D.X 0) = D.k := by rw [card_X, n, zero_mul, add_zero]
  refine New.span_isShort_eq_top D.classAut_levelX_zero_eq_bot P.conductor_mem_differentIdeal
    (Nat.add_le_add_left h_boxes _) ?_
  rw [le_div_iff₀' (by positivity), h_const, h_rank]
  exact h_bound

/-- The ramified source forms `D.ramifiedSourceForms` are spanned by those that are `B`-short for
`B = exp D.errorUnit`: their values are `p`-adically integral for every `p`, and all conjugates of
the values have squared norm at most `B`. -/
lemma span_isShort_ramifiedSourceForms_eq_top {P : Parameters} (D : Data P) :
    span ℂ {φ : D.ramifiedSourceForms | IsShort D.errorUnit.exp (φ : D.SourceForm).val} = ⊤ := by
  -- The `Z`-short source forms span, and `∏ (1 - z_w)` makes them `4 ^ f Z`-short.
  let Z : ℝ := D.errorUnit.exp / 4 ^ D.f
  have h_maps : Set.MapsTo (D.ramifyingOp univ) {φ : D.SourceForm | IsShort Z φ.val}
      {φ : D.SourceForm | IsShort D.errorUnit.exp φ.val} := by
    intro φ hφ
    simpa [Z, card_piNPlaces, mul_div_cancel₀] using D.isShort_ramifyingOp univ hφ
  exact span_setOf_mem_eq_top_of_eq_range D.ramifiedSourceForms_eq_range D.span_isShort_eq_top
    h_maps

end Data

end New

end
