import New.OneLift.ComparisonOperator.FirstFactors
import New.UpperBound.Divisibility.ChainValuation

/-!
# The lift of a character: denominators, and one group ring element for all twists

Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `ϑ` be a tame character with set of places
(modulus) `Q`, and let `New.Data.CriticalPair.trivialLift` be the lift of `ν ϑ`, a normalised theta
lift from `U(1)` to `U(2 z)`. The number `New.Data.CriticalPair.integralAlgebraicPart` is an integer
multiple of its normalised squared norm `New.Data.CriticalPair.algPart`.

* `New.Data.CriticalPair.trivialLift_apply`: the lift as a finite sum of values of the kernel
  `New.Data.CriticalPair.pointKernel`.
* `New.Data.CriticalPair.weylGauge_denomBound_smul_pointKernel_le_one`:
  `New.Data.CriticalPair.denomBound` times each kernel value is integral at primes prime to the norm
  of `Q`, in terms of the gauge `New.weylGauge`.
* `New.Data.CriticalPair.denomBound_smul_trivialLift_mem_integralForms`,
  `New.Data.CriticalPair.integralAlgebraicPart_mem_integralAway`: so
  `New.Data.CriticalPair.denomBound` times the lift is an integral form away from `Q`, and
  `New.Data.CriticalPair.integralAlgebraicPart` is an integral number away from `Q`.
* `New.Data.CriticalPair.norm_sq_trivialLift_eq_sum`: the squared norm of the lift as a double sum
  of values of the tame character times pairings `New.Data.CriticalPair.kernelPairing` that depend
  on `Q` only.
* `New.Data.TameChar.IsIntegralMeasure`: functions of `ϑ` given, on the tame characters with set
  `Q`, by one element of the group ring of `U(1)(𝔸)` that is integral away from `Q`.
* `New.Data.CriticalPair.isIntegralMeasure_integralAlgebraicPart`: the multiple
  `New.Data.CriticalPair.integralAlgebraicPart` is such a function.

Notions from other files:
* `New.Data.TameChar`: a character of `U(1)(𝔸)` of weight 0 with tame part supported on a finite set
  `Q` of places of norm prime to `D.M * D.N`, `Q` disjoint from its conjugate.
* `New.Data.CriticalPair`: a critical pair, that is, an integer `1 ≤ z ≤ t` and a character `ν` of
  `U(1)(𝔸)` of weight `-c`, with `z ≤ c(v) ≤ 4b` and tame part supported on the chosen places.
* `New.Data.CriticalPair.HasLiftRank`: the index set `n` has `2 z` elements and `z ≥ 2`, for the
  pair `p = (ν, z)`.

## Relation to the literature

This file proves, for this data, versions of known results: integral group-ring elements that
interpolate twisted values of Hecke L-functions (see `New.Congruences.Selmer.ClassSums`), which are
squared norms of theta lifts from U(1) (see `Lib.SiegelWeil.RallisInner.SharpData`). Here only the
side of the squared norms is treated.
-/

noncomputable section

namespace New.Data

open Matrix Fintype LValueData LevelPlaces Parameters Complex Circle Finset Exchange Rows

variable {P : Parameters} {D : Data P} {p : CriticalPair (P := P) D} {n : Type} [Fintype n]
  [DecidableEq n] (H : p.HasLiftRank n) (ϑ : D.TameChar)

/-- `F` is an integral measure at the modulus `Q` of `ϑ`, that is, evaluation on a group ring
element that is integral away from `Q`: there are finitely many points `u a` of `U(1)(𝔸)` and
complex numbers `c a` such that (a) `‖j (c a)‖ ≤ 1` for every prime `l` prime to the norms of the
places in `Q` and every ring map `j : ℂ →+* ℂ_[l]`, and (b) `F ϑ' = ∑ a, c a * ϑ' (u a)` for all
tame `ϑ'` of modulus `Q`. -/
def TameChar.IsIntegralMeasure (F : D.TameChar → ℂ) : Prop :=
  ∃ (α : Type) (_ : Fintype α) (u : α → unitary (𝔸 D.E)) (c : α → ℂ),
    -- (a) the coefficients are integral at every prime that does not divide the norm `ϑ.normQ`
    (∀ a : α, c a ∈ Seesaw.integralAway ϑ.normQ) ∧
    -- (b) on characters of the same modulus, `F` is evaluation on `∑ a, c a [u a]`
    ∀ ϑ' : D.TameChar, ϑ'.Q = ϑ.Q → F ϑ' = ∑ a : α, c a * ϑ'.toAutChar.1 (u a)

/-- If `F` is an integral measure at the modulus `Q` of the tame character `ϑ`, that is, given on
the characters of modulus `Q` by an element of the group ring of `U(1)(𝔸)` that is integral away
from `Q`, then so is `ϑ' ↦ ‖F ϑ'‖ ^ 2`. Its element is the product of that of `F` and the image of
it under the conjugate-linear map with `[u] ↦ [u⁻¹]`. -/
lemma TameChar.IsIntegralMeasure.norm_sq {F : D.TameChar → ℂ} (hF : ϑ.IsIntegralMeasure F) :
    ϑ.IsIntegralMeasure fun ϑ' : D.TameChar ↦ (‖F ϑ'‖ : ℂ) ^ 2 := by
  obtain ⟨α, _, u, c, h_int, eq_sum⟩ := hF
  -- `‖F ϑ'‖² = F ϑ' * conj (F ϑ')` is a double sum, and `conj (ϑ'.toAutChar u) = ϑ'.toAutChar u⁻¹`
  -- the conjugate of `c y` is integral at `j` since `c y` is integral at `j ∘ conj`
  refine ⟨α × α, inferInstance, fun (x, y) ↦ u x * (u y)⁻¹, fun (x, y) ↦ c x * star (c y),
    fun (x, y) ↦ mul_mem (h_int x) fun l _ hl j ↦ h_int y l hl (j.comp (starRingEnd ℂ)),
    fun ϑ' hQ ↦ ?_⟩
  calc (‖F ϑ'‖ : ℂ) ^ 2 = F ϑ' * starRingEnd ℂ (F ϑ') := (mul_conj' _).symm
    _ = ∑ x : α, ∑ y : α, c x * ϑ'.toAutChar.1 (u x) *
          starRingEnd ℂ (c y * ϑ'.toAutChar.1 (u y)) := by
      rw [eq_sum ϑ' hQ, map_sum, univ.sum_mul_sum]
    _ = _ := by
      simp only [sum_prod_type, map_mul, map_inv, Circle.coe_mul, coe_inv_eq_conj,
        mul_mul_mul_comm, RCLike.star_def]

namespace CriticalPair

/-- For a critical pair `p = (ν, z)`, a bound `D.t ≤ exp l` on the number `D.t`, which bounds `z`,
is also the bound `z ≤ exp l`. -/
instance {l : ℝ} [D.HasLogUpper D.t l] : D.HasLogUpper p.z l := D.hasLogUpper_of_le p.z_mem.2

/-! ### The lift as a sum of kernel values, and its integrality -/

/-- The point datum of the pair `p` at the modulus `Q` of `ϑ`, a Schwartz function on the finite
adelic points of `Hom(E, E^n)`. It is the vacuum off the chosen places (the places of the two level
primes of `D`) and the places of `Q`; at these places it is the indicator `identityBlockIndicator`,
taken modulo `levelModulus 1` (the product of all of them), of the columns that reduce to one fixed
basis vector at the chosen places and have the entry `1` in that position at the places of `Q`. The
factor `P.vacuumScale D.towerExp ^ card n` makes the vacuum integral; here `lValueData H ϑ` is the
lift data of `p` twisted by `ϑ`. -/
def pointDatum : ((stdSpace D.E Unit).hom (stdSpace D.E n)).finitePart :=
  P.vacuumScale D.towerExp ^ Fintype.card (n × Unit) •
    vacuumDatum (stdSpace D.E Unit) (stdSpace D.E n) ((lValueData H ϑ).descentPair.levelModulus 1)
      (lValueData H ϑ).descentPair.identityBlockIndicator

/-- The kernel of the pair `p` twisted by `ϑ`: for finite points `g` of `U(1)` and `h` of `U(2 z)`,
the vector of derivatives at zero (jet) of the theta function of `pointDatum H ϑ` at `(g, h)`, in
the weight `κ` of the lift, with one coordinate for each index in the basis `WeylIndexFamily` of
that weight. The variables are scaled by `star D.piMBar * P.jetScale D.towerExp`: the period scale
of the Taylor series at the exponent `D.towerExp` that picks the field `D.E` in its tower, times the
conjugate of `D.piMBar`, an integer of `P.K` of norm the product of the two level primes. -/
abbrev pointKernel :
    Gf D.E Unit → Gf D.E n → WeylIndexFamily (fun _ ↦ n) (lValueData H ϑ).descentPair.columnCount →
      ℂ :=
  (lValueData H ϑ).kernelValue (star ↑D.piMBar * P.jetScale D.towerExp) (pointDatum H ϑ)

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
let `ϑ` be a tame character, and let `g`, `h` be finite adelic points of `U(1)` and `U(n)` over
`D.E`. For `X = lValueData H ϑ`, the lift data of `ν ϑ`, the form `X.kernelForm g` on `U(n)` is the
theta kernel at `g` of the block datum `X.descentPair.blockDatum`, with unscaled derivatives. Its
value at `h`, times the normalising factor, is the sum of the values of the scaled theta kernel
`pointKernel H ϑ` at `(g * twistResidueLift A, h)`. Here `A` runs over the families of units of the
residue fields at the modulus of `ϑ`, and `twistResidueLift A` is an integral lift of `A⁻¹`.

The factor is `a ^ card n * b ^ p.rowLengthSum`. The number `a = P.vacuumScale D.towerExp` makes the
vacuum Schwartz function of rank one integral. The number `b` scales the variables of the Taylor
series: it is the period scale `P.jetScale D.towerExp` times the conjugate of `D.piMBar`, an integer
of `P.K` of norm `D.M`. -/
lemma smul_kernelForm_apply (H : p.HasLiftRank n) (ϑ : D.TameChar) (g : Gf D.E Unit)
    (h : Gf D.E n) :
    (P.vacuumScale D.towerExp ^ card n * (star (D.piMBar : ℂ) * P.jetScale D.towerExp) ^
      p.rowLengthSum) •
        (lValueData H ϑ).kernelForm g h =
      ∑ A : TwistGL (D.levelPlaces ϑ) Unit,
        pointKernel H ϑ (g * (D.levelPlaces ϑ).twistResidueLift A) h := by
  let X : LValueData D.E n := lValueData H ϑ
  have boxes_eq : boxes X.descentPair.columnCount (card n) = p.rowLengthSum := by
    simp [X, boxes, DescentPair.columnCount, mixedWeight, (lValueData H ϑ).one_lt_card,
      Pi.single_apply]
  have form_eq : X.kernelForm g h = ∑ A : TwistGL (D.levelPlaces ϑ) Unit, X.kernelValue 1
      (vacuumDatum (stdSpace D.E Unit) (stdSpace D.E n) (X.descentPair.levelModulus 1)
        X.descentPair.identityBlockIndicator) (g * (D.levelPlaces ϑ).twistResidueLift A) h := by
    simp [X, vacuumDatum, kernelForm, kernelValue, DescentPair.blockDatum_eq_sum_modDatum,
      sum_mulVec, rep_apply_apply]
  -- the two scales of `pointKernel` come out of the datum and of the jets as powers
  simp [X, form_eq, smul_sum, kernelValue, pointDatum, boxes_eq, smul_smul, smul_mulVec,
    schurJet_jetSeries_eq_smul (isLiftWeight _) (_ * _)]

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
and let `ϑ` be a tame character. The form `trivialLift H ϑ` is the normalised theta lift of `ν ϑ`
from `U(1)` to `U(n)`; the character is part of the Weil action, so that the function lifted is the
constant `1`. Its value at a finite adelic point `h` of `U(n)` is the sum of the values of the theta
kernel `pointKernel H ϑ` at `(c.1.out * twistResidueLift c.2, h)`. Here `c.1` runs over the double
cosets of the finite adelic `U(1)` by its rational points and `D.chosenLevel`, `c.1.out` is a
representative, `c.2` runs over the families of units of the residue fields at the modulus of `ϑ`,
and `twistResidueLift c.2` is an integral lift of the inverse family. -/
lemma trivialLift_apply (H : p.HasLiftRank n) (ϑ : D.TameChar) (h : Gf D.E n) :
    trivialLift H ϑ h =
      ∑ c : StdClasses (n := Unit) D.chosenLevel × TwistGL (D.levelPlaces ϑ) Unit,
        pointKernel H ϑ (c.1.out * (D.levelPlaces ϑ).twistResidueLift c.2) h := by
  -- the classes of `U(1)` at this level have no automorphisms, so the class sum is a plain sum
  have classAut_eq (g : Gf D.E Unit) : classAut (stdSpace D.E Unit).Γf D.chosenLevel g = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel le_rfl (by simpa using D.nat_le_of_hasLogBound) g
  have lift_eq : (lValueData H ϑ).trivialLift =
      ∑ c : StdClasses (n := Unit) D.chosenLevel, (lValueData H ϑ).kernelForm c.out := by
    change classSum (stdSpace D.E Unit).Γf D.chosenLevel (lValueData H ϑ).kernelForm = _
    rw [classSum, ← finsum_eq_sum_of_fintype]
    exact finsum_congr fun c ↦ by simp [classAut_eq]
  rw [sum_prod_type, trivialLift, lift_eq]
  simp only [← smul_kernelForm_apply, apply_eq_evalForm, map_smul, map_sum, smul_sum]

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
let `ϑ` be a tame character, `l` a prime that does not divide the norm of the modulus of `ϑ`, `j` an
embedding of `ℂ` into `ℂ_[l]`, and `g`, `h` finite adelic points of `U(1)` and `U(n)`. Let `M = D.M`
be the product of the two level primes, `f = D.f` the number of infinite places of `D.E`, and
`d = P.d` the prime with `P.K = ℚ(√-d)`. Then `p.denomBound = M ^ (4 f z) * (M d) ^ p.rowLengthSum`
times the value at `(g, h)` of the theta kernel `pointKernel H ϑ` has gauge at most `1` at the point
`h` with respect to `j`: the inverse of `h`, acting in the highest weight of the lift with no power
of the determinant, moves it to a vector whose coordinates have absolute value at most `1`. -/
lemma weylGauge_denomBound_smul_pointKernel_le_one (H : p.HasLiftRank n) (ϑ : D.TameChar) {l : ℕ}
    [Fact l.Prime] {j : PadicPlace l} (g : Gf D.E Unit) (h : Gf D.E n) (hl : l.Coprime ϑ.normQ) :
    weylGauge (ι := j) (lValueData H ϑ).descentPair.columnCount 0 h
      ((p.denomBound : ℂ) • pointKernel H ϑ g h) ≤ 1 := by
  -- `p.denomBound` clears the denominators of the datum `pointDatum H ϑ` and those of the jets; so
  -- the kernel of `p.denomBound • pointDatum H ϑ` does not increase gauges, and the vector `1` has
  -- gauge one.
  let X : LValueData D.E n := lValueData H ϑ
  let datumDenom : ℕ := (D.M ^ 1) ^ (2 * Core.numInfPlaces (P.E D.towerExp) * card (n × Unit))
  have h_std : (datumDenom : ℂ) • (pointDatum H ϑ).1 ∈ Parameters.standardData _ (D.M ^ 1 : ℕ) :=
    smul_vacuumDatum_mem_standardData normQ_mul_M_pow_mem_modulus
      (by grind [DescentPair.identityBlockIndicator, one_mem, zero_mem]) hl
  have h_den : datumDenom * (D.M ^ 1 * P.d) ^ boxes X.descentPair.columnCount (card n) ∣
      p.denomBound := by
    simp [X, datumDenom, denomBound, boxes, DescentPair.columnCount, mixedWeight,
      (lValueData H ϑ).one_lt_card, ← H.1, Pi.single_apply]
  have h_raises : (p.denomBound : ℂ) • pointDatum H ϑ ∈
      (thetaKernel X.isLiftWeight (star ↑D.piMBar * P.jetScale D.towerExp) X.charW_hasWeight
        X.charV_hasWeight ⊤).raises 1 1 1 :=
    smul_mem_raises_of_dvd _ h_std norm_star_piMBar_le_one h_den
  -- the jet at `(g, h)` applied to `1` is the kernel value by definition; the weight of `U(1)` is
  -- trivial, so `1` has gauge one
  simpa +contextual [weylGauge, weylRep, schur_eq_one] using! h_raises g h 1

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
let `ϑ` be a tame character, `l` a prime that does not divide the norm of the modulus of `ϑ`, and
`j` an embedding of `ℂ` into `ℂ_[l]`. Then the theta lift `trivialLift H ϑ` of `ν ϑ` to `U(n)`,
times the natural number `p.denomBound`, is a form integral at `j`. -/
lemma denomBound_smul_trivialLift_mem_integralForms (H : p.HasLiftRank n) (ϑ : D.TameChar) {l : ℕ}
    [Fact l.Prime] (j : PadicPlace l) (hl : l.Coprime ϑ.normQ) :
    (p.denomBound : ℂ) • trivialLift H ϑ ∈ LevelForm.integralForms j := by
  -- The value at `h` is a sum of kernel values, each integral after scaling by `p.denomBound`,
  -- and the gauge is ultrametric.
  intro h
  change weylGauge (lValueData H ϑ).descentPair.columnCount (lValueData H ϑ).descentPair.detExp h
    ((p.denomBound : ℂ) • trivialLift H ϑ h) ≤ 1
  rw [trivialLift_apply, Finset.smul_sum,
    show (lValueData H ϑ).descentPair.detExp = 0 from funext fun τ ↦ by simp]
  exact weylGauge_sum_le h zero_le_one fun c _ ↦
    weylGauge_denomBound_smul_pointKernel_le_one H ϑ _ h hl

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
and let `ϑ` be a tame character whose modulus has norm `N = ϑ.normQ`. The number
`integralAlgebraicPart H ϑ = D.chosenGroupOrder * p.denomBound ^ 2 * ‖φ‖ ^ 2 / N ^ (2 z - 1)`, where
`φ = trivialLift H ϑ` is the normalised theta lift of `ν ϑ` to `U(n)`, is integral at every prime
that does not divide `N`. -/
lemma integralAlgebraicPart_mem_integralAway (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    integralAlgebraicPart H ϑ ∈ Seesaw.integralAway ϑ.normQ := by
  -- The form `φ` is integral at `j` and at `j ∘ conj`, so its squared norm is integral up to the
  -- orders of the stabilisers; the norm of the modulus is a unit.
  intro l _ hl j
  let φ : (lValueData H ϑ).descentPair.FormV := (p.denomBound : ℂ) • trivialLift H ϑ
  have h_inner : ‖j (D.chosenGroupOrder • inner ℂ φ φ)‖ ≤ 1 :=
    LevelForm.norm_nsmul_inner_le_one φ φ ⟨j⟩
      (D.card_classAut_dvd_chosenGroupOrder (H.1.trans_le D.nat_le_of_hasLogBound)
        levelOf_le_stdLevel)
      (denomBound_smul_trivialLift_mem_integralForms H ϑ _ hl)
      (denomBound_smul_trivialLift_mem_integralForms H ϑ _ hl)
  have h_value : integralAlgebraicPart H ϑ =
      D.chosenGroupOrder • inner ℂ φ φ / (ϑ.normQ : ℂ) ^ (card n - 1) := by
    simp [φ, integralAlgebraicPart, algPart, inner_self_eq_norm_sq_to_K, norm_smul, mul_pow,
      mul_assoc, mul_div_assoc]
  rwa [h_value, map_div₀, map_pow, map_natCast, norm_div, norm_pow, hl.norm_natCast_eq_one, one_pow,
    div_one]

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
and let `φ = trivialLift H TameChar.one` be the normalised theta lift of `ν` to `U(n)`, with no
twist. The number `integralAlgebraicPart H TameChar.one`, the squared norm `‖φ‖ ^ 2` times the
natural number `D.chosenGroupOrder * p.denomBound ^ 2`, is integral at every prime `l`: its image
under every field isomorphism `ι : ℂ ≃+* PadicAlgCl l` has norm at most one. -/
lemma norm_integralAlgebraicPart_one_le_one (H : p.HasLiftRank n) {l : ℕ} [Fact l.Prime]
    (ι : ℂ ≃+* PadicAlgCl l) :
    ‖ι (integralAlgebraicPart H TameChar.one)‖ ≤ 1 := by
  -- The modulus of the trivial character is empty, so every prime `l` is allowed.
  have h_coprime : l.Coprime (TameChar.one : D.TameChar).normQ := by
    simp [TameChar.normQ, toAutChar_one_and_toTwist_one_and_Q_one]
  calc ‖ι (integralAlgebraicPart H TameChar.one)‖
      = ‖complexToCp ι (integralAlgebraicPart H TameChar.one)‖ :=
        (PadicComplex.norm_extends l _).symm
    _ ≤ 1 := integralAlgebraicPart_mem_integralAway H TameChar.one l h_coprime (complexToCp ι)

/-! ### One group ring element for all twists -/

/-- The index set of the sum in `trivialLift_apply`: pairs of a class of `U(1)` at the principal
level at the chosen places and a family of units of the residue fields at the modulus of `ϑ`. -/
abbrev TrivialLiftIndex : Type :=
  StdClasses (n := Unit) D.chosenLevel × TwistGL (D.levelPlaces ϑ) Unit

/-- The finite point of `U(1)` attached to an index: the representative of the class times
`twistResidueLift` of the family of units, a lift of the inverse family. -/
abbrev liftPoint (a : TrivialLiftIndex ϑ) : Gf D.E Unit :=
  a.1.out * (D.levelPlaces ϑ).twistResidueLift a.2

/-- Let `p = (ν, z)` be a pair with `z ≥ 2`, let `n` have `2 z` elements, and let `ϑ`, `ϑ'` be tame
characters with the same modulus. The value of the lift of `ν ϑ'` at a finite point `h` of `U(n)` is
the sum over `a` of `ϑ'(det (1, g))⁻¹` times the value at `(g, h)` of the theta kernel of `p`
twisted by `ϑ.pow 0`, the trivial character regarded as tame of modulus `ϑ.Q`. Here `a` is a class
of `U(1)` at the principal level at the chosen places with a family of units of the residue fields
at the modulus, `g = liftPoint ϑ a` is the finite point of `U(1)` attached to `a`, and `(1, g)` is
the adelic point with component `1` at the infinite places and finite part `g`. -/
lemma trivialLift_apply_eq_sum_smul (H : p.HasLiftRank n) (ϑ : D.TameChar) {ϑ' : D.TameChar}
    (hQ : ϑ'.Q = ϑ.Q) (h : Gf D.E n) :
    trivialLift H ϑ' h = ∑ a : TrivialLiftIndex ϑ,
      (ϑ'.toAutChar.1 (G.det (s := 1) (1, liftPoint ϑ a)) : ℂ)⁻¹ •
        pointKernel H (ϑ.pow 0) (liftPoint ϑ a) h := by
  obtain ⟨χ, Q, ψ, hasWeight, ψ_eq_one, star_notMem, coprime⟩ := ϑ'
  obtain rfl : Q = ϑ.Q := hQ
  -- the character is a scalar factor of the Weil action (`pairWeil_apply`); the point datum and
  -- the points `liftPoint` depend on the modulus only
  simp [trivialLift_apply, TameChar.pow, kernelValue, pairWeil_apply, rankTwist, smul_smul,
    smul_mulVec]
  -- the scalar factors of the two sides agree up to their order
  ac_rfl

/-- The class sum over `U(2 z)`, at the level of the lift, of the Gram pairing of the values at
`liftPoint ϑ b` and `liftPoint ϑ a` of the kernel of the trivial character of modulus `ϑ.Q`. A
single term of the lift need not have this level; the sum is taken at fixed representatives of the
classes. -/
def kernelPairing (a b : TrivialLiftIndex ϑ) : ℂ :=
  classSum stdRatPoints (lValueData H ϑ).descentPair.levelGroup fun k : Gf D.E n ↦
    gramForm (pointKernel H (ϑ.pow 0) (liftPoint ϑ b) k) (pointKernel H (ϑ.pow 0) (liftPoint ϑ a) k)

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
and let `ϑ`, `ϑ'` be tame characters with the same modulus. The squared norm of the theta lift
`trivialLift H ϑ'` of `ν ϑ'` to `U(n)` (the class sum, at the level of the lift, of the Gram
pairings of its values with themselves) is the sum of the numbers
`ϑ'(det (g b / g a)) * kernelPairing H ϑ a b`, where `g a` is the adelic point of `U(1)` with
component `1` at the infinite places and finite part `liftPoint ϑ a`. Here `a`, `b` run over
`TrivialLiftIndex ϑ`, and `kernelPairing H ϑ a b` is the same class sum for the kernels of `p`
twisted by the trivial character of that modulus, taken at `g b` and `g a`. -/
lemma norm_sq_trivialLift_eq_sum (H : p.HasLiftRank n) (ϑ : D.TameChar) {ϑ' : D.TameChar}
    (hQ : ϑ'.Q = ϑ.Q) :
    (‖trivialLift H ϑ'‖ : ℂ) ^ 2 =
      ∑ a : TrivialLiftIndex ϑ, ∑ b : TrivialLiftIndex ϑ,
        ϑ'.toAutChar.1 (G.det (s := 1) ((1, liftPoint ϑ b) / (1, liftPoint ϑ a))) *
          kernelPairing H ϑ a b := by
  -- the level depends on the modulus only
  have levelGroup_eq : (lValueData H ϑ').descentPair.levelGroup =
      (lValueData H ϑ).descentPair.levelGroup := by
    obtain ⟨⟩ := ϑ'
    cases hQ
    rfl
  let c (a : TrivialLiftIndex ϑ) : Circle := ϑ'.toAutChar.1 (G.det (s := 1) (1, liftPoint ϑ a))
  calc (‖trivialLift H ϑ'‖ : ℂ) ^ 2
      = classSum stdRatPoints (lValueData H ϑ).descentPair.levelGroup fun k : Gf D.E n ↦
          gramForm (trivialLift H ϑ' k) (trivialLift H ϑ' k) := by
        simp [← coe_algebraMap, ← inner_self_eq_norm_sq_to_K, inner, levelGroup_eq,
          LevelForm.innerAt_eq_stdClassSum]
    -- expand both arguments of the sesquilinear form; `conj (c b)⁻¹ = c b`
    _ = ∑ a : TrivialLiftIndex ϑ, ∑ b : TrivialLiftIndex ϑ,
          (c a : ℂ)⁻¹ * (c b * kernelPairing H ϑ a b) := by
        simp [c, trivialLift_apply_eq_sum_smul H ϑ hQ, mul_sum, classSum_sum, ← coe_inv_eq_conj,
          ← mul_classSum, kernelPairing]
    _ = _ := by simp_rw [c, map_div, Circle.coe_div, div_eq_inv_mul, mul_assoc]

/-- The number `kernelPairing H ϑ a b` is the class sum over the unitary group `U(n)` of the pairing
of the kernel values at `liftPoint ϑ b` and `liftPoint ϑ a`. Times
`D.chosenGroupOrder * p.denomBound ^ 2` it is integral at every prime `l` that does not divide the
norm of the modulus: its image under an embedding `j` of `ℂ` into `ℂ_[l]` has norm at most `1`. -/
lemma mul_kernelPairing_mem_embValRing (H : p.HasLiftRank n) (ϑ : D.TameChar)
    (a b : TrivialLiftIndex ϑ) {l : ℕ} [Fact l.Prime] (hl : l.Coprime ϑ.normQ) (j : PadicPlace l) :
    (D.chosenGroupOrder * p.denomBound ^ 2 : ℕ) * kernelPairing H ϑ a b ∈ embValRing (ι := j) := by
  have scaled_eq : (D.chosenGroupOrder * p.denomBound ^ 2 : ℕ) * kernelPairing H ϑ a b =
      D.chosenGroupOrder • classSum stdRatPoints (lValueData H ϑ).descentPair.levelGroup
        fun k : Gf D.E n ↦
          gramForm ((p.denomBound : ℂ) • pointKernel H (ϑ.pow 0) (liftPoint ϑ b) k)
            ((p.denomBound : ℂ) • pointKernel H (ϑ.pow 0) (liftPoint ϑ a) k) := by
    simp [kernelPairing, ← mul_classSum, sq, mul_assoc]
  rw [scaled_eq]
  -- the orders of the automorphism groups divide `D.chosenGroupOrder`
  refine smul_classSum_mem _ (D.card_classAut_dvd_chosenGroupOrder
    (H.1.trans_le D.nat_le_of_hasLogBound) levelOf_le_stdLevel) fun k ↦ ?_
  -- both kernel values, scaled by `p.denomBound`, have gauge at most one
  apply gramForm_mem_embValRing <;> exact weylGauge_denomBound_smul_pointKernel_le_one H (ϑ.pow 0) _
    k hl

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2`, let `n` have `2 z` elements (hypothesis `H`),
and let `ϑ` be a tame character of modulus `Q`. For a tame character `ϑ'`, the number
`integralAlgebraicPart H ϑ'` is
`D.chosenGroupOrder * p.denomBound ^ 2 * ‖trivialLift H ϑ'‖ ^ 2 / ϑ'.normQ ^ (2 z - 1)`: the squared
norm of the theta lift of `ν ϑ'` to `U(n)`, divided by a power of the norm of the modulus and
multiplied by a natural number that does not depend on `ϑ'`. This function of `ϑ'` is an integral
measure at `Q`: there are finitely many points `u a` of `U(1)(𝔸)` and numbers `c a`, integral at the
primes that do not divide the norm of `Q`, such that its value at every `ϑ'` of modulus `Q` is
`∑ a, c a * ϑ' (u a)`. -/
lemma isIntegralMeasure_integralAlgebraicPart (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    ϑ.IsIntegralMeasure (integralAlgebraicPart H) := by
  -- By `norm_sq_trivialLift_eq_sum` the squared norm is a sum over pairs of indices; the points are
  -- the determinants of the quotients, the coefficients the scaled pairings.
  let u (x : TrivialLiftIndex ϑ × TrivialLiftIndex ϑ) : unitary (𝔸 D.E) :=
    G.det (s := 1) ((1, liftPoint ϑ x.2) / (1, liftPoint ϑ x.1))
  let c (x : TrivialLiftIndex ϑ × TrivialLiftIndex ϑ) : ℂ :=
    (D.chosenGroupOrder * p.denomBound ^ 2 : ℕ) * kernelPairing H ϑ x.1 x.2 *
      (ϑ.normQ ^ (card n - 1) : ℂ)⁻¹
  refine ⟨TrivialLiftIndex ϑ × TrivialLiftIndex ϑ, inferInstance, u, c, ?_, ?_⟩
  · rintro ⟨a, b⟩ l _ hl j
    -- the norm of the modulus is an `l`-adic unit
    have norm_inv_mem : (ϑ.normQ ^ (card n - 1) : ℂ)⁻¹ ∈ embValRing (ι := ⟨j⟩) :=
      show ‖j _‖ ≤ 1 by rw [map_inv₀, map_pow, map_natCast, norm_inv, norm_pow,
        hl.norm_natCast_eq_one, one_pow, inv_one]
    exact mul_mem (mul_kernelPairing_mem_embValRing H ϑ a b hl ⟨j⟩) norm_inv_mem
  · intro ϑ' hQ
    rw [integralAlgebraicPart, algPart, norm_sq_trivialLift_eq_sum H ϑ hQ,
      show ϑ'.normQ = ϑ.normQ by rw [TameChar.normQ, hQ], ← sum_prod_type', sum_div,
      mul_sum]
    exact sum_congr rfl fun x _ ↦ by ring

end CriticalPair

end New.Data

end
