import Lib.GaloisRep.BaseChange.ShintaniLift
import Lib.GaloisRep.LocalGlobal.IwahoriCompatibility

/-!
# Tame exponents of inertia and local-global compatibility for labelled forms

Let `w` be a finite place of `E` whose residue field `k_w` has order `q`, let `A` be a valuation
subring of an algebraic closure `Ω` lying over `w`, and let `T` be an injective complex-valued
multiplicative character of an algebraically closed extension `K` of `k_w`.

## Main definitions and results

* `New.GaloisRep.IsTameExponent w A T f s a`: the inertial element `s` moves a `(q ^ f - 1)`-th root
  of a uniformiser by the root of unity that `T` reads as `exp (2πi a / (q ^ f - 1))`.
* `New.GaloisRep.IsLabelledAt`: for a polynomial `c` over the residue field, the polynomial with
  roots `ιℓ ((T ^ a) x)` satisfies a given condition at each such `s`. Here `x` runs over the roots
  of `c`, `ιℓ` is the fixed map from `ℂ` to `PadicAlgCl ℓ`, and `T ^ a` is the `a`-th power of the
  character `T`.
* `New.GaloisRep.IsTameExponent.pow_apply_charName`: comparison with the local Artin map, for
  characters of `k_wˣ`.
* `New.GaloisRep.exists_isTameExponent`: exponents exist when `f` is a factorial.
* `New.GaloisRep.Attached.isLabelledAt`: if an eigenform has, at a split place `w`, a type for
  `GL n` of the residue field given by a label (`New.HasProductLabel`: a polynomial `c` of degree
  `d` and characters `χ l` with multiplicities `t l`, where `d + ∑ l, t l` is the rank and the roots
  of `c` and the names of the `χ l` are all distinct), then inertia at `w` acts on the attached
  Galois representation through the tame characters given by the roots of the polynomial of the
  label (`New.GaloisRep.IsLabelledAt`, `New.GaloisRep.IsTameExponent`). The proof uses base changes
  of prime degree in which `w` is inert to reduce to the case where `c` splits into linear factors.
  That case follows from `New.GaloisRep.Attached.local_global_of_eigencharacter` applied to local
  units.

Notions from other files:
* `New.IsPlaceOver A w`: the valuation subring `A` of `Ω` lies over `w`, that is, an integer of `E`
  is in the maximal ideal of `A` exactly when it lies in `w`.
* `New.Cohomology.centrePrime Ω A`: the integers of `Ω` that lie in the maximal ideal of `A`.
* `New.charName T χ`: the unit of `k_w` that names the character `χ` of `k_wˣ`; the map `χ ↦ x_χ` is
  an isomorphism from the character group of `k_wˣ` to `k_wˣ` that depends on `T`.
* `New.GaloisRep.PolyKillsAt r A s Q`: the polynomial `Q` kills `r s` if `ℓ` is a unit at `A`, and
  kills the action of `s` on the periods of `r` if `A` lies above `ℓ`.

## Relation to the literature

Known result: Local-global compatibility at tame level, away from ℓ and at ℓ. Here it is proved only
at split places, for depth-zero types induced from a squarefree type and characters of the
determinant. It is stated as polynomials that kill inertia elements, without the local Langlands
correspondence, and it is reduced by cyclic base change to the case of sorted tame Iwahori
eigencharacters. Source: Harris, Taylor, The geometry and cohomology of some simple Shimura
varieties (2001); Taylor, Yoshida, J. Amer. Math. Soc. 20 (2007); Barnet-Lamb, Gee, Geraghty,
Taylor, Local-global compatibility for l = p, II (2014), Thm 1.1.

See also `Lib.ClassField.Local.ArtinMap`.
-/

/-! ## Tame exponents of inertial elements and inertia acting through labels -/

namespace New.GaloisRep

open NumberField Polynomial Cohomology Ideal Quotient IsAlgClosed IsLocalRing
  RingHom algebraMap

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [EmbeddedNumberField E]
  (w : FinPlace E) (A : ClosurePlace)
  {K : Type} [Field K] [Algebra (ResField w) K]
  (T : MulChar K ℂ) [IsFaithfulMulChar K T] (f : ℕ) (s : Gal(Ω/E)) (a : ℕ)

/-- A ring homomorphism `g` from `𝓞 E` to a field that kills the prime `w` factors through the
residue field of `w`. -/
lemma exists_resField_hom {R : Type*} [Field R] (g : 𝓞 E →+* R) (h_le_ker : w.asIdeal ≤ ker g) :
    ∃ j : ResField w →+* R, ∀ x : 𝓞 E, j (algebraMap (𝓞 E) (ResField w) x) = g x :=
  ⟨liftOfSurjective _ (algebraMap_ResField_surjective w)
    ⟨g, fun _ hx ↦ h_le_ker (algebraMap_ResField_eq_zero.1 hx)⟩, liftOfSurjective_comp_apply _ _ _⟩

/-- The automorphism `s` has tame exponent `a` at level `f`. With `q = w.q` the order of the residue
field `k_w` and `Q = q ^ f`: (a) `A` lies over `w`; (b) `f ≠ 0`; (c) `s` lies in the inertia group
of `A`; and there are (d) a ring homomorphism `φ : 𝓞 Ω →+* K` that kills the centre of `A` and
extends the map `𝓞 E → k_w → K`, (e) a uniformiser `π ∈ E` and `z ∈ Ω` with `z ^ (Q - 1) = π`, and
(f) an integer `t` of `Ω` equal to `s z / z` with `T (φ t) = exp (2πi / (Q - 1)) ^ a`. -/
def IsTameExponent : Prop :=
  IsPlaceOver A w ∧ f ≠ 0 ∧
  s ∈ inertiaGroup Gal(Ω/E) A ∧
  ∃ (φ : 𝓞 Ω →+* K) (π : E) (z : Ω) (t : 𝓞 Ω),
    centrePrime Ω A ≤ ker φ ∧
    (∀ x : 𝓞 E,
      φ (algebraMap (𝓞 E) (𝓞 Ω) x) = algebraMap (ResField w) K (algebraMap (𝓞 E) (ResField w) x)) ∧
    IsUniformiser A π ∧
    z ^ (w.q ^ f - 1) = algebraMap E Ω π ∧
    (t : Ω) = s z / z ∧
    T (φ t) = Complex.exp (2 * Real.pi * Complex.I / (w.q ^ f - 1 : ℕ)) ^ a

variable {w A f s a}

open Nat

-- Without this, `IsDomain K` is found through the faithful character of the section variables.
attribute [-instance] New.Variety.IsAbsIntegrallyClosedLocal.toIsDomain in
/-- Inertia acts through the tame characters of level `f` given by the roots of `c`. This is in the
sense of the relation `P` between automorphisms and polynomials (such as "the polynomial kills the
image of `s`"). Whenever `s` has tame exponent `a` (`New.GaloisRep.IsTameExponent`), `P` holds for
`s` and `∏ x, (X - ιℓ ((T ^ a) x))`. The product is over the roots `x` of `c` in `K`, with
multiplicity. Here `T ^ a` is the `a`-th power of the character `T`. -/
def IsLabelledAt {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] (A : ClosurePlace) (T : MulChar K ℂ) (f : ℕ)
    (P : Gal(Ω/E) → (PadicAlgCl ℓ)[X] → Prop) (c : (ResField w)[X]) :
    Prop :=
  ∀ ⦃s : Gal(Ω/E)⦄ ⦃a : ℕ⦄,
    IsTameExponent w A T f s a → P s ((c.aroots K).map fun x : K ↦ X - C (ιℓ ((T ^ a) x))).prod

omit [IsFaithfulMulChar K T] in
lemma IsTameExponent.mem_inertiaGroup (h_exp : IsTameExponent w A T f s a) :
    s ∈ inertiaGroup Gal(Ω/E) A :=
  let ⟨_, _, hs, _⟩ := h_exp; hs

/-- Let `s` have tame exponent `a` at `A` over `w` (`New.GaloisRep.IsTameExponent`), let `K` be
algebraically closed and `T` injective, and let `u` be a local unit whose local Artin symbol is the
class of `s`. Then for every character `χ` of `k_wˣ`, the value of `T ^ a` at the image in `K` of
the unit `charName T χ` of `k_w` that names `χ` is the value of `χ` at the residue of `u`. -/
lemma IsTameExponent.pow_apply_charName {hs_dec : s ∈ decompGroup Gal(Ω/E) A}
    (h_exp : IsTameExponent w A T f s a)
    {u : (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)ˣ}
    (hu : Valued.v u.val = 1) (h_artin : localArtin Gal(Ω/E) A w u = ⟦⟨s, hs_dec⟩⟧)
    (χ : MulChar (ResField w) ℂ) :
    (T ^ a) ((charName T χ).val : ResField w) = χ (residue (LocInt w) ⟨u, hu.le⟩) := by
  -- Write `q ^ f - 1 = (q - 1) * k`, `ρ` for the reduction map and `θ` for `thetaChar T q x_χ`.
  -- Then `θ` is `χ` on the residue field and `θ (ρ t ^ k) = (T ^ a) x_χ`, so it is enough that
  -- `ρ t ^ k` is the residue of `u`. This is the tame symbol congruence: if `y ^ (q - 1)` is a
  -- uniformiser, then `u ≡ x` at `w` if and only if `s y / y ≡ x` at `A`.
  obtain ⟨hA, hf, -, ρ, π, z, t, hρ_cen, hρ_int, hπ, hz, ht, hT⟩ := h_exp
  obtain ⟨k, hk⟩ : w.q - 1 ∣ w.q ^ f - 1 := w.q.sub_one_dvd_pow_sub_one f
  obtain ⟨x, hx⟩ := algebraMap_ResField_surjective w (residue (LocInt w) ⟨u, hu.le⟩)
  -- as `z ^ k` is a `(q - 1)`-th root of the uniformiser and `u ≡ x` at `w`,
  -- `t ^ k = s (z ^ k) / z ^ k` is congruent to `x` at `A`
  have hzk : (z ^ k) ^ (w.q - 1) = algebraMap E Ω π := by rw [← pow_mul', ← hk, hz]
  have h_cong : t ^ k - algebraMap (𝓞 E) (𝓞 Ω) x ∈ centrePrime Ω A := by
    have h_symbol : A.valuation (s (z ^ k) / z ^ k - algebraMap E Ω x) < 1 :=
      (hA.valuation_sub_lt_one_iff_of_localArtin_eq hπ hu h_artin hzk).1
        (residue_eq_iff_valuation_sub_lt_one.1 hx.symm)
    rw [map_pow, ← div_pow, ← ht] at h_symbol
    exact mem_centrePrime.2 h_symbol
  have h_res : ρ t ^ k = algebraMap (ResField w) K (residue (LocInt w) ⟨u, hu.le⟩) := by
    simpa [← hx, hρ_int, sub_eq_zero] using hρ_cen h_cong
  calc
    _ = thetaChar T (Nat.card (ResField w)) (algebraMap _ K (charName T χ).val) (ρ t ^ k) :=
      (thetaChar_apply_pow T Finite.one_lt_card (algebraMap_pow_card_pred_eq_one _)
        (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hf w.one_lt_q)) (by rwa [card_ResField]) hT).symm
    _ = χ (residue (LocInt w) ⟨u, hu.le⟩) := by rw [h_res, thetaChar_charName]

/-- Let `c` be a label of degree `r` over the residue field `k_w` of order `q` (monic, squarefree,
`c(0) ≠ 0`) and `x` a root of `c` in `K`. Then `x ^ (q ^ r! - 1) = 1`, and `x ^ (q ^ d - 1) = 1` for
some `d` with `1 ≤ d ≤ r`. -/
lemma _root_.New.IsLabel.root_pow_eq_one {c : (ResField w)[X]} {r : ℕ} (h_label : IsLabel r c)
    {x : K} (hx : aeval x c = 0) :
    x ^ (w.q ^ (r)! - 1) = 1 ∧ ∃ d ∈ Set.Icc (1 : ℕ) r, x ^ (w.q ^ d - 1) = 1 := by
  -- Take for `d` the degree of the minimal polynomial `P` of `x`: the nonzero element `x` lies in
  -- the field with `q ^ n` elements when `d ∣ n`, and `d ∣ r !` as `1 ≤ d ≤ r`.
  obtain ⟨hmonic, -, hdeg, hc0⟩ := h_label
  set P : (ResField w)[X] := minpoly (ResField w) x
  have hP : Irreducible P := minpoly.irreducible ⟨c, hmonic, hx⟩
  have hx0 : x ≠ 0 := fun h0 ↦ hc0 (by simpa [h0, aeval_def, eval₂_at_zero] using hx)
  have hd_pos : 0 < P.natDegree := hP.natDegree_pos
  have hd_le : P.natDegree ≤ r :=
    (natDegree_le_natDegree (minpoly.min _ _ hmonic hx)).trans_eq hdeg
  have h_pow {n : ℕ} (hn : n ≠ 0) (hd : P.natDegree ∣ n) : x ^ (w.q ^ n - 1) = 1 := by
    rw [pow_pred_eq_one_iff (one_lt_pow₀ w.one_lt_q hn), ← card_ResField,
      root_pow_card_pow_eq_self_iff hP (minpoly.aeval _ x)]
    exact ⟨hx0, hd⟩
  exact ⟨h_pow r.factorial_ne_zero (dvd_factorial hd_pos hd_le),
    P.natDegree, ⟨hd_pos, hd_le⟩, h_pow hd_pos.ne' dvd_rfl⟩

/-- If `A` lies over `w` and `K` is algebraically closed, the embedding of the residue field of `w`
in `K` extends to a homomorphism `𝓞 Ω →+* K` that kills the centre of `A`. -/
lemma exists_ringHom_centrePrime_le_ker [IsAlgClosed K] (hA : IsPlaceOver A w) :
    ∃ ρ : 𝓞 Ω →+* K, centrePrime Ω A ≤ ker ρ ∧ ∀ x : 𝓞 E,
      ρ (algebraMap (𝓞 E) (𝓞 Ω) x) =
        algebraMap (ResField w) K (algebraMap (𝓞 E) (ResField w) x) := by
  have : (centrePrime Ω A).LiesOver w.asIdeal := hA.centrePrime_liesOver
  let : Field (𝓞 E ⧸ w.asIdeal) := Quotient.field w.asIdeal
  let : Algebra (𝓞 E ⧸ w.asIdeal) K :=
    Algebra.compHom K (Ideal.Quotient.lift w.asIdeal (algebraMap (𝓞 E) (ResField w)) (by simp))
  let j : (𝓞 Ω ⧸ centrePrime Ω A) →ₐ[𝓞 E ⧸ w.asIdeal] K := IsAlgClosed.lift
  exact ⟨j.toRingHom.comp (Ideal.Quotient.mk _), fun t ht ↦ by simp [eq_zero_iff_mem.2 ht],
    fun x ↦ j.commutes (Ideal.Quotient.mk w.asIdeal x)⟩

/-- Let `A` lie over `w`, let `K` be algebraically closed and `T` injective (both are asked by
`IsFaithfulMulChar K T`), and take the level `f !`. Then (a) some element of the inertia group has
tame exponent `1`; (b) every element `s` of the inertia group has a tame exponent `a`, and if `s` is
the chosen generator `hA.tameGenerator` of tame inertia, this `a` is prime to `q ^ f ! - 1`, where
`q = w.q` is the order of the residue field. -/
lemma exists_isTameExponent (hA : IsPlaceOver A w) (f : ℕ) :
    -- (a)
    (∃ s : inertiaGroup Gal(Ω/E) A, IsTameExponent w A T (f)! s.val 1) ∧
    -- (b)
    ∀ s ∈ inertiaGroup Gal(Ω/E) A, ∃ a : ℕ,
      IsTameExponent w A T (f)! s a ∧ (s = hA.tameGenerator → a.Coprime (w.q ^ (f)! - 1)) := by
  -- With `N = q ^ f! - 1` and `z ^ N` a uniformiser, the tame generator `γ` gives a primitive
  -- `N`-th root of unity `ζ = γ z / z`. For some `j` prime to `N`, `T` sends the residue of `ζ ^ j`
  -- to `exp (2πi / N)`; the exponent of `s` is the `a` with `s z / z = (ζ ^ j) ^ a`.
  let N : ℕ := w.q ^ f.factorial - 1
  have hN_res : NeZero (N : ResField w) :=
    ⟨by simp [N, ← card_ResField, f.factorial_ne_zero, NeZero.pos]⟩
  have : NeZero (N : K) := .of_faithfulSMul (ResField w) K N
  have hN : NeZero N := hN_res.of_neZero_natCast
  have hN_val : A.valuation N = 1 := hA.valuation_natCast_eq_one_iff.2 fun hmem ↦
    hN_res.1 (mod_cast algebraMap_ResField_eq_zero.2 hmem)
  obtain ⟨ρ, hρ_cen, hρ_int⟩ := exists_ringHom_centrePrime_le_ker (K := K) hA
  obtain ⟨π, z, hπ, hz, hζ⟩ := hA.exists_isPrimitiveRoot_tameGenerator_smul_div hN_val
  -- `ρ ζ` is again primitive, being a root of the cyclotomic polynomial; `T` is injective
  have hρζ : IsPrimitiveRoot (ρ hζ.toInteger) N := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic N ρ]
    exact (isRoot_cyclotomic_iff.2 hζ.toInteger_isPrimitiveRoot).map
  obtain ⟨j, -, hj, hTj⟩ :
      ∃ j < N, j.Coprime N ∧ T (ρ hζ.toInteger) ^ j = Complex.exp (2 * Real.pi * Complex.I / N) :=
    (hρζ.map_of_injective IsFaithfulMulChar.injective).isPrimitiveRoot_iff.1
      (Complex.isPrimitiveRoot_exp N hN.1)
  have hζj : IsPrimitiveRoot ((hA.tameGenerator • z / z) ^ j) N := hζ.pow_of_coprime j hj
  have tame_of_eq (s : inertiaGroup Gal(Ω/E) A) (a : ℕ)
      (hsa : ((hA.tameGenerator • z / z) ^ j) ^ a = s.val z / z) :
      IsTameExponent w A T f.factorial s a :=
    ⟨hA, f.factorial_ne_zero, s.2, ρ, π, z, (hζ.toInteger ^ j) ^ a, hρ_cen, hρ_int, hπ, hz, hsa,
      by simp only [map_pow, hTj, N]⟩
  refine ⟨⟨hA.tameGenerator ^ j, tame_of_eq _ 1 <|
    (pow_one _).trans (inertia_pow_smul_div hA.tameGenerator.2 hN_val hz j).symm⟩, fun s hs ↦ ?_⟩
  -- `s z / z` is an `N`-th root of unity, so a power of `ζ ^ j`
  obtain ⟨a, -, ha⟩ := hζj.eq_pow_of_pow_eq_one (ξ := s z / z) (by simp [div_pow, ← map_pow, hz])
  refine ⟨a, tame_of_eq ⟨s, hs⟩ a ha, fun hs_gen ↦ (hζj.pow_iff_coprime hN.pos a).1 ?_⟩
  rwa [ha, hs_gen]

omit [IsFaithfulMulChar K T] in
/-- Tame exponents after an unramified base change. Let `u` be a place of `L / E` above `w` and
below `A`, unramified and with `q_u = q_w ^ p`. If `σ ∈ Gal(Ω/L)` has tame exponent `a` at level
`p * g` over `E`, then the residue fields form a tower `k_w → k_u → K`, whose first step has degree
`p` and is induced by `𝓞 E → 𝓞 L`, and `σ` has tame exponent `a` at level `g` over `L`. -/
lemma IsTameExponent.exists_tower_of_unramified {L : Type} [Field L] [EmbeddedNumberField L]
    [Algebra E L] [IsScalarTower E L Ω] {u : FinPlace L} {p g : ℕ} {σ : Gal(Ω/L)}
    (h_exp : IsTameExponent w A T (p * g) (σ.restrictScalars E) a) (h_below : u.below E = w)
    (hAu : IsPlaceOver A u) (h_ram : u.asIdeal.ramificationIdx (𝓞 E) = 1) (hq : w.q ^ p = u.q) :
    ∃ (_ : Algebra (ResField w) (ResField u)) (_ : Algebra (ResField u) K),
      IsScalarTower (ResField w) (ResField u) K ∧
      Module.finrank (ResField w) (ResField u) = p ∧
      (∀ x : 𝓞 E, algebraMap (ResField w) (ResField u) (algebraMap (𝓞 E) (ResField w) x) =
        algebraMap (𝓞 L) (ResField u) (algebraMap (𝓞 E) (𝓞 L) x)) ∧
      IsTameExponent u A T g σ a := by
  subst h_below
  obtain ⟨hA, h_level, hσ, ρ, π, z, t, hρ_cen, hρ_int, hπ, hz, ht, hT⟩ := h_exp
  rw [pow_mul, hq] at hz hT
  obtain ⟨j, hj⟩ := exists_resField_hom (u.below E)
    ((algebraMap (𝓞 L) (ResField u)).comp (algebraMap (𝓞 E) (𝓞 L)))
    fun x hx ↦ algebraMap_ResField_eq_zero.2 hx
  obtain ⟨i, hi⟩ := exists_resField_hom u (ρ.comp (algebraMap (𝓞 L) (𝓞 Ω))) <| by
    rw [hAu.centrePrime_liesOver.over]
    exact fun x hx ↦ hρ_cen hx
  algebraize [j, i]
  have h_tower (y : ResField (u.below E)) : algebraMap (ResField (u.below E)) K y = i (j y) := by
    obtain ⟨x, rfl⟩ := algebraMap_ResField_surjective _ y
    rw [hj, comp_apply, hi, comp_apply, ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L), hρ_int]
  have h_rank : Module.finrank (ResField (u.below E)) (ResField u) = p := by
    refine Nat.pow_right_injective (u.below E).one_lt_q (?_ : (u.below E).q ^ _ = (u.below E).q ^ p)
    rw [hq, ← card_ResField, ← card_ResField, ← Module.natCard_eq_pow_finrank]
  -- as `u` is unramified, `π` is still a uniformiser over `L`
  have hπ' : IsUniformiser A (algebraMap E L π) := by
    rw [hAu.isUniformiser_iff, ← (u.below E).valuation_liesOver L, hA.isUniformiser_iff.1 hπ,
      h_ram,
      pow_one]
  exact ⟨j.toAlgebra, i.toAlgebra, .of_algebraMap_eq h_tower, h_rank, hj, hAu,
    right_ne_zero_of_mul h_level, hσ, ρ, algebraMap E L π, z, t, hρ_cen, fun x ↦ (hi x).symm, hπ',
    hz.trans (IsScalarTower.algebraMap_apply E L Ω π), ht, hT⟩

end New.GaloisRep

/-! ## Local-global compatibility at a split place for a labelled form -/

section LabelCompatibility

open NumberField Polynomial Ideal Finset Function Module Fin New QZChar

attribute [local instance low] Fintype.ofFinite

/-- Local-global compatibility at level `1`. Let the Galois representation `r` be attached to the
Hecke polynomials `P` of the eigenform `f` of weight `κ`. At the split place `w`, `f` has the label
`labelChar T c * ∏ l, (χ l ∘ det on GL (t l))` (`New.HasProductLabel`: `c` of degree `d`,
`d + ∑ l, t l = card n`), where `T` embeds `Kˣ` in `ℂˣ` and `K` is algebraically closed. Let `A` lie
above `w`, and suppose the roots of `c` in `K` satisfy `x ^ (q - 1) = 1`, with `q = w.q`. Then
inertia at `A` is labelled (`New.GaloisRep.IsLabelledAt`) at level `1` by
`c * ∏ l, (X - charName T (χ l)) ^ t l`, in the following sense. For `σ` of tame exponent `a`, `r`
is of finite type at `A` (trivial on inertia near `1` if `ℓ` is a unit at `A`, and potentially
crystalline along embeddings inducing `A`) and has the Hodge–Tate jumps of `κ`. Also
`Q = ∏ x, (X - ιℓ ((T ^ a) x))` kills the action of `σ`, the product being over the roots `x` in `K`
of the label. -/
lemma New.GaloisRep.Attached.isLabelledAt_one {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type}
    [Nonempty n] [Field E] [CMType E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n]
    {κ : Weight E} {f : Gf E n → WeylIndex n κ.1 → ℂ} {P : FinPlace E → ℂ[X]} {r : GalRep ℓ E n}
    {w : FinPlace E} {A : ValuationSubring Ω} {hw : star w ≠ w} {K : Type} [Field K]
    [Algebra (ResField w) K] {T : MulChar K ℂ} [IsFaithfulMulChar K T] {s d : ℕ}
    {c : (ResField w)[X]} {χ : Fin s → MulChar (ResField w) ℂ} {t : Fin s → ℕ} [WeilData E]
    (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P) (hr : Attached P r)
    (hA : IsPlaceOver A w) (h_prod_label : HasProductLabel f hw T d c χ t)
    (h_roots : ∀ x : K, aeval x c = 0 → x ^ (w.q ^ 1 - 1) = 1) :
    IsLabelledAt A T 1
      (fun (σ : Gal(Ω/E)) (Q : (PadicAlgCl ℓ)[X]) ↦
        IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n)) ∧ PolyKillsAt r A σ Q)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) := by
  -- Here `c` splits, so the label is a product of characters of determinants, and the claims
  -- follow from `Attached.local_global_of_eigencharacter`.
  obtain ⟨h_label, h_sep, h_deg, h_fix, h_sum_ne⟩ := h_prod_label
  intro σ a h_tame
  -- the class of `σ` is the Artin symbol of a local unit `x`
  have hσ : σ ∈ inertiaGroup Gal(Ω/E) A := h_tame.mem_inertiaGroup T
  obtain ⟨x, hx, hxσ⟩ := hA.exists_localArtin_eq (inv_mem hσ) 0
  have hx_unit : Valued.v x.val = 1 := by simpa using hx
  have h_fixed (y : K) (hy : aeval y c = 0) : y ^ Nat.card (ResField w) = y := by
    rw [card_ResField]
    exact ((pow_pred_eq_one_iff w.one_lt_q).1 (by simpa using h_roots y hy)).2
  -- so `c` is `∏ i, (X - charName T (ψ i))` for some characters `ψ i`
  obtain ⟨ψ, rfl⟩ := h_label.exists_eq_prod_charName_of_root_pow_card_eq T h_fixed
  -- The names of the `ψ i` and the `χ l` are the roots of a separable polynomial, so are distinct.
  have h_inj : Injective (append ψ χ) := .of_comp (f := fun η ↦ (charName T η).val) <| by
    simpa [Function.comp_def, ← separable_prod_X_sub_C_iff, prod_univ_add] using h_sep

  -- The span of the translates of `f` contains an Iwahori eigenvector `z` with a sorted `ξ`,
  -- whose values on units are those of the `ψ i` (once each) and the `χ l` (`t l` times).
  obtain ⟨z, hz, ξ, lab, h_eig, h_sorted, h_card, h_val⟩ :
      ∃ z ∈ cyclicSpan (Patching.localFormRep (stdSpace E n) κ hw).ρ ⟨f, hf⟩,
        ∃ ξ : Fin (Fintype.card n) → (LocField w)ˣ →* ℂˣ,
        ∃ lab : Fin (Fintype.card n) → Fin (d + s),
          IsIwahoriEigen (Patching.localFormRep (stdSpace E n) κ hw) (torusChar ξ) z ∧
          (Antitone fun i ↦ ‖(ξ i (uniformizer w) : ℂ)‖) ∧
          (∀ b, Fintype.card {i // lab i = b} = append 1 t b) ∧
          ∀ (y : (LocField w)ˣ) (hy : Valued.v y.val = 1) (i : Fin (Fintype.card n)),
            (ξ i y : ℂ) = append ψ χ (lab i) (IsLocalRing.residue (LocInt w) ⟨y, hy.le⟩) :=
    -- `h_fix` and `h_sum_ne` are read in `localFormRep`, which acts by right translation at `w`
    exists_sorted_of_detChar (v_uniformizer w) isUnitary_localFormRep (Fintype.equivFin n) h_inj
      (m := append 1 t) (by simpa [sum_univ_add] using h_deg)
      (by simpa [Subtype.ext_iff] using! h_fix) (surjInv_eq _)
      (by simpa [labelChar_X_sub_C, ↓finsum_eq_sum_of_fintype, prod_univ_add, Subtype.ext_iff]
        using! h_sum_ne)
  -- `T ^ a` sends the name of a character `η` to `η` of the residue of `x`, so the polynomial of
  -- the claim has the roots `ιℓ (ψ i x)`, and `ιℓ (χ l x)` with multiplicity `t l`.
  have h_poly :
      ((((∏ i : Fin d, (X - C (charName T (ψ i)).val)) *
          ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l).aroots K).map
        fun y : K ↦ X - C (ιℓ ((T ^ a) y))).prod =
      (∏ b, (X - C (append ψ χ b (IsLocalRing.residue (LocInt w) ⟨x, hx_unit.le⟩))) ^
        append 1 t b).map ιℓ.toRingHom := by
    simp [aroots, h_tame.pow_apply_charName T hx_unit hxσ, Multiset.map_bind, Multiset.map_nsmul,
      Polynomial.map_prod, prod_eq_zero_iff, sub_eq_zero, X_ne_C, roots_mul, roots_prod, prod_ofFn,
      prod_univ_add, Multiset.prod_nsmul]
  rw [h_poly, ← prod_X_sub_C_eq_prod_pow_of_card_fiber h_card (h_val x hx_unit)]
  simpa [Polynomial.map_prod] using hr.local_global_of_eigencharacter h_eig
    (he.of_mem_cyclicSpan hz h_eig.1) h_sorted hA ⟨σ, hσ.1⟩ x 0 (inv_mem hσ) hxσ hx

/-- Let `w` be a split place of the CM field `E` with Weil data, let `A` lie above `w`, and let `p`
be prime. There are a character `η` of `E_wˣ`, a continuous character `μ : Gal(Ω/E) → ℚ/ℤ` and a
place `u` of `stepField μ` (the field cut out by the symmetrised character `symmetrise μ`) such that
(a) these form a step of degree `p` with local character `η` (`New.GaloisRep.IsStepOfLocalChar`; in
particular `symmetrise μ` sends the local Artin symbol at `A` of each `x` to `η x`, and `u` is the
only place above `w`), and (b) `w` is inert in the step: `symmetrise μ` kills the inertia group of
`A`, the place `u` is unramified, and `q_u = q_w ^ p`. -/
lemma New.GaloisRep.exists_isStepOfLocalChar_inert {E : Type} [Field E] [EmbeddedNumberField E]
    [CMType E] [WeilData E] {w : FinPlace E} {A : ClosurePlace} {p : ℕ} (hw : w.IsSplit)
    (hA : IsPlaceOver A w) (hp : p.Prime) :
    ∃ (η : (LocField w)ˣ →* Multiplicative QZ) (μ : QZChar Gal(Ω/E)) (u : FinPlace (stepField μ)),
      IsStepOfLocalChar A η p μ u ∧
      inertiaGroup Gal(Ω/E) A ≤ ker (symmetrise μ) ∧
      u.asIdeal.ramificationIdx (𝓞 E) = 1 ∧
      w.q ^ p = u.q := by
  -- Apply Grunwald's theorem to the unramified character `-ord mod p` of order `p`.
  have : Fact p.Prime := ⟨hp⟩
  let η : (LocField w)ˣ →* Multiplicative QZ :=
    .mk' (fun x ↦ .ofAdd (.ofZMod p (Valued.v x.val).log)) (by simp)
  have hη_ne : η ≠ 1 := DFunLike.ne_iff.2 ⟨uniformizer w, by simp [η, map_eq_zero_iff]⟩
  have hη_pow (x : (LocField w)ˣ) : η x ^ p = 1 := by
    simp [η, ← ofAdd_nsmul, ← map_nsmul, ZMod.natCast_self]
  have hη_unit (x : (LocField w)ˣ) (hx : Valued.v x.val = 1) : η x = 1 := by simp [η, hx]
  obtain ⟨μ, u, h_step⟩ := exists_isStepOfLocalChar hw hA hp η hη_ne hη_pow
    fun x hx ↦ by rw [map_pow, hη_unit x hx, one_pow]
  have h_unram : inertiaGroup Gal(Ω/E) A ≤ ker (symmetrise μ) :=
    (hA.artinAt_units_trivial_iff_inertiaGroup_le (symmetrise μ)).1
      fun x hx ↦ (h_step.abelianLift_symmetrise_artinAt x).trans (hη_unit x hx)
  obtain ⟨-, h_ram_of_le, -⟩ := hA.ramification_in_tower (ker (symmetrise μ)) h_step.isPlaceOver
  have h_ram : u.asIdeal.ramificationIdx (𝓞 E) = 1 := h_ram_of_le h_unram
  -- one place above `w` and `e = 1` give the residue degree `p`
  have h_below : u.below E = w := (h_step.below_eq_iff u).2 rfl
  have h_inertia : u.asIdeal.inertiaDeg (𝓞 E) = p := by
    simpa [h_below, h_step.below_eq_iff, h_ram, h_step.finrank_eq] using
      u.ncard_mul_ramificationIdx_mul_inertiaDeg (K := E)
  exact ⟨η, μ, u, h_step, h_unram, h_ram, by simp [← h_below, ← h_inertia, absNorm_pow_inertiaDeg]⟩

/-- Let `k' / k` be finite fields inside `K`. If `F : Hall k` lifts to `F' : Hall k'` (`New.Lift ℕ`:
for every `m`, one `ℕ`-combination of characters of `GL_m(k') ⋊ Gal(k'/k)` descends to both) and the
name of `χ' l` is the image of the name of `χ l`, then the lift extends to the products with the
`χ l ∘ det` and `χ' l ∘ det` in size `t l`. -/
lemma New.Lift.mul_prod_rankPart_detChar {k k' K : Type*} [Field k] [Field k'] [Algebra k k']
    [Finite k] [Finite k'] [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
    (T : MulChar K ℂ) [IsFaithfulMulChar K T] {F : Hall k} {F' : Hall k'} (h_lift : Lift ℕ F F')
    {s : ℕ} {χ : Fin s → MulChar k ℂ} {χ' : Fin s → MulChar k' ℂ} (t : Fin s → ℕ)
    (h_name : ∀ l : Fin s, (charName T (χ' l) : k') = algebraMap k k' (charName T (χ l))) :
    Lift ℕ (F * ∏ l : Fin s, (detChar (χ l)).rankPart (t l))
      (F' * ∏ l : Fin s, (detChar (χ' l)).rankPart (t l)) :=
  -- the pairs related by a lift contain `(1, 1)` and those of each factor, and are closed under
  -- products
  h_lift.mul (prod_hom_rel .one fun l _ _ h_rest ↦
    .mul (.rankPart_of_hasCommonLift (lift_detChar T (h_name l) (t l))) h_rest)

/-- Local-global compatibility at level `g`. Let `r` be attached to the Hecke polynomials of the
eigenform `f` of weight `κ`, which has the label `c`, `χ l`, `t l` at the split place `w`, and let
`A` lie above `w`. If the roots `x` of `c` in `K` satisfy `x ^ (q ^ g - 1) = 1`, where `q = w.q`,
then, as in `New.GaloisRep.Attached.isLabelledAt_one`, whenever `σ` has tame exponent `a` at level
`g`, `r` is of finite type at `A`, has the jumps of `κ`, and `∏ x, (X - ιℓ ((T ^ a) x))` kills the
action of `σ`, over the roots `x` of `c * ∏ l, (X - charName T (χ l)) ^ t l`. -/
lemma New.GaloisRep.Attached.isLabelledAt_of_root_pow_eq_one {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    {E n : Type} [Nonempty n] [Field E] [CMType E] [EmbeddedNumberField E] [Fintype n]
    [DecidableEq n] {κ : Weight E} {f : Gf E n → WeylIndex n κ.1 → ℂ} {P : FinPlace E → ℂ[X]}
    {r : GalRep ℓ E n} {w : FinPlace E} {A : ValuationSubring Ω} {hw : star w ≠ w} {K : Type}
    [Field K] [Algebra (ResField w) K] {T : MulChar K ℂ} [IsFaithfulMulChar K T] {s d g : ℕ}
    {c : (ResField w)[X]} {χ : Fin s → MulChar (ResField w) ℂ} {t : Fin s → ℕ} [WeilData E]
    (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P) (hr : Attached P r)
    (hA : IsPlaceOver A w) (h_prod_label : HasProductLabel f hw T d c χ t)
    (h_roots : ∀ x : K, aeval x c = 0 → x ^ (w.q ^ g - 1) = 1) :
    IsLabelledAt A T g
      (fun (σ : Gal(Ω/E)) (Q : (PadicAlgCl ℓ)[X]) ↦
        IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n)) ∧ PolyKillsAt r A σ Q)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) := by
  -- Induction on the level. A prime factor `p` of the level is removed by base change to an
  -- extension of degree `p` in which `w` is inert.
  induction g using induction_on_primes generalizing E with
  | zero => exact fun σ a ⟨_, h_level, _⟩ ↦ absurd rfl h_level
  | one => exact hr.isLabelledAt_one hf he hA h_prod_label h_roots
  | prime_mul p g hp ih =>
    obtain ⟨h_label, h_sep, h_deg, h_has⟩ := h_prod_label
    intro σ a h_tame
    have hσ : σ ∈ inertiaGroup Gal(Ω/E) A := h_tame.mem_inertiaGroup T
    obtain ⟨η, μ, u, h_step, h_unram, h_ram, hq⟩ := exists_isStepOfLocalChar_inert hw hA hp
    obtain ⟨_⟩ := h_step.nonempty_weilData
    have : IsStep (stepField μ) (ideleChar μ) := h_step.isStep
    have hAu : IsPlaceOver A u := h_step.isPlaceOver
    -- As `u` is unramified, `σ` fixes `stepField μ`, and there it has exponent `a` at level `g`.
    let σ' : Gal(Ω/stepField μ) := { σ with commutes' := fun x ↦ x.2 ⟨σ, h_unram hσ⟩ }
    obtain ⟨_, _, _, h_res_rank, h_res, h_tame'⟩ := IsTameExponent.exists_tower_of_unramified T
      (σ := σ') h_tame ((h_step.below_eq_iff u).2 rfl) hAu h_ram hq
    let j : ResField w →+* ResField u := algebraMap (ResField w) (ResField u)
    -- The characters `χ' l` of `ResField u` with the same names as the `χ l`
    let χ' (l : Fin s) : MulChar (ResField u) ℂ :=
      (charName T).symm (Units.map j.toMonoidHom (charName T (χ l)))
    have hχ' (l : Fin s) : (charName T (χ' l)).val = j (charName T (χ l)).val := by simp [χ']
    -- The label `Ξ` of `f` lifts to itself, so it is a character. Shintani lifting gives an
    -- eigenform `f'` over `stepField μ`, a weak base change of `f`, with the lifted label.
    let Ξ : Hall (ResField w) := New.labelChar T c * ∏ l, (detChar (χ l)).rankPart (t l)
    have h_char : Lift ℕ Ξ Ξ :=
      (lift_labelChar_self T h_label).mul_prod_rankPart_detChar T t fun _ ↦ rfl
    let Ξ' : Hall (ResField u) := New.labelChar T (c.map j) * ∏ l, (detChar (χ' l)).rankPart (t l)
    have h_shintani : Lift ℕ Ξ Ξ' :=
      (shintani_lift_labelChar (by rwa [h_res_rank]) T h_label).mul_prod_rankPart_detChar T t hχ'
    -- `f'` has weight `κ.baseChange`, Hecke polynomials `P'` and the label `Ξ'`
    obtain ⟨f', hf', P', he', h_bc, h_has'⟩ := exists_baseChange_hasLabel hw h_step.isSplit
      h_step.below_eq_iff (fun _ ↦ by simp [h_step.abelianLift_artinAt]) h_res
      (h_res_rank.trans h_step.finrank_eq.symm) hf
      (isChar_of_mem_virtualChars h_char.evalGL_mem_virtualChars) h_shintani h_has
    have h_sep' : (c.map j * ∏ l, (X - C (charName T (χ' l)).val)).Separable := by
      simpa [hχ', Polynomial.map_prod] using h_sep.map (f := j)
    have h_roots' (x : K) (hx : aeval x (c.map j) = 0) : x ^ (u.q ^ g - 1) = 1 := by
      rw [← hq, ← pow_mul]
      exact h_roots x ((c.aeval_map_algebraMap (ResField u) x).symm.trans hx)
    have h_map : c.map j * ∏ l, (X - C (charName T (χ' l)).val) ^ t l =
        (c * ∏ l, (X - C (charName T (χ l)).val) ^ t l).map j := by simp [hχ', Polynomial.map_prod]
    -- A representation `r'` is attached to `f'`. The induction hypothesis applies to it, and the
    -- three properties descend from `r'` to `r`.
    obtain ⟨r', hr'⟩ : ∃ r' : GalRep ℓ (stepField μ) n, Attached P' r' :=
      (sphericalCompat_std u hf' he').1
    obtain ⟨h_fin, h_jump, h_kill⟩ :=
      ih hf' he' hr' hAu ⟨h_label.map _, h_sep', h_deg, h_has'⟩ h_roots' h_tame'
    rw [h_map, aroots_map] at h_kill
    have hσ_mem : σ ∈ stepKer μ :=
      ⟨h_unram hσ, (hA.artinAt_trivial_iff_decompGroup_le μ).1 h_step.abelianLift_artinAt hσ.1⟩
    have h_down : DescendsAt μ r' r A := h_bc.descendsAt hr' he' he hr A
    exact ⟨h_down.isFiniteTypeAt h_fin, h_down.hasJumpsAt _ h_jump,
      h_down.polyKillsAt ⟨σ, hσ_mem⟩ _ h_kill⟩

/-- Let the Galois representation `r` be attached to the Hecke polynomials `P` of the eigenform `f`
of weight `κ`, which has the label `c` (of degree `d`), `χ l`, `t l` at the split place `w`
(`New.HasProductLabel`), and let `A` lie above `w`. Then (a) `r` is of finite type at `A` (finite on
inertia, or potentially crystalline above `ℓ`), (b) it has the Hodge–Tate jumps of `κ`, and (c) if
`σ` has tame exponent `a` at level `d!` (`New.GaloisRep.IsTameExponent`), then
`∏ x, (X - ιℓ ((T ^ a) x))` kills the action of `σ` (`New.GaloisRep.PolyKillsAt`), the product being
over the roots `x` in `K` of `c * ∏ l, (X - x_l) ^ t l`, where `x_l = New.charName T (χ l)`.

This is local-global compatibility at tame level, away from `ℓ` and at `ℓ`, restricted to inertia at
a split place and to depth-zero types.

Clause (c) is a weak form of what this compatibility (Barnet-Lamb–Gee–Geraghty–Taylor, Caraiani)
gives together with the description of the inertial parameters of depth-zero representations of
`GL_n` (see Emerton–Gee–Herzig). -/
lemma New.GaloisRep.Attached.isLabelledAt {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type}
    [Nonempty n] [Field E] [CMType E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n]
    {κ : Weight E} {f : Gf E n → WeylIndex n κ.1 → ℂ} {P : FinPlace E → ℂ[X]} {r : GalRep ℓ E n}
    {w : FinPlace E} {A : ValuationSubring Ω} {hw : star w ≠ w} {K : Type} [Field K]
    [Algebra (ResField w) K] {T : MulChar K ℂ} [IsFaithfulMulChar K T] {s d : ℕ}
    {c : (ResField w)[X]} {χ : Fin s → MulChar (ResField w) ℂ} {t : Fin s → ℕ} [WeilData E]
    (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P) (hr : Attached P r)
    (h_prod_label : HasProductLabel f hw T d c χ t) (hA : IsPlaceOver A w) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
    IsLabelledAt A T d.factorial (PolyKillsAt r A)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) := by
  have key : IsLabelledAt A T d.factorial
      (fun σ Q ↦
        IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n)) ∧ PolyKillsAt r A σ Q)
      (c * ∏ l, (X - C (charName T (χ l)).val) ^ t l) :=
    hr.isLabelledAt_of_root_pow_eq_one hf he hA h_prod_label
      fun x hx ↦ (h_prod_label.1.root_pow_eq_one hx).1
  -- The first two claims do not depend on `σ`, and some `σ₀` has a tame exponent.
  obtain ⟨⟨σ₀, hσ₀⟩, -⟩ := exists_isTameExponent T hA d
  obtain ⟨h_fin, h_jump, -⟩ := key hσ₀
  exact ⟨h_fin, h_jump, fun σ a h_tame ↦ let ⟨_, _, h_kill⟩ := key h_tame; h_kill⟩

end LabelCompatibility
