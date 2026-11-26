import Lib.Adelic.Unitary.CongruenceLevels
import Lib.General.Analysis.FiniteFourier
import Lib.Weil.Construction.WeilData

/-!
# Idelic generators of ideals, semilocal fields and tame local characters

The file collects local and idelic facts about number fields. For a CM field `E` it computes values
of the splitting character `υ`, and with `New.HasPrimitiveRoot5040 E` it shows that `New.Ô E` in the
finite adeles forms an adelic pair. It defines Schwartz–Bruhat functions, semilocal fields and tame
local characters, and shows that a finite product of completions is a semilocal field. An auxiliary
fact gives the valuation of natural numbers prime to one of valuation less than 1.

## Main definitions and results

* `New.exists_reduction_and_idele_generator`: a nonzero ideal `I` of `𝓞 E` has an idelic generator
  `t` in the integral finite adeles `New.Ô`, and `Ô / t Ô = 𝓞 / I`.
* `New.upsilon_toAdele`: the splitting character `υ` (`New.SplittingChar`) is trivial on the
  principal ideles.
* `New.upsilon_eq_prod_mul_of_v_eq`, `New.upsilon_eq_atUniformizer_zpow`,
  `New.upsilon_atUniformizer_mul_star`: values of `υ`, which is unramified at all finite places,
  computed from the valuations of the finite part and the values at the chosen uniformisers.
* `New.schwartzBruhat`: locally constant, compactly supported complex functions that vanish outside
  a set. `New.schwartzBruhat.comp`, `New.schwartzBruhat.isLocallyConstant_curry` and
  `New.integral_mem_of_isLocallyConstant` are tools for substituting and averaging.
* `New.SemilocalField`: conditions on a topological ring `F` that a finite product of
  non-archimedean local fields meets, with ring of integers `O` and uniformiser `ϖ`.
* `New.invOnUnits`, `New.TameLocalChar`: `χ⁻¹` cut off to the units of `O`, and the data showing
  that it comes from a primitive character (`New.Exchange.IsPrimitiveMulChar`) of the finite ring
  `O / ϖ`.

Notions from other files:
* `New.IsAdelic`: The properties of the pair Ô ⊂ 𝔸_f abstracted to R ⊂ A: R is open, compact and
  stable under conjugation, locally a valuation ring, contains a skew element i with −i·i = 1 and an
  element of trace 1, and −1 is a norm from R.
* `New.HasPrimitiveRoot5040`: `E` contains a primitive root of unity of order `7! = 5040`.
* `New.SplittingChar`: a unitary Hecke character `υ` of `E` that complex conjugation inverts and
  whose value at an idele `x` with unit finite part is `∏ x_τ / |x_τ|` over the infinite places
  `τ`; `υ.atUniformizer w` is its value at the chosen uniformiser at the finite place `w`.

## Relation to the literature

Known; see `Lib.ClassField.Global.CMSplittingCharacters` and `Lib.Weil.TameGaussSum` for sources.
-/

noncomputable section

/-!
## Idelic generators and the splitting character

An adele `x` is a pair: `x.1` the infinite and `x.2` the finite components. The valuation `v` is
multiplicative, with value `exp (-1)` at a uniformiser.
-/

namespace New

open SplittingChar NumberField Ideal Quotient IsDedekindDomain HeightOneSpectrum WithZero Valued
  RingEquiv

section

variable {E : Type*} [Field E] [NumberField E]

/-- For a nonzero ideal `I` of `𝓞 E` there is a finite idele `t` whose order at every finite place
`w` is the multiplicity of `w` in `I` and which is `1` at the places not dividing `I`. -/
lemma exists_idele_v_eq_exp_neg_multiplicity {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    ∃ t : (𝔸f E)ˣ,
      (∀ w : HeightOneSpectrum (𝓞 E), v (t.val w) = .exp (-multiplicity w.asIdeal I)) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), ¬I ≤ w.asIdeal → t.val w = 1 := by
  obtain ⟨t, ht⟩ := exists_idele_eq_uniformizer_zpow (fun w ↦ -multiplicity w.asIdeal I)
    ((finite_factors hI).subset fun w hw ↦ dvd_of_multiplicity_pos (by simp_all [pos_iff_ne_zero]))
  refine ⟨t, fun w ↦ by simp [ht], fun w hw ↦ ?_⟩
  have h_zero : multiplicity w.asIdeal I = 0 :=
    Nat.eq_zero_of_not_pos fun h ↦ hw (dvd_iff_le.1 (dvd_of_multiplicity_pos h))
  simp [ht, h_zero]

/-- Let `I` be a nonzero ideal of `𝓞 E` and `t` an integral finite adele whose order at every finite
place `w` is the multiplicity of `w` in `I`. Then the ideal `t Ô` of the ring `Ô` of integral finite
adeles contracts to `I`. -/
lemma under_span_singleton_of_v_eq {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) {t : Ô E}
    (ht : ∀ w : HeightOneSpectrum (𝓞 E), v (t.val w) = .exp (-multiplicity w.asIdeal I)) :
    (span {t}).under (𝓞 E) = I := by
  -- An integer lies in `t Ô` iff it lies in `w ^ multiplicity w I` for all `w`, that is, in `I`.
  refine .trans (ext fun c ↦ ?_) (iInf_maxPowDividing_eq hI)
  calc c ∈ (span {t}).under (𝓞 E)
    _ ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.intValuation c ≤ .exp (-multiplicity w.asIdeal I) := by
      simp [ht, Subtype.ext_iff, exists_eq_mul_iff_v_le, valuation_of_algebraMap,
        mem_span_singleton, dvd_def]
    _ ↔ c ∈ ⨅ w : HeightOneSpectrum (𝓞 E), w.maxPowDividing I := by
      simp [hI, maxPowDividing_eq_pow_multiplicity, ← intValuation_le_pow_iff_mem]

/-- Let `Ô` be the ring of integral finite adeles and `y` a finite adele. If the ideal `I` of `𝓞 E`
generates the principal ideal `t Ô` of `Ô`, then `I y ⊆ Ô` if and only if `t y ∈ Ô`. -/
lemma forall_smul_mem_Ô_iff_of_map_eq_span {I : Ideal (𝓞 E)} {t : 𝔸f E} (ht_mem : t ∈ Ô E)
    (ht : I.map (algebraMap (𝓞 E) (Ô E)) = span {⟨t, ht_mem⟩}) (y : 𝔸f E) :
    (∀ c ∈ I, c • y ∈ Ô E) ↔ t * y ∈ Ô E := by
  -- The `c` in `Ô` with `c y ∈ Ô` form an ideal `J`; it contains `I` iff it contains `I Ô = t Ô`.
  let J : Ideal (Ô E) :=
    { carrier := {c : Ô E | c.val * y ∈ Ô E}
      add_mem' := fun ha hb ↦ by simpa [add_mul] using add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c _ hx ↦ by simpa [mul_assoc] using mul_mem c.prop hx }
  calc (∀ c ∈ I, c • y ∈ Ô E) ↔ I ≤ J.comap (algebraMap (𝓞 E) (Ô E)) := by
        simp only [Algebra.smul_def]
        rfl -- by definition of `J` and `comap`
    _ ↔ span {⟨t, ht_mem⟩} ≤ J := by rw [← map_le_iff_le_comap, ht]
    _ ↔ t * y ∈ Ô E := by simp [J]

/-- A nonzero ideal `I` of `𝓞 E` becomes principal in the ring `Ô` of integral finite adeles
(a subring of the finite adeles `𝔸f E`), and `Ô / I Ô = 𝓞 / I`. There is a ring
map `ρ : Ô → 𝓞 / I` that (a) extends the reduction modulo `I` and (b) has kernel `I Ô`, and a
finite idele `t` that (c) is integral, is `1` at the places not dividing `I` and generates the
kernel, and (d) has order `ord_w I` at every `w`; (e) for a finite adele `y`, `I y ⊆ Ô` if and
only if `t y ∈ Ô`. -/
lemma exists_reduction_and_idele_generator {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    ∃ ρ : Ô E →+* 𝓞 E ⧸ I,
      (∀ a : 𝓞 E, ρ (algebraMap (𝓞 E) (Ô E) a) = a) ∧
      (∀ {x : Ô E}, ρ x = 0 ↔ x ∈ I.map (algebraMap (𝓞 E) (Ô E))) ∧
      ∃ t : (𝔸f E)ˣ,
        (t.val ∈ Ô E ∧
         (∀ w : HeightOneSpectrum (𝓞 E), ¬I ≤ w.asIdeal → t.val w = 1) ∧
         ∀ x : Ô E, ρ x = 0 ↔ t⁻¹.val * x ∈ Ô E) ∧
        (∀ w : HeightOneSpectrum (𝓞 E), v (t.val w) = .exp (-multiplicity w.asIdeal I)) ∧
        ∀ y : 𝔸f E, (∀ c ∈ I, c • y ∈ Ô E) ↔ t.val * y ∈ Ô E := by
  -- The ideal `T = t Ô` contracts to `I`, so `I Ô = T` and `𝓞 / I → Ô / T` is bijective; `ρ` is
  -- the reduction modulo `T` followed by the inverse.
  obtain ⟨t, h_val, h_one⟩ := exists_idele_v_eq_exp_neg_multiplicity hI
  obtain ⟨a, ha_mem, ha_ne⟩ := I.ne_bot_iff.1 hI
  have h_int : t.val ∈ Ô E := by simp [mem_Ô, h_val, ← log_le_log]
  let T : Ideal (Ô E) := span {⟨t, h_int⟩}
  have h_under : T.under (𝓞 E) = I := under_span_singleton_of_v_eq (t := ⟨t, h_int⟩) hI h_val
  have h_map : I.map (algebraMap (𝓞 E) (Ô E)) = T := by
    rw [← map_under_Ô (I := T) ha_ne (h_under.ge ha_mem), h_under]
  let e : (𝓞 E ⧸ I) ≃+* Ô E ⧸ T := ofBijective _ (bijective_quot_Ô ha_ne h_under ha_mem)
  have h_extends (c : 𝓞 E) : e.symm (mk T (algebraMap (𝓞 E) (Ô E) c)) = mk I c := by
    simp [e, symm_apply_eq]
  have h_ker {x : Ô E} : e.symm (mk T x) = 0 ↔ x ∈ T := by simp [eq_zero_iff_mem]
  have h_mem_T (x : Ô E) : x ∈ T ↔ t⁻¹.val * x ∈ Ô E := by
    simp [T, Subtype.ext_iff, ← t.inv_mul_eq_iff_eq_mul, mem_span_singleton, dvd_def]
  exact ⟨e.symm.toRingHom.comp (mk T), h_extends, h_ker.trans (by rw [h_map]), t,
    ⟨h_int, h_one, fun x ↦ h_ker.trans (h_mem_T x)⟩, h_val,
    forall_smul_mem_Ô_iff_of_map_eq_span h_int h_map⟩

end

variable {E : Type*} [Field E] [CMType E] [SplittingChar E]

/-- The splitting character `υ` is trivial on the principal ideles, the images of `Eˣ`. -/
lemma upsilon_toAdele (x : Eˣ) : υ.val (x.map (toAdele (E := E)) : (𝔸 E)ˣ) = 1 := υ.2 _ ⟨x, rfl⟩

/-- Let υ be the splitting character. If an idele x and a finite idele y have the same valuation at
every finite place, then υ(x) is υ(y) times the product of x_τ/|x_τ| over the infinite places τ.
Here y is read as an idele with component 1 at the infinite places. -/
lemma upsilon_eq_prod_mul_of_v_eq {x : (𝔸 E)ˣ} (y : (𝔸f E)ˣ)
    (h_val : ∀ w : HeightOneSpectrum (𝓞 E), v (x.val.2 w) = v (y.val w)) :
    υ.val x = (∏ τ : InfinitePlace E, x.val.1 τ / ‖x.val.1 τ‖) * υ.val (finIdeleIncl y) := by
  -- The idele `x / y` has the infinite part of `x`, and its finite part has valuation `1`
  -- everywhere (`idelesUnitOff ∅`), so it is a unit of `Ô`; `υ_unit` gives the value of `υ`.
  let z : (𝔸 E)ˣ := x * finIdeleIncl y⁻¹
  have h_mem : z.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)) ∈ idelesUnitOff ∅ := by
    -- by `h_val` the valuations of `x` and `y` cancel at every place
    simpa [z, idelesUnitOff, Units.ext_iff, field] using! h_val
  simpa [z, mul_inv_eq_iff_eq_mul₀] using υ_unit z (idelesUnitOff_empty.le h_mem)

/-- Let `υ` be the splitting character and let the idele `x`, with infinite components `x.val.1`
and finite components `x.val.2`, be a unit at all finite places other than `w`. Then `υ x` is
`∏ x_τ / |x_τ|` over the infinite places `τ`, times the value `υ.atUniformizer w` of `υ` at the
uniformiser at `w` to the power `ord_w x` (which is `-log (v (x.val.2 w))`). -/
lemma upsilon_eq_atUniformizer_zpow (w : FinPlace E) {x : (𝔸 E)ˣ}
    (h_unit : ∀ u : FinPlace E, u ≠ w → v (x.val.2 u) = 1) :
    υ.val x = (∏ τ : InfinitePlace E, x.val.1 τ / ‖x.val.1 τ‖) *
      υ.atUniformizer w ^ (-log (v (x.val.2 w))) := by
  -- Apply `upsilon_eq_prod_mul_of_v_eq` to the power of the uniformiser at `w` that has the
  -- valuation of `x` there.
  let xw : (LocField w)ˣ := ideleAt w (x.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)))
  let k : ℤ := log (v xw.val)
  let y : (𝔸f E)ˣ := locIdele w ((uniformizer w)⁻¹ ^ k)
  have h_val (u : FinPlace E) : v (x.val.2 u) = v (y.val u) := by
    obtain rfl | hu := eq_or_ne u w
    · change v xw.val = v (y.val u)
      simp [y, k, -map_inv, -map_zpow]
    · simp [y, h_unit u hu, hu, -map_inv, -map_zpow]
  simpa [k, y, xw] using! upsilon_eq_prod_mul_of_v_eq y h_val

/-- The values of the splitting character at the uniformisers of a finite place `w` and of its
complex conjugate are inverse to each other. -/
lemma upsilon_atUniformizer_mul_star (w : FinPlace E) :
    υ.atUniformizer w * υ.atUniformizer (star w) = 1 := by
  -- The value of `υ` at the conjugate of the uniformiser idele at `w` is `υ.atUniformizer (star w)`
  -- by `upsilon_eq_atUniformizer_zpow`, and it is `(υ.atUniformizer w)⁻¹` by `υ_star`.
  have h_at : (υ.val (star (locFullIdele w (uniformizer w))) : ℂ) = υ.atUniformizer (star w) := by
    -- the conjugate idele has a uniformiser at `star w` and `1` at all the other places
    rw [upsilon_eq_atUniformizer_zpow (star w)
      (by simp +contextual [star_singleAdele, locFullIdele])]
    simp [star_singleAdele, locFullIdele]
  have h_self : (υ.val (locFullIdele w (uniformizer w)) : ℂ) = υ.atUniformizer w := by
    simp [HeckeChar.atUniformizer, HeckeChar.finPart, locIdele, locFullIdele]
  simp [← h_at, ← h_self, υ_star]

end New

/-! ## Natural numbers of valuation one -/

/-- If the natural number `p` has valuation less than `1` at a valuation subring `B` of a field,
then every natural number `q` prime to `p` has valuation `1` at `B`. -/
lemma Nat.Coprime.valuation_eq_one {Ω : Type*} [Field Ω] {B : ValuationSubring Ω} {p q : ℕ}
    (hpq : p.Coprime q) (hp_lt : B.valuation p < 1) : B.valuation q = 1 := by
  have hq_notMem : (q : B) ∉ IsLocalRing.maximalIdeal B :=
    Ideal.IsPrime.notMem_of_isCoprime_of_mem hpq.cast (B.coe_mem_nonunits_iff.mp hp_lt)
  exact (B.valuation_eq_one_iff q).mp (IsLocalRing.notMem_maximalIdeal.mp hq_notMem)

/-!
## The integral finite adeles as an adelic pair

The instance `New.isAdelic_Ô` lets the local results, proved for an abstract pair `R ⊆ A` with
`New.IsAdelic R`, be applied to the integral finite adeles `New.Ô E` of a CM field `E` with
`New.HasPrimitiveRoot5040 E`.
-/

/-- The integral finite adeles of a CM field `E` with `HasPrimitiveRoot5040 E` have the properties
collected in `IsAdelic`. -/
instance New.isAdelic_Ô {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
    [HasPrimitiveRoot5040 E] : IsAdelic (Ô E) where
  isOpen_isCompact := ⟨isOpen_Ô, isCompact_Ô⟩
  isValuationPair := isValuationPair_Ô
  exists_skew_unit := by
    -- the integers `i` and `τ` of `E` keep their relations in the finite adeles
    obtain ⟨i, τ, hi_sq, hi_star, hτ, -⟩ :=
      HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
    refine ⟨algebraMap E (𝔸f E) i, coe_mem_Ô i, algebraMap E (𝔸f E) τ, coe_mem_Ô τ, ?_⟩
    simp only [neg_mul, star_algebraMap_finAdele]
    norm_cast
    exact ⟨by rw [hi_sq, neg_neg], hi_star, hτ⟩
  exists_norm_neg_one := ⟨_, by simp, star_normNegOne_mul_self⟩

/-!
## Schwartz–Bruhat spaces, semilocal fields and tame characters

Schwartz–Bruhat functions on topological spaces, then semilocal fields `F` (rings that behave like
finite products of non-archimedean local fields) and tame characters of them.
-/

section LocalDefs

open MeasureTheory

namespace New

variable {X : Type*} [TopologicalSpace X] {s : Set X} {φ : X → ℂ} {Γ Y Z : Type*}
  [TopologicalSpace Γ] [TopologicalSpace Y]

/-! ### Locally constant functions with compact support -/

/-- The space of locally constant, compactly supported complex functions on X that vanish
outside s. -/
def schwartzBruhat (s : Set X) : Submodule ℂ (X → ℂ) :=
  Submodule.ofLinearComb {f : X → ℂ | IsLocallyConstant f ∧ HasCompactSupport f ∧ f.support ⊆ s}
      ⟨0, IsLocallyConstant.zero, HasCompactSupport.zero, nofun⟩ <| by
    intro f ⟨f_const, f_compact, f_supp⟩ g ⟨g_const, g_compact, g_supp⟩ a b
    rw [Function.support_subset_iff'] at f_supp g_supp
    exact ⟨f_const.comp₂ g_const fun x y ↦ a * x + b * y, f_compact.mul_left.add g_compact.mul_left,
      Function.support_subset_iff'.2 fun x hx ↦ by simp [f_supp x hx, g_supp x hx]⟩

/-- Let `f : Y → X` be continuous with a continuous left inverse `g` that maps `s` into `t`. If
`φ` is locally constant, compactly supported and zero outside `s`, then `φ ∘ f` is locally
constant, compactly supported and zero outside `t`. -/
lemma schwartzBruhat.comp [T2Space X] {t : Set Y} (hφ : φ ∈ schwartzBruhat s) {f : Y → X}
    (g : X → Y) (hgf : g.LeftInverse f) (hs : s.MapsTo g t)
    (hf : Continuous f := by fun_prop) (hg : Continuous g := by fun_prop) :
    φ ∘ f ∈ schwartzBruhat t := by
  obtain ⟨h_const, h_compact, h_supp⟩ := hφ
  -- `f` is a closed embedding, having the continuous left inverse `g`;
  -- if `φ (f y) ≠ 0` then `f y ∈ s`, so `y = g (f y) ∈ t`
  exact ⟨h_const.comp_continuous hf, h_compact.comp_isClosedEmbedding (hgf.isClosedEmbedding hg hf),
    fun y hy ↦ by simpa [hgf y] using hs (h_supp hy)⟩

/-- Let `ψ γ` be a family of functions on `X` that is locally constant jointly in the parameter `γ`
and the point. On a compact set `K`, the functions `ψ γ` agree with `ψ k` for `γ` near `k`. -/
lemma eventually_eqOn_of_isLocallyConstant_uncurry {ψ : Γ → X → Z}
    (hψ : IsLocallyConstant ψ.uncurry) {K : Set X} (hK : IsCompact K) (k : Γ) :
    ∀ᶠ γ : Γ in nhds k, ∀ x ∈ K, ψ γ x = ψ k x := by
  refine hK.eventually_forall_of_forall_eventually fun x _ ↦ ?_
  have hψ_k : IsLocallyConstant fun z : Γ × X ↦ ψ k z.2 :=
    hψ.comp_continuous (f := fun z : Γ × X ↦ (k, z.2)) (by fun_prop)
  filter_upwards [hψ.eventually_eq (k, x), hψ_k.eventually_eq (k, x)] with z h_left h_right using
    h_left.trans h_right.symm

/-- Let `f γ : Y → X` be a family of maps with left inverses `g γ`, both jointly continuous in the
parameter `γ` and the point. If `φ` is locally constant, compactly supported and zero outside `s`,
then the function `y ↦ φ (f γ y)` depends on `γ` in a locally constant way. -/
lemma schwartzBruhat.isLocallyConstant_curry (hφ : φ ∈ schwartzBruhat s) (f : Γ → Y → X)
    (g : Γ → X → Y) (hgf : ∀ (γ : Γ) (y : Y), g γ (f γ y) = y)
    (hf : Continuous ↿f := by fun_prop) (hg : Continuous ↿g := by fun_prop) :
    IsLocallyConstant fun (γ : Γ) (y : Y) ↦ φ (f γ y) := by
  -- The family `x ↦ φ (f a (g b x))` is locally constant in `(a, b, x)`. On the compact support of
  -- `φ` its members therefore all agree for `a` and `b` in an open set `U ∋ k`.
  obtain ⟨h_const, h_compact, -⟩ := hφ
  refine (IsLocallyConstant.iff_exists_open _).2 fun k ↦ ?_
  let ψ (ab : Γ × Γ) (x : X) : ℂ := φ (f ab.1 (g ab.2 x))
  have hψ : IsLocallyConstant ψ.uncurry := h_const.comp_continuous (by fun_prop)
  obtain ⟨U, hU_open, hk, hU⟩ : ∃ U : Set Γ, IsOpen U ∧ k ∈ U ∧
      U ×ˢ U ⊆ {ab : Γ × Γ | ∀ x ∈ tsupport φ, ψ ab x = ψ (k, k) x} :=
    exists_nhds_square (eventually_eqOn_of_isLocallyConstant_uncurry hψ h_compact (k, k))
  -- If `φ (f b y) ≠ 0`, compare `(a, b)` with `(b, b)` at the point `x = f b y` of the support.
  have eq_of_ne_zero {a b : Γ} (ha : a ∈ U) (hb : b ∈ U) {y : Y} (hy : φ (f b y) ≠ 0) :
      φ (f a y) = φ (f b y) := by
    have hx : f b y ∈ tsupport φ := subset_tsupport φ hy
    calc
      φ (f a y) = ψ (a, b) (f b y) := by simp only [ψ, hgf]
      _ = ψ (k, k) (f b y) := hU ⟨ha, hb⟩ _ hx
      _ = ψ (b, b) (f b y) := (hU ⟨hb, hb⟩ _ hx).symm
      _ = φ (f b y) := by simp only [ψ, hgf]
  refine ⟨U, hU_open, hk, fun a ha ↦ funext fun y ↦ ?_⟩
  -- Both values are zero, or one is not and `eq_of_ne_zero` makes them equal.
  by_cases hk_zero : φ (f k y) = 0
  · by_cases ha_zero : φ (f a y) = 0
    · simp [hk_zero, ha_zero]
    · exact (eq_of_ne_zero hk ha ha_zero).symm
  · exact eq_of_ne_zero ha hk hk_zero

/-- The pointwise integral of a locally constant family of functions over a compact space, for a
finite measure, lies in every subspace `P` that contains all members of the family. -/
lemma integral_mem_of_isLocallyConstant [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {f : Y → Z → ℂ} (hf : IsLocallyConstant f)
    {P : Submodule ℂ (Z → ℂ)} (h_mem : ∀ g : Y, f g ∈ P) :
    (fun z : Z ↦ ∫ g : Y, f g z ∂μ) ∈ P := by
  classical
  -- `f` takes finitely many values `v`, all in `P`. The integral is their sum, with `v` weighted
  -- by the measure of the set where `f = v`.
  let T : Finset (Z → ℂ) := hf.range_finite.toFinset
  have h_meas (v : Z → ℂ) : MeasurableSet (f ⁻¹' {v}) := (hf _).measurableSet
  have integral_eq : (fun z : Z ↦ ∫ g, f g z ∂μ) = ∑ v ∈ T, μ.real (f ⁻¹' {v}) • v := by
    ext z
    calc ∫ g, f g z ∂μ = ∫ g, ∑ v ∈ T, (f ⁻¹' {v}).indicator (fun _ ↦ v z) g ∂μ := by
          simp [T, Set.indicator]
      _ = (∑ v ∈ T, μ.real (f ⁻¹' {v}) • v) z := by
        rw [integral_finsetSum _ fun v _ ↦ (integrable_const _).indicator (h_meas v)]
        simp [integral_indicator_const, h_meas]
  have hT : ∀ v ∈ T, v ∈ P := by simpa [T] using h_mem
  rw [integral_eq]
  exact P.sum_mem fun v hv ↦ P.smul_of_tower_mem _ (hT v hv)

/-! ### Semilocal fields and their characters -/

/-- Conditions met by a finite product of non-archimedean local fields: a locally compact ring with
Haar measure, compact open subring O of volume one, an element ϖ of O that is invertible in F and
topologically nilpotent, and `New.IsValuationPair O`. -/
class SemilocalField (F : Type*) extends CommRing F, TopologicalSpace F, MeasureSpace F,
  IsTopologicalRing F, PolishSpace F, LocallyCompactSpace F, BorelSpace F,
  volume.IsAddHaarMeasure where
  /-- The ring of integers. -/
  O : Subring F
  /-- The element called the uniformiser: a unit of `F`, only required to be integral and
  topologically nilpotent. -/
  ϖ : Fˣ
  /-- The uniformiser is integral. -/
  ϖ_mem : ↑ϖ ∈ O
  /-- The ring of integers is compact. -/
  isCompact_O : IsCompact (O : Set F)
  /-- The Haar measure gives the ring of integers volume one. -/
  volume_O : volume O = 1
  /-- The ring of integers is open. -/
  isOpen_O : _root_.IsOpen O.carrier
  /-- The powers of the uniformiser tend to zero. -/
  isTopologicallyNilpotent_ϖ : IsTopologicallyNilpotent ϖ.1
  /-- As in a product of valuation rings, for `a, b` in `F` there is an idempotent `e` of `O` such
  that `a` and `b` are `O`-multiples of `(1 - e) a + e b`. -/
  isValuationPair : IsValuationPair O

variable {F : Type} [V : SemilocalField F] (χ : MulChar F ℂ)

open SemilocalField

/-- x is a unit of the subring O. -/
@[simp]
abbrev IsIntegralUnit (x : F) : Prop := x ∈ O ∧ ∃ s ∈ O, s * x = 1

open scoped Classical in
/-- `χ⁻¹` on the units of `O`, zero elsewhere. -/
def invOnUnits (x : F) : ℂ := if IsIntegralUnit x then (χ x)⁻¹ else 0

/-- A finite residue ring O/ϖO with the reduction π from O onto it, and a primitive character η
(`New.Exchange.IsPrimitiveMulChar`) of it such that η ∘ π is χ⁻¹ on the units of O and 0 on the rest
of O. -/
class TameLocalChar where
  /-- The residue ring `O / ϖ`. -/
  ResidueRing : Type
  /-- The ring structure of the residue ring. -/
  [commRing : CommRing ResidueRing]
  /-- The residue ring is finite. -/
  [finite : Finite ResidueRing]
  /-- The reduction `π` from `O` to the residue ring. -/
  reduction : V.O →+* ResidueRing
  /-- The character `η` of the residue ring through which `χ⁻¹` factors on the units of `O`. -/
  resChar : MulChar ResidueRing ℂ
  /-- The reduction is surjective with kernel `ϖ O`. -/
  reduction_surjective_and_eq_zero_iff : Function.Surjective reduction ∧ ∀ x : O,
    reduction x = 0 ↔ ϖ⁻¹.1 * x.1 ∈ O
  /-- `η` is primitive, and `η ∘ π` is `χ⁻¹` on the units of `O` and zero on the rest of `O`. -/
  isPrimitive_resChar_and_invOnUnits_eq :
      Exchange.IsPrimitiveMulChar resChar ∧ ∀ x : O, invOnUnits χ x.1 = resChar (reduction x)

attribute [instance_reducible, instance] TameLocalChar.commRing
attribute [instance] TameLocalChar.finite

lemma isIntegralUnit_iff_isUnit {u : V.O} : IsIntegralUnit u.val ↔ IsUnit u := by
  simp [isUnit_iff_exists_inv', Subtype.ext_iff]

/-- The additive character ψ is continuous and has conductor O: ψ is trivial on tO exactly when t
lies in O. -/
def HasIntegralConductor (ψ : AddChar F ℂ) : Prop :=
  Continuous ψ ∧ ∀ t : F, (∀ s ∈ O, ψ (t * s) = 1) ↔ t ∈ O

end New

end LocalDefs

/-!
## Finite products of completions

For a finite set `P` of finite places of a number field `E`, the product `New.LocProd` of the
completions `New.LocField` at `P` satisfies the conditions `New.SemilocalField`.
-/

namespace New

open Valued Subring

variable {E : Type} [Field E] [NumberField E] (P : Finset (FinPlace E))

/-- The product of the completions E_w over the places w in P. -/
abbrev LocProd : Type := ∀ w : P, LocField w.val

variable {P}

/-- The product of the completions at the places in `P` is a semilocal field: `O` is the product of
the local rings of integers and `ϖ` is the family of the chosen uniformisers. -/
noncomputable instance : SemilocalField (LocProd P) where
  O := .copy (⨅ i : P, v.integer.comap (Pi.evalRingHom (fun w : P ↦ LocField w.val) i))
    (Set.univ.pi fun i : P ↦ (LocInt i.val : Set (LocField i.val))) <| by
      ext x
      simp [v.mem_integer_iff, mem_LocInt]
  ϖ := MulEquiv.piUnits.symm fun i : P ↦ uniformizer i.val
  ϖ_mem i _ := by simp +decide [mem_LocInt]
  isCompact_O := isCompact_univ_pi fun i : P ↦ isCompact_LocInt i.val
  volume_O := (MeasureTheory.volume_pi_pi _).trans (by simp)
  isOpen_O := isOpen_set_pi Set.finite_univ fun i _ ↦ isOpen_integer (LocField i.val)
  isTopologicallyNilpotent_ϖ :=
    tendsto_pi_nhds.mpr fun i ↦ tendsto_zero_pow_of_v_lt_one (by simp +decide)
  isValuationPair a b := by
    -- the idempotent `e` and the two multipliers `y` and `z` are chosen componentwise
    have h_local (i : P) : ∃ e ∈ LocInt i.val, ∃ y ∈ LocInt i.val, ∃ z ∈ LocInt i.val,
        e * e = e ∧ y * (a i - e * (a i - b i)) = a i ∧ z * (a i - e * (a i - b i)) = b i := by
      obtain ⟨e, he_idem, he_le⟩ := isValuationPair_valuationSubring (LocInt i.val) (a i) (b i)
      simp only [sup_le_iff, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
        at he_le
      obtain ⟨⟨y, hy⟩, z, hz⟩ := he_le
      exact ⟨e, e.prop, y, y.prop, z, z.prop, he_idem, hy, hz⟩
    choose e he_mem y hy_mem z hz_mem he_idem hy hz using h_local
    refine ⟨⟨e, fun i _ ↦ he_mem i⟩, funext he_idem, ?_⟩
    simp only [sup_le_iff, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨⟨y, fun i _ ↦ hy_mem i⟩, funext hy⟩, ⟨z, fun i _ ↦ hz_mem i⟩, funext hz⟩

/-- An element of the product of the completions at `P` lies in the ring of integers `O` exactly
when each of its components has valuation at most `1`. -/
lemma mem_O_locProd {x : LocProd P} : x ∈ SemilocalField.O ↔ ∀ i : P, v (x i) ≤ 1 := Set.mem_univ_pi

end New

end
