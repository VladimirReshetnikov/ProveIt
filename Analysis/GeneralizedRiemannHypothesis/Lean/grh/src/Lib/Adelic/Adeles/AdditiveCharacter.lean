import Lib.Adelic.Adeles.Basic
import Lib.Adelic.QuotientMeasure.Basic
import Lib.General.Groups.CongruenceSubgroups

/-!
# The additive character, Haar measures and the rational lattice in the adeles

The adeles `New.𝔸` of a number field `E` are one copy of `ℂ` for each infinite place, times the
finite adeles `New.𝔸f`; this is the adele ring when `E` is totally complex. `New.Ô` is the ring of
integral finite adeles. The file defines the standard additive character and the Haar measures
used in Fourier analysis on `New.𝔸`. For a totally complex field `E`, it proves that `E`, embedded
diagonally by `New.toAdele`, is a cocompact lattice of covolume one, and so are vectors and matrices
over `E`. The proof uses a fundamental domain built from a fractional ideal.

## Main definitions and results

* `New.ψf`: the character of the finite adeles that is trivial on `New.Ô` (`New.ψf_eq_one_of_mem`)
  and is `𝐞 (tr a)` on `a ∈ E` (`New.ψf_coe`), where `𝐞 t = exp (2πi t)`. These two properties
  define it, since every finite adele is an element of `E` plus an integral one.
* `New.stdAddChar`: its product with `𝐞 (-∑_w 2 re x_w)`. Here `x_w` is the component of the adele
  at the infinite place `w`.
* `New.volume_Ô`: `volume` on the finite adeles gives `New.Ô` the mass `New.volÔ`. On a completion
  `New.LocField w`, `volume` gives the local integers mass one (`New.volume_LocInt`). On the adeles
  it is the product with Lebesgue measure on each `ℂ`.
* `New.ratAdeles`, `New.ratVectors`, `New.ratMatrices`: the rational points, vectors and matrices.
* `New.HasFundDomain`: a compact set contains a fundamental domain of volume one.
* `New.IsCovolOneLattice`: a discrete cocompact subgroup whose quotient measure has mass one.

Notions from other files:
* `New.LocField`, `New.LocInt`: The completion E_w of E at the finite place w and its ring of
  integers.
* `New.PlaceEmbedding E`: a choice, for each infinite place `w`, of a complex embedding `Φ w` of
  `E` that induces `w`. The map `New.toAdele` uses these embeddings at the infinite places.

## Relation to the literature

For totally complex `E` the file proves a known result: a number field is a discrete subgroup of its
adeles with compact quotient, here with a measure for which the covolume is one.
-/

noncomputable section

/-!
## A fundamental domain for a fractional ideal and its volume

`New.exists_fundDomain_prod` builds a fundamental domain `F ×ˢ O` for a number field `I` acting by
translations on `V × W` (in the applications: infinite part times finite part of adeles), with `F` a
fundamental parallelotope of a fractional ideal, and gives the volume of `F`.
-/

section FundamentalDomain

open MeasureTheory NumberField mixedEmbedding ZSpan nonZeroDivisors

open scoped Classical in
/-- Let `j : I →+ V × W` be additive on the number field `I`. Assume that the second component of
`j` lies in the subgroup `O` exactly on the fractional ideal `J`, and that `W` is the sum of the
second components and `O`. Assume also that the first component is the Minkowski embedding followed
by a measure-preserving linear isomorphism `e`. Then there is a bounded measurable set `F` in `V`
such that (a) `F` has volume `N(J) 2^(-r₂) √|disc I|`, with `r₂` the number of complex places, and
(b) for each `x` exactly one `a : I` has `j a + x ∈ F ×ˢ O`. -/
lemma New.exists_fundDomain_prod {I V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasureSpace V] [BorelSpace V] [AddCommGroup W] [Field I] [NumberField I] (j : I →+ V × W)
    (O : AddSubgroup W) (J : (FractionalIdeal (𝓞 I)⁰ I)ˣ) (hO : ∀ a : I, (j a).2 ∈ O ↔ a ∈ J.val)
    (h_approx : ∀ w : W, ∃ a : I, w - (j a).2 ∈ O)
    (e : mixedSpace I ≃ₗ[ℝ] V) (he : MeasurePreserving e)
    (h_emb : ∀ a : I, e (mixedEmbedding I a) = (j a).1) :
    ∃ F : Set V,
      MeasurableSet F ∧
      Bornology.IsBounded F ∧
      -- (a)
      volume F =
        ENNReal.ofReal J.val.absNorm * (2⁻¹ ^ InfinitePlace.nrComplexPlaces I * ‖discr I‖₊.sqrt) ∧
      -- (b)
      ∀ x : V × W, ∃! a : I, j a + x ∈ F ×ˢ O := by
  -- `F` is the fundamental domain of the lattice `J`, moved to `V` by `e`.
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ J) ℝ V :=
    (fractionalIdealLatticeBasis I J).map e
  refine ⟨fundamentalDomain b, by measurability, fundamentalDomain_isBounded b, ?_, fun x ↦ ?_⟩
  · -- `e` preserves the measure; Mathlib has the covolumes of `J` and of the ring of integers
    have h_preimage : e ⁻¹' fundamentalDomain b =
        fundamentalDomain (fractionalIdealLatticeBasis I J) := by
      simp [b, ← map_fundamentalDomain, e.injective.preimage_image]
    rw [← he.measure_preimage (by measurability), h_preimage,
      volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis]
  · -- First move the second component into `O` by subtracting some `j a`. The elements that keep
    -- it in `O` are those of `J`, and exactly one of them moves the first component into `F`.
    obtain ⟨a, ha⟩ := h_approx x.2
    have h_span (v : V) : v ∈ Submodule.span ℤ (Set.range b) ↔ ∃ c ∈ J.val, (j c).1 = v := by
      simp [b, ← map, ← h_emb, mem_span_fractionalIdealLatticeBasis]
    have h_inj : Function.Injective fun c : I ↦ (j c).1 := by
      simpa [← h_emb, Function.comp_def] using e.injective.comp (mixedEmbedding_injective I)
    have h_unique : ∃! c : I, (j c).1 + (x - j a).1 ∈ fundamentalDomain b ∧ c ∈ J.val := by
      obtain ⟨⟨v, hv⟩, h_mem, h_uniq⟩ := exist_unique_vadd_mem_fundamentalDomain b (x - j a).1
      obtain ⟨c, hc, rfl⟩ := (h_span v).1 hv
      exact ⟨c, ⟨h_mem, hc⟩, fun d ⟨hd_mem, hd⟩ ↦ h_inj <|
        congrArg Subtype.val (h_uniq ⟨(j d).1, (h_span _).2 ⟨d, hd, rfl⟩⟩ hd_mem)⟩
    -- the translate sought is `c - a`
    refine (Equiv.subRight a).existsUnique_congr_right.1 ?_
    simpa [add_comm_sub, add_mem_cancel_right ha, hO] using h_unique

end FundamentalDomain

/-!
## The standard additive character and the Haar measures on adeles

Instances give the topological and measurable structure of the adeles, the finite adeles, the
completions `New.LocField w` and the unitary groups `New.U J` of complex matrices.
-/

section AdditiveCharDefs

open NumberField MeasureTheory Measure FourierTransform Algebra AddChar QuotientAddGroup

namespace New

variable (E : Type*) [Field E] [NumberField E]

/-! ### The standard additive character and the mass of the integral adeles -/

/-- The character `𝐞 t = exp (2πi t)` is trivial exactly at the integers. -/
lemma fourierChar_eq_one_iff {t : ℝ} : 𝐞 t = 1 ↔ ∃ n : ℤ, t = n :=
  Circle.exp_eq_one.trans (by field_simp)

/-- The number 2^{r₂}/√|disc E|, where r₂ is the number of complex places of E. When E is totally
complex and the infinite places carry Lebesgue measure, it is the volume of the integral finite
adeles for which the quotient of the adeles by E has total mass one. -/
def volÔ : NNReal := 2 ^ InfinitePlace.nrComplexPlaces E / ‖NumberField.discr E‖₊.sqrt

/-- Every class of finite adeles modulo `Ô` contains an element of `E`. -/
lemma mk_algebraMap_surjective :
    Function.Surjective ((mk' (Ô E).toAddSubgroup).comp (algebraMap E (𝔸f E) : E →+ 𝔸f E)) := by
  rintro ⟨x⟩
  exact (exists_sub_mem_Ô x).imp fun a ha ↦ (eq_iff_sub_mem.mpr ha).symm

/-- For an algebraic integer `a` of `E`, the value `𝐞 (tr a) = exp (2πi Tr_{E/ℚ} a)` is one. -/
lemma fourierChar_trace_eq_one {a : E} (ha : IsIntegral ℤ a) : 𝐞 (trace ℚ E a) = 1 :=
  -- the trace of an algebraic integer is an integer
  fourierChar_eq_one_iff.mpr ⟨trace ℤ (𝓞 E) ⟨a, ha⟩, mod_cast (coe_trace_int ⟨a, ha⟩).symm⟩

/-- The standard additive character of the finite adeles: ψ_f(x) = exp(2πi Tr_{E/ℚ}(a)) for any
a in E with x − a integral. -/
def ψf : AddChar (𝔸f E) Circle :=
  -- `𝐞 ∘ tr` on `E` kills the algebraic integers, so it descends along the surjection
  -- `E → 𝔸f E ⧸ Ô E`; compose with the quotient map `𝔸f E → 𝔸f E ⧸ Ô E`.
  toAddMonoidHomEquiv.symm <|
    AddMonoidHom.comp
      (((mk' (Ô E).toAddSubgroup).comp (algebraMap E (𝔸f E))).liftOfSurjective
        (mk_algebraMap_surjective E)
        ⟨AddMonoidHom.mk' (fun a : E ↦ 𝐞 (trace ℚ E a)) (by aesop (add simp map_add_eq_mul)),
          fun a ha ↦ fourierChar_trace_eq_one E (algebraMap_mem_Ô.1 (by aesop))⟩)
      (mk' (Ô E).toAddSubgroup)

/-- The standard additive character of `New.𝔸 E` (the adele ring when E is totally complex): the
product of exp(−2πi ∑_w 2 Re x_w) over the infinite places and ψ_f of the finite part. -/
def stdAddChar : AddChar (𝔸 E) Circle where
  toFun x := 𝐞 (-∑ w : InfinitePlace E, 2 * (x.1 w).re) * ψf E x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    simp [mul_add, Finset.sum_add_distrib, map_add_eq_mul]
    grind

variable {E} {n : Type*} (w : FinPlace E) [Fintype n] [DecidableEq n] (J : Matrix n n ℂ)

instance : PolishSpace (U J) where

instance : LocallyCompactSpace (U J) := inferInstance

instance : MeasureSpace (LocField w) where
  -- the Haar measure that gives the local ring of integers mass one
  volume :=
    addHaarMeasure ⟨⟨LocInt w, isCompact_LocInt w⟩,
      (Valued.isOpen_integer (LocField w)).interior_eq.substr (by simp)⟩

instance : IsAddHaarMeasure (volume (α := LocField w)) := isAddHaarMeasure_addHaarMeasure _

/-- The chosen Haar measure on the completion `E_w` gives its ring of integers mass one. -/
@[simp]
lemma volume_LocInt : volume (LocInt w : Set (LocField w)) = 1 := addHaarMeasure_self

@[simp]
lemma volÔ_ne_zero : volÔ E ≠ 0 := by simp [volÔ, discr_ne_zero]

instance : MeasureSpace (𝔸f E) where
  -- the Haar measure that gives `Ô E` the mass `volÔ E`
  volume := volÔ E • addHaarMeasure ⟨⟨Ô E, isCompact_Ô⟩, by simp [isOpen_Ô.interior_eq]⟩

instance : IsAddHaarMeasure (volume (α := 𝔸f E)) := .nnreal_smul _ (by simp)

/-- For the chosen Haar measure on the finite adeles of E, the ring Ô of integral finite adeles
has volume 2^{r₂}/√|disc E|. -/
@[simp]
lemma volume_Ô : volume (Ô E : Set (𝔸f E)) = volÔ E := by
  let K : TopologicalSpace.PositiveCompacts (𝔸f E) :=
    ⟨⟨Ô E, isCompact_Ô⟩, by simp [isOpen_Ô.interior_eq]⟩
  -- unfold the instance that defines `volume`
  change (volÔ E • addHaarMeasure K) (K : Set (𝔸f E)) = volÔ E
  simp [addHaarMeasure_self]

/-! ### The finite character, and further instances -/

/-- On an element `a` of `E` the finite character `ψf` takes the value `exp (2πi Tr_{E/ℚ} a)`. -/
lemma ψf_coe (a : E) : ψf E a = 𝐞 (trace ℚ E a) := by
  -- `ψf` is defined by descending `𝐞 ∘ tr` along the surjection `π`
  let π : E →+ 𝔸f E ⧸ (Ô E).toAddSubgroup := (mk' _).comp (algebraMap E (𝔸f E) : E →+ 𝔸f E)
  simp only [ψf, AddChar.toAddMonoidHomEquiv_symm_apply, AddMonoidHom.coe_comp, Function.comp_apply]
  exact congrArg Additive.toMul
    (AddMonoidHom.liftOfRightInverse_comp_apply π _ _ _ a)

/-- The finite character `ψf` is trivial on the ring `Ô E` of integral finite adeles. -/
lemma ψf_eq_one_of_mem {x : 𝔸f E} (h : x ∈ Ô E) : ψf E x = 1 := by
  simp [ψf, (eq_zero_iff (N := (Ô E).toAddSubgroup) x).mpr h]

instance : SigmaFinite (volume (α := 𝔸f E)) := inferInstance

deriving instance SecondCountableTopology, T2Space for 𝔸f E, 𝔸 E

deriving instance PolishSpace, LocallyCompactSpace, BorelSpace, IsTopologicalRing,
  MeasurableSingletonClass for 𝔸 E

instance : SigmaFinite (volume (α := 𝔸 E)) := inferInstance

/-- The measure `volume` on `New.𝔸 E` (the adeles, when E is totally complex) is an additive Haar
measure. -/
instance isAddHaarMeasure_𝔸 : IsAddHaarMeasure (volume (α := 𝔸 E)) :=
  prod.instIsAddHaarMeasure volume volume

end New

end AdditiveCharDefs

/-! ## Rational points as a cocompact lattice of covolume one -/

section RationalLattice

open NumberField MeasureTheory InfinitePlace IsTotallyComplex Metric Matrix QuotientAddGroup
open scoped Pointwise

namespace New

/-- A complex embedding `φ` is the chosen embedding `Φ` of its place or the conjugate of it. -/
lemma Φ_mk_eq_or_star_eq {E : Type*} [Field E] [PlaceEmbedding E] (φ : E →+* ℂ) :
    Φ (InfinitePlace.mk φ) = φ ∨ star (Φ (InfinitePlace.mk φ)) = φ :=
  mk_eq_iff.mp (mk_Φ _)

variable (E : Type*) [Field E] [PlaceEmbedding E] [NumberField E] (m n : Type*)
  {B I : Type*} [AddCommGroup B] [AddCommGroup I] [TopologicalSpace B]
  (f : I →+ B) (C : Set B) [MeasureSpace B]

/-! ### Rational points, fundamental domains and lattices -/

/-- The image of E in its adeles under the diagonal embedding, as an additive subgroup. -/
def ratAdeles : AddSubgroup (𝔸 E) := (toAdele (E := E)).toAddMonoidHom.range

/-- The additive subgroup of adelic vectors indexed by n that is the image of E^n under the
coordinatewise diagonal embedding. -/
def ratVectors : AddSubgroup (n → 𝔸 E) := ((toAdele (E := E)).toAddMonoidHom.compLeft n).range

/-- The additive subgroup of m×n adelic matrices that is the image of the m×n matrices over E
under the entrywise diagonal embedding. -/
def ratMatrices : AddSubgroup (Matrix m n (𝔸 E)) :=
  (toAdele (E := E)).toAddMonoidHom.mapMatrix (m := m) (n := n).range

/-- For an additive map `f : I →+ B` and a set `C` in `B`: `C` is compact and contains a measurable
set `D` of volume one such that every `x` in `B` has exactly one `a` in `I` with `f a + x ∈ D`. -/
def HasFundDomain : Prop :=
  IsCompact C ∧ ∃ D ⊆ C, MeasurableSet D ∧ volume D = 1 ∧ ∀ x : B, ∃! a : I, f a + x ∈ D

/-- A lattice of covolume one: a discrete subgroup `Λ` of `B` with `B ⧸ Λ` compact and of quotient
measure one, such that the translates of one compact set by `Λ` cover `B`. -/
class IsCovolOneLattice (Λ : AddSubgroup B) extends DiscreteTopology Λ, CompactSpace (B ⧸ Λ),
  IsProbabilityMeasure Λ.quotMeasure where
  /-- Some compact set meets every coset of `Λ`. -/
  exists_compact_cover (Λ) : Λ.IsCocompact

variable {E m n f C}

lemma mem_ratVectors {x : n → 𝔸 E} : x ∈ ratVectors E n ↔ ∀ i : n, x i ∈ ratAdeles E := by
  simp [ratVectors, ratAdeles, funext_iff, Classical.skolem]

lemma mem_ratMatrices {x : Matrix m n (𝔸 E)} :
    x ∈ ratMatrices E m n ↔ ∀ (i : m) (j : n), x i j ∈ ratAdeles E := by
  simp [ratMatrices, ratAdeles, ← ext_iff, Classical.skolem, of.exists_congr_left]

@[simp, grind .]
lemma toAdele_half_add_half : toAdele (2⁻¹ : E) + toAdele (2⁻¹ : E) = 1 := by
  norm_num [← map_add]

@[grind .]
lemma toAdele_inv_mul_cancel {x : E} (hx : x ≠ 0) : toAdele x⁻¹ * toAdele x = 1 := by
  simp [← map_mul, hx]

variable [IsTotallyComplex E] [Fintype n] [IsTopologicalAddGroup B]
  [SecondCountableTopology B] [T2Space B] [LocallyCompactSpace B]
  [(volume (α := B)).IsAddHaarMeasure]

/-! ### From a fundamental domain to a lattice -/

omit [T2Space B] in
/-- If a compact set `C` contains a fundamental domain of volume one for `f : I →+ B`
(`HasFundDomain f C`), then for a finite index type `n` the power `C^n` contains one for the
coordinatewise map `(n → I) →+ (n → B)`. -/
lemma HasFundDomain.pi (h : HasFundDomain f C) :
    HasFundDomain (f.compLeft n) (Set.pi Set.univ fun _ : n ↦ C) := by
  -- A power of the fundamental domain `D ⊆ C` is a fundamental domain in the power of `C`.
  obtain ⟨hC, D, hDC, hD_meas, hD_vol, h_uniq⟩ := h
  refine ⟨isCompact_univ_pi fun _ ↦ hC, .pi .univ fun _ ↦ D, Set.pi_mono fun _ _ ↦ hDC,
    .univ_pi fun _ ↦ hD_meas, by simp [volume, hD_vol], fun x ↦ ?_⟩
  choose a ha ha_uniq using fun i : n ↦ h_uniq (x i)
  exact ⟨a, fun i _ ↦ ha i, fun b hb ↦ funext fun i ↦ ha_uniq i (b i) (hb i trivial)⟩

/-- Let `f : I →+ B` be additive, `B` a second countable locally compact Hausdorff abelian group
with Haar measure. If the compact set `C` contains a measurable `D` of volume one whose translates
by the `f a` partition `B` (`HasFundDomain f C`), then the image of `f` is a lattice of covolume
one: it is discrete and cocompact, with quotient measure of mass one. -/
lemma HasFundDomain.isCovolOneLattice [BorelSpace B]
    (h : HasFundDomain f C) : IsCovolOneLattice f.range := by
  obtain ⟨hC, D, hDC, hD_meas, hD_vol, h_uniq⟩ := h
  -- Discreteness: `D - D` is a neighbourhood of `0` (Steinhaus) and meets the image only in `0`.
  have h_disc : DiscreteTopology f.range := by
    have h_nhds : D - D ∈ nhds (0 : B) :=
      volume.sub_mem_nhds_zero_of_addHaar_pos D hD_meas (by simp [hD_vol])
    refine discreteTopology_of_isOpen_singleton_zero ((⊥ : AddSubgroup f.range).isOpen_of_mem_nhds
      ((mem_nhds_induced ((↑) : f.range → B) 0 _).2 ⟨D - D, h_nhds, ?_⟩))
    rintro ⟨_, a, rfl⟩ ⟨x, hx, y, hy, hxy : x - y = f a⟩
    have ha_mem : f a + y ∈ D := by rwa [← hxy, sub_add_cancel]
    simp [(h_uniq y).unique ha_mem (show f 0 + y ∈ D by simpa)]
  -- Every point is moved into `C` by the image; hence the quotient is the image of `C`.
  have h_cover (x : B) : ∃ γ ∈ f.range, γ + x ∈ C := by
    simpa using (h_uniq x).exists.imp fun a ha ↦ hDC ha
  have h_cpt : CompactSpace (B ⧸ f.range) := by
    have h_image : ((↑) : B → B ⧸ f.range) '' C = Set.univ := top_unique fun q _ ↦
      let ⟨γ, hγ, h_mem⟩ := h_cover q.out
      ⟨γ + q.out, h_mem, by simp [hγ]⟩
    rw [← isCompact_univ_iff, ← h_image]
    exact hC.image continuous_mk
  -- Each orbit meets `D` exactly once.
  have h_once (x : B) : ∫⁻ γ : f.range, D.indicator 1 (γ +ᵥ x) ∂.count = 1 := by
    obtain ⟨a, ha, ha_uniq⟩ := h_uniq x
    rw [lintegral_count, tsum_eq_single ⟨f a, a, rfl⟩]
    · simp [f.range.vadd_def, ha]
    · rintro ⟨_, b, rfl⟩ hb
      exact Set.indicator_of_notMem (fun h_mem ↦ hb (by simp [ha_uniq b h_mem])) _
  -- Unfolding the integral of the indicator of `D`: the quotient has the volume of `D`.
  have h_mass : f.range.quotMeasure volume Set.univ = 1 := by
    simpa [h_once, hD_meas, hD_vol] using
      lintegral_addOrbitMeasure_lintegral (ν := .count) (H := f.range) (μ := volume)
        (measurable_one.indicator hD_meas)
  exact
    { toDiscreteTopology := h_disc, toCompactSpace := h_cpt,
      toIsProbabilityMeasure := ⟨h_mass⟩, exists_compact_cover := ⟨C, hC, h_cover⟩ }

/-! ### The rational points of the adeles and finiteness in compact sets -/

open scoped Classical in
/-- Let `E` be a totally complex number field, with a chosen complex embedding `Φ v` for each
infinite place `v`. Some volume-preserving ℝ-linear isomorphism from the Minkowski space of `E` to
`InfinitePlace E → ℂ` sends the Minkowski embedding of each `x : E` to the family `(Φ v x)_v`. -/
lemma exists_mixedEquiv :
    ∃ e : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] (InfinitePlace E → ℂ),
      MeasurePreserving e ∧ ∀ x : E, e (mixedEmbedding E x) = fun v : InfinitePlace E ↦ Φ v x := by
  -- There is no real place, so Minkowski space is its complex factor (`e₀`), and all places are
  -- complex (`e₁`). At each place apply the identity or complex conjugation, to turn Mathlib's
  -- embedding `v.embedding` into `Φ v` (`e₂`).
  have h_no_real : IsEmpty {v : InfinitePlace E // v.IsReal} := ⟨by simp [isComplex]⟩
  let σ (v : InfinitePlace E) : ℂ ≃ₗᵢ[ℝ] ℂ := if v.embedding = Φ v then 1 else Complex.conjLIE
  let ι : {v : InfinitePlace E // v.IsComplex} ≃ InfinitePlace E := .subtypeUnivEquiv isComplex
  let e₀ : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] ({v : InfinitePlace E // v.IsComplex} → ℂ) :=
    .uniqueProd
  let e₁ : ({v : InfinitePlace E // v.IsComplex} → ℂ) ≃ₗ[ℝ] (InfinitePlace E → ℂ) :=
    .funCongrLeft ℝ ℂ ι.symm
  let e₂ : (InfinitePlace E → ℂ) ≃ₗ[ℝ] (InfinitePlace E → ℂ) :=
    .piCongrRight fun v ↦ (σ v).toLinearEquiv
  have h_e₀ : MeasurePreserving e₀ := by
    change MeasurePreserving
      (Prod.snd : mixedEmbedding.mixedSpace E → ({v : InfinitePlace E // v.IsComplex} → ℂ))
    exact ⟨measurable_snd, by simp [volume]⟩
  have h_e₁ : MeasurePreserving e₁ := volume_preserving_arrowCongr' ι (.refl ℂ) (.id _)
  have h_e₂ : MeasurePreserving e₂ := volume_preserving_pi fun v ↦ (σ v).measurePreserving
  have h_σ (v : InfinitePlace E) (x : E) : σ v (v.embedding x) = Φ v x := by
    by_cases hv : v.embedding = Φ v
    · simp [σ, hv]
    · have h_conj : v.embedding = ComplexEmbedding.conjugate (Φ v) := by
        simpa [mk_Φ, hv] using embedding_mk_eq (Φ v)
      simp [σ, ite_eq_right hv, h_conj]
  exact ⟨e₀ ≪≫ₗ e₁ ≪≫ₗ e₂, h_e₂.comp (h_e₁.comp h_e₀), fun x ↦ funext fun v ↦ h_σ v x⟩

open scoped Classical in
/-- Let `K` be a number field and `φ : K → V` a ring homomorphism. Let `e` be a volume-preserving
ℝ-linear isomorphism from the Minkowski space of `K` to `V` that turns the Minkowski embedding into
`φ`. Then for some `R > 0` the closed ball of radius `R` in `V` times the integral finite adeles
`Ô K` is compact and contains a fundamental domain of volume one (`New.HasFundDomain`) for the map
`K → V × 𝔸f K` given by `φ` and the diagonal embedding into the finite adeles. -/
lemma exists_hasFundDomain {K V : Type*} [NormedRing V] [NormedSpace ℝ V] [ProperSpace V]
    [MeasureSpace V] [BorelSpace V] [Field K] [NumberField K] (φ : K →+* V)
    (e : mixedEmbedding.mixedSpace K ≃ₗ[ℝ] V) (he : MeasurePreserving e)
    (h_emb : ∀ a : K, e (mixedEmbedding K a) = φ a) :
    ∃ R > (0 : ℝ), HasFundDomain (φ.prod (algebraMap K (𝔸f K))).toAddMonoidHom
      (closedBall (0 : V) R ×ˢ Ô K) := by
  -- `exists_fundDomain_prod` for the unit ideal gives a bounded `F` of volume `2 ^ (-r₂) √|disc K|`
  -- with `F ×ˢ Ô K` a fundamental domain.
  have h_integral (a : K) : algebraMap K (𝔸f K) a ∈ Ô K ↔
      a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    simp [IsIntegralClosure.isIntegral_iff (A := 𝓞 K)]
  obtain ⟨F, h_meas, h_bounded, h_vol, h_unique⟩ :
      ∃ F : Set V, MeasurableSet F ∧ Bornology.IsBounded F ∧
        volume F = ENNReal.ofReal (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K).absNorm *
          (2⁻¹ ^ nrComplexPlaces K * ‖NumberField.discr K‖₊.sqrt) ∧
        ∀ x : V × 𝔸f K, ∃! a : K, (φ a, algebraMap K (𝔸f K) a) + x ∈ F ×ˢ (Ô K : Set (𝔸f K)) :=
    exists_fundDomain_prod (φ.prod (algebraMap K (𝔸f K))).toAddMonoidHom (Ô K).toAddSubgroup 1
      h_integral exists_sub_mem_Ô e he h_emb
  obtain ⟨R, hR, h_ball⟩ := h_bounded.subset_closedBall_lt 0 0
  refine ⟨R, hR, (isCompact_closedBall 0 R).prod isCompact_Ô, F ×ˢ Ô K, Set.prod_mono_left h_ball,
    h_meas.prod isOpen_Ô.measurableSet, ?_, h_unique⟩
  -- The mass `volÔ` of `Ô K` is the inverse of the volume of `F`.
  show volume (F ×ˢ (Ô K : Set (𝔸f K))) = 1
  rw [Measure.volume_eq_prod, Measure.prod_prod, h_vol, volume_Ô]
  simp [← ENNReal.toReal_eq_one_iff, volÔ, field, discr_ne_zero]

open scoped Classical in
/-- Let `E` be a totally complex number field with chosen embeddings at the infinite places. For
some `R > 0`, the closed ball of radius `R` in the infinite part `InfinitePlace E → ℂ` times the
integral finite adeles `Ô E` is compact and contains a fundamental domain of volume one
(`HasFundDomain`) for `E` acting on its adeles through the diagonal embedding `toAdele`. -/
lemma exists_hasFundDomain_toAdele :
    ∃ R > (0 : ℝ), HasFundDomain (toAdele : E →+* 𝔸 E).toAddMonoidHom
      (closedBall (0 : InfinitePlace E → ℂ) R ×ˢ Ô E) := by
  let ⟨e, he, h_emb⟩ := exists_mixedEquiv (E := E)
  exact exists_hasFundDomain (RingHom.pi Φ : E →+* (InfinitePlace E → ℂ)) e he h_emb

/-- For totally complex `E` the rational points `New.ratAdeles E` form a lattice of covolume one in
the adeles of `E`: a discrete subgroup whose compact quotient has measure one. -/
instance isCovolOneLattice_ratAdeles : IsCovolOneLattice (ratAdeles E) := by
  obtain ⟨R, -, h_dom⟩ := exists_hasFundDomain_toAdele (E := E)
  exact h_dom.isCovolOneLattice

/-- For totally complex `E` and finite `n` the rational vectors `New.ratVectors E n` form a lattice
of covolume one in the adelic vectors indexed by `n`. -/
instance isCovolOneLattice_ratVectors : IsCovolOneLattice (ratVectors E n) := by
  obtain ⟨R, -, h_dom⟩ := exists_hasFundDomain_toAdele (E := E)
  exact h_dom.pi.isCovolOneLattice

/-- For totally complex `E` and finite `m`, `n` the rational matrices `New.ratMatrices E m n` form
a lattice of covolume one in the adelic `m × n` matrices. -/
instance isCovolOneLattice_ratMatrices [Fintype m] : IsCovolOneLattice (ratMatrices E m n) := by
  obtain ⟨R, -, h_dom⟩ := exists_hasFundDomain_toAdele (E := E)
  -- a matrix is by definition a family of rows, so the power is taken twice
  exact h_dom.pi.pi.isCovolOneLattice

/-- An injective additive map `f` into a Hausdorff topological group, with discrete image, sends
only finitely many points into a given compact set. -/
lemma finite_preimage_of_discreteTopology_range {B I : Type*} [AddCommGroup B] [AddCommGroup I]
    [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B] {f : I →+ B} {C : Set B}
    (hf_inj : Function.Injective f) (h_disc : DiscreteTopology f.range) (hC : IsCompact C) :
    (f ⁻¹' C).Finite := by
  -- `f` tends to infinity along the cofinite filter
  simpa using f.tendsto_coe_cofinite_of_isDiscrete hf_inj ⟨h_disc⟩ hC.compl_mem_cocompact

omit [SecondCountableTopology B] [LocallyCompactSpace B] [(volume (α := B)).IsAddHaarMeasure] in
/-- Let `f : I →+ B` be an injective additive map whose image is a lattice of covolume one in `B`
(discrete, with compact quotient of measure one). Then for every compact set `C`, only finitely many
`a` in `I` have `f a ∈ C`. -/
lemma IsCovolOneLattice.finite_preimage (h : IsCovolOneLattice f.range)
    (hf_inj : Function.Injective f) (hC : IsCompact C) : (f ⁻¹' C).Finite :=
  finite_preimage_of_discreteTopology_range hf_inj h.toDiscreteTopology hC

/-- For totally complex `E`, a compact set of adeles contains the diagonal images of only finitely
many elements of `E`. -/
lemma finite_setOf_toAdele_mem {K : Set (𝔸 E)} (hK : IsCompact K) :
    {x : E | toAdele x ∈ K}.Finite :=
  (isCovolOneLattice_ratAdeles (E := E)).finite_preimage (toAdele (E := E)).injective hK

/-- For totally complex `E` and finite `n`, a compact set of adelic vectors indexed by `n` contains
the coordinatewise diagonal images of only finitely many vectors over `E`. -/
lemma isCovolOneLattice_ratVectors.finite_preimage {K : Set (n → 𝔸 E)} (hK : IsCompact K) :
    {ξ : n → E | toAdele ∘ ξ ∈ K}.Finite :=
  IsCovolOneLattice.finite_preimage (isCovolOneLattice_ratVectors (E := E) (n := n))
    (toAdele (E := E)).injective.comp_left hK

/-- For totally complex `E` and finite `m`, `n`, a compact set of adelic `m × n` matrices contains
the entrywise diagonal images of only finitely many matrices over `E`. -/
lemma finite_setOf_map_toAdele_mem [Fintype m] {K : Set (Matrix m n (𝔸 E))} (hK : IsCompact K) :
    {A : Matrix m n E | A.map toAdele ∈ K}.Finite :=
  (isCovolOneLattice_ratMatrices (E := E) (m := m) (n := n)).finite_preimage
    (Matrix.map_injective (toAdele (E := E)).injective) hK

variable [StarAddMonoid B] [ContinuousStar B]

instance : IsClosed (X := B) (selfAdjoint B) := isClosed_fixedPoints continuous_star

end New

end RationalLattice

end
