import New.Spanning.Frames.TopCorrelation
import New.Spanning.MainTerm.FillingLevel
import New.Spanning.MainTerm.KloostermanSum
import New.Spanning.Unfolding.AmplitudeSums

/-!
# Class sums as orbit sums, and unfolding at a set of primes

This file links the global sums of the filling argument to the local theory at a finite set `T` of
finite places, stable under conjugation. A finite adelic point is studied through its projection
`New.Filling.toPlaces` to `T` and the condition `New.Filling.IsIntegralOff` of being integral off
`T`. This file writes a class sum as a finite sum of orbit sums over the terms in the big cell. It
compares levels, moduli and characters with those at `T`, and it counts images modulo `M` by
measures. It unfolds each orbit sum to a Kloosterman sum at `T` times an orbital integral at
infinity.

With `h_c` the representative `New.Filling.classRep c` of the class `c`,
`New.Filling.translateByClassReps c c' γ` is `h_c⁻¹ γ h_c'`, `New.Filling.termsOver c s c'` the set
of rational `γ` for which it is integral of reduction `s` modulo `M`, and
`New.Floors.FloorGroups.weylElem ϱ p` the Weyl element `w_p`. `New.Filling.boundedNonzeroIntegers`
is the finite set of bounded nonzero integers that contains the nonzero leading minors of
contributing terms. `New.Filling.entrySet` is the set 𝒯 of quotients of two of its elements. The
number `New.Filling.termDisc γ` is formed from the last two leading minors of the frame products of
`γ`.

## Main definitions and results

* `New.Filling.exists_amplitudeSum_eq_sum_cosetAmplitude`: a class sum for the cut function is a
  finite sum over the heads with entries in the finite set `New.Filling.entrySet`. Let these entries
  be units off `T` and let all terms over `(c, s, c')` lie in the big cell. If the terms with
  `termDisc γ ≠ 0` and one link have a nonzero sum, those that contribute lie in the double cosets
  of the `w_p σ` for one `σ`. These cosets carry the orbit sums `New.Filling.cosetAmplitude`, over
  the `u γ u'⁻¹` with `u`, `u'` in the unipotent group `New.Shape.Form.besselU`.
* `New.Filling.IsFillingData.card_reducedImage_mul_measure_congruenceSubgroup_eq`: let `B` be a
  subgroup of the finite adelic group and `μ` an s-finite measure at `T`, carried by the projections
  of elements of `B` integral off `T` and right invariant under the projections of `B`. Then the
  order of the image of `B ∩ K` modulo `M` times `μ K(M)` is the `μ`-measure of the integral points.
* `New.Filling.IsFillingData.cosetAmplitude_eq_kloostermanSum_smul`: for `γ = w_p σ` with
  `σ ∈ floorGroup ϱ`, and with `h_c⁻¹ γ h_c'` and the inverses of the entries of `p` integral off
  `T`, the orbit sum is a Kloosterman sum at `T` times an orbital integral at infinity. Each double
  coset unfolds to one integral, the double cosets correspond to the pairs in the Kloosterman sum,
  and the values of the extended Bessel character are its terms.
* `New.Filling.IsFillingData.scaledOrbitalIntegral_smul_eq_cosetAmplitude`: so the orbit sum times
  `headDensity` and the mass of `K(M)` is an entry of the integral at `T` times the integral at
  infinity.

Notions from other files:
* `New.Filling.latticeStabilizer`, `New.Filling.principalLevel`: The group `K` of integral points of
  the finite adelic unitary group, and the kernel `K(M)` of its reduction modulo `M`;
  `New.Floors.PlaceData.congruenceSubgroup` is the group `K(M)` at `T`.
* `New.Filling.amplitude`: The integral of β_c(y) β_c'(γ⁻¹y) W(y) ⊗ W(γ⁻¹y)^* over the infinite
  points y, with β_c the cutoff `New.Filling.classCutoff` and W the full or the cut Bessel function
  at infinity, according to the argument `side`.
* `New.Floors.IntegralPlace.extendedBesselChar`: The finite Bessel function, a character of u on u
  K(M) for u in 𝖴 = `New.Shape.Form.besselU`, and 0 off 𝖴 K(M).
* `New.Filling.IsFillingData` (in `New.Spanning.MainTerm.FillingLevel`): the place data at `T` is
  large lattice data for the chosen place structure, with modulus the component of `M` at `T`.
* `New.Filling.cosetAmplitude` (in `New.Spanning.MainTerm.FillingLevel`): the sum of the amplitudes
  of the `u γ u'⁻¹` over the pairs of rational points of 𝖴 for which it is a term over `(c, s, c')`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Filling

open NumberField MeasureTheory Matrix ENNReal Fintype Floors FloorGroups Function
  ComplexOrder SemilocalField Measure Filter Complex Set

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape}

variable {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable] {x : S.GFin}

/-! ### Terms in the big cell and class sums -/

section

/-- For classes `c`, `c'`, the translate `translateByClassReps c c'` (h_c⁻¹ γ h_c') of
`u⁻¹ * γ * u'` equals the inverse of the translate of `u` by `c, c`, times the translate of `γ` by
`c, c'`, times the translate of `u'` by `c', c'`. -/
lemma translateByClassReps_inv_mul_mul (c c' : S.Classes) (u γ u' : S.G E) :
    S.translateByClassReps c c' (u⁻¹ * γ * u') =
      (S.translateByClassReps c c u)⁻¹ * S.translateByClassReps c c' γ *
        S.translateByClassReps c' c' u' := by
  simp [translateByClassReps, mul_assoc]

/-- If `σ` fixes the vectors `e_a`, `e*_a` of the `ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`), so does
its translate `h_c⁻¹ σ h_c'` by class representatives. -/
lemma translateByClassReps_mem_floorGroup {σ : S.G E} (hσ : σ ∈ floorGroup 𝔰.ϱ) (c c' : S.Classes) :
    S.translateByClassReps c c' σ ∈ floorGroup 𝔰.ϱ := by
  simp [mem_floorGroup, Sum.forall, apply_eq_one_apply_of_mem_floorGroup hσ,
    coe_translateByClassReps, classBasis, toBesselH,
    besselLatticeBasis, mul_apply, Matrix.one_apply]

/-- Let `σ` fix the vectors `e_a`, `e*_a` of the `ϱ = 𝔰.ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`). Let
`L = h_c⁻¹ σ h_c'` be its translate by the representatives of the classes `c`, `c'`, and let `z` be
the last frame vector, of index `𝔰.top`. Then `L z = orbitPoint 𝔰.top L⁻¹` is the vector
`c.out⁻¹ ω - (t / N) z` in the lattice basis, where `N = π π̄` with `π = S.piN`. Here
`t = h(z, σ z)` is the last diagonal entry of `S.frameProducts σ`, `ω` holds the coordinates of
`σ z` at the basis vectors `𝔰.indexX₀ j` of `X₀`, and `c.out ∈ U(X₀)` is the chosen representative
of `c`. -/
lemma orbitPoint_top_translateByClassReps_inv {σ : S.G E} (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (c c' : S.Classes) :
    orbitPoint 𝔰.top (S.translateByClassReps c c' σ)⁻¹ =
      vectorOfLastEntry S.piN (algebraMap E (𝔸f E) (S.frameProducts σ 𝔰.top 𝔰.top))
        (c.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ fun j : 𝔰.κ ↦ σ.val.val (𝔰.indexX₀ j) 𝔰.z) := by
  -- The change of basis on the right fixes `z`, so the column of `σ` at `z` remains.
  have h_fix : (classBasis c').val *ᵥ Pi.single 𝔰.z 1 = Pi.single 𝔰.z 1 := by
    simp [funext_iff, Sum.forall, classBasis, toBesselH, besselLatticeBasis, mul_apply]
  have h_column : orbitPoint 𝔰.top (S.translateByClassReps c c' σ)⁻¹ =
      S.latticeBasis⁻¹.val *ᵥ
        fromBlocks 1 0 0 (fromBlocks (fromBlocks c.out⁻¹.val.val 0 0 1) 0 0 1) *ᵥ
        fun i : 𝔰.BesselIndex ↦ algebraMap E (𝔸f E) (σ.val.val i 𝔰.z) := by
    have h_map : σ.val.val.map (algebraMap E (𝔸f E)) *ᵥ Pi.single 𝔰.z 1 =
        fun i : 𝔰.BesselIndex ↦ algebraMap E (𝔸f E) (σ.val.val i 𝔰.z) := mulVec_single_one _ 𝔰.z
    rw [← h_map, ← h_fix]
    simp [orbitPoint, coe_translateByClassReps, classBasis, toBesselH, ← mulVec_mulVec,
      -mulVec_single]
  rw [h_column, vectorOfLastEntry]
  -- Both sides are the inverse of the lattice basis applied to a vector; compare the vectors.
  congr 1
  simp [funext_iff, Sum.forall, frameGram, splitGram, middleGram, mulVec, ← piN_mul_star,
    ← mul_assoc, ← star_mul, apply_eq_one_apply_of_mem_floorGroup hσ, dotProduct, mul_apply]

/-- The norm equation. Let `σ` be an isometry of the hermitian form `h` over `E`, and let it fix the
vectors `e_a`, `e*_a` of the `ϱ = 𝔰.ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`). Let `z` be the basis
vector `𝔰.z`, the last frame vector (index `𝔰.top`), with `h(z, z) = -N` for the prime `N = S.N`.
Then `N ω̄ · ω = t t̄ - N²`, where `ω` holds the coordinates of `σ z` in the basis of `X₀` indexed
by `𝔰.κ` and `t = h(z, σ z)` is the last diagonal entry of `S.frameProducts σ`. -/
lemma mul_star_dotProduct_eq_last_frameProducts {σ : S.G E} (hσ : σ ∈ floorGroup 𝔰.ϱ) :
    S.N * star (fun j : 𝔰.κ ↦ σ.val.val (𝔰.indexX₀ j) 𝔰.z) ⬝ᵥ
        (fun j : 𝔰.κ ↦ σ.val.val (𝔰.indexX₀ j) 𝔰.z) =
      S.frameProducts σ 𝔰.top 𝔰.top * star (S.frameProducts σ 𝔰.top 𝔰.top) - S.N ^ 2 := by
  -- With `a` the coordinate of `σ z` at `z`, we have `t = -N a` and
  -- `-N = h(σ z, σ z) = ω̄ · ω - N a ā`.
  let ω : 𝔰.κ → E := fun j ↦ σ.val.val (𝔰.indexX₀ j) 𝔰.z
  let a : E := σ.val.val 𝔰.z 𝔰.z
  have h_last : S.frameProducts σ 𝔰.top 𝔰.top = -(S.N * a) := by
    simp [a, frameGram, middleGram, splitGram, mul_apply]
  have h_form : (σ.val.valᴴ * (S.ratMiddle E).splitGram * σ.val.val) 𝔰.z 𝔰.z =
      (S.ratMiddle E).splitGram 𝔰.z 𝔰.z := by rw [mem_U.1 σ.prop]
  have h_norm : star ω ⬝ᵥ ω + -(star a * S.N * a) = -S.N := by
    simpa [apply_eq_one_apply_of_mem_floorGroup hσ, middleGram, splitGram, mul_apply, dotProduct,
      Matrix.one_apply]
      using h_form
  rw [h_last, star_neg, star_mul', star_natCast]
  linear_combination S.N * h_norm

/-- Weyl elements move to the left of the translate: `h_c⁻¹ (w_p σ) h_c' = w_p (h_c⁻¹ σ h_c')`, with
the entries `p` read in the finite adeles on the right. -/
lemma translateByClassReps_weylElem_mul (c c' : S.Classes) (p : ℕ → Eˣ) (σ : S.G E) :
    S.translateByClassReps c c' (weylElem 𝔰.ϱ p * σ) =
      weylElem 𝔰.ϱ (Units.map (algebraMap E (𝔸f E)) ∘ p) * S.translateByClassReps c c' σ := by
  -- No `e*_a` has level below `ϱ`.
  have h_level (a : Fin 𝔰.ϱ) : ¬2 * 𝔰.ϱ - a < 𝔰.ϱ := by lia
  -- The Weyl element commutes with the change of basis, entry by entry.
  simp +contextual [Subtype.ext_iff, ← mul_assoc, Units.ext_iff, ← ext_iff, Sum.forall, weylElem,
    weylOn, coe_translateByClassReps, classBasis, toBesselH, besselLatticeBasis,
      fromBlocks_multiply,
    fromCols_mul_fromBlocks, mul_apply, Matrix.one_apply, BesselIndex.level, h_level,
    apply_ite (algebraMap E (𝔸f E))]

end

/-- Let `S` satisfy the standing hypotheses `New.Filling.IsAdmissible`. Let `γ` be a term over
`(c, s, c')` (`termsOver`). Suppose that its amplitude for the cut Bessel function W♭, the integral
of `W♭(y) ⊗ W♭(γ⁻¹ y)^*` against the cutoffs of `c`, `c'` over the points `y` at infinity, is
nonzero. Then each nonzero leading minor `δ` of the matrix `S.frameProducts γ = (h(f_j, γ f_l))` of
products of the frame `f` with its image lies in `S.boundedNonzeroIntegers`: it is an integer of `E`
with `‖δ‖ ^ 2 ≤ b ^ (270 n ^ 2)` at every infinite place. Here `b = S.b` is the size parameter of
`S` and `n = 𝔰.n = ϱ + 1`. -/
lemma leadingMinor_mem_boundedNonzeroIntegers [WeilData E]
    [S.IsAdmissible] {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') (h_amp : S.amplitude .cut c c' γ ≠ 0) {l : Fin (𝔰.n + 1)}
    (h_ne : leadingMinor (S.frameProducts γ) l ≠ 0) :
    leadingMinor (S.frameProducts γ) l ∈ S.boundedNonzeroIntegers := by
  refine ⟨h_ne, IsIntegral.det fun _ _ ↦ isIntegral_frameProducts hγ _ _, fun v ↦ ?_⟩
  -- At some point `y` both `W♭(y)` and `W♭(γ⁻¹ y)` are nonzero. Unipotent translates of the two
  -- points lie in the boxes, and they do not change the minors.
  obtain ⟨y, hy⟩ : ∃ y : InfinitePlace E → 𝔰.G₁, S.besselKernel .cut γ y ≠ 0 := by
    by_contra! h_zero
    exact h_amp (by simp [amplitude, h_zero])
  have h_cut {z : InfinitePlace E → 𝔰.G₁} {i : S.BesselCoord} (hz : S.besselFn .cut z i ≠ 0)
      (w : InfinitePlace E) : InCut (z w) S.b :=
    (S.besselSystem w).isCutPair.inCut_of_ne_zero _ fun h_zero ↦
      hz (Finset.prod_eq_zero (Finset.mem_univ w) (by simp [h_zero]))
  obtain ⟨i, hi⟩ : ∃ i : S.BesselCoord × S.BesselCoord, S.besselKernel .cut γ y i ≠ 0 := by
    by_contra! h_zero
    exact hy (PiLp.ext h_zero)
  obtain ⟨u, hu, hu_box⟩ : ∃ u ∈ S.classUnipotent c, S.ratToInf u * y ∈ S.boxedPoints :=
    exists_classUnipotent_mul_mem_boxedPoints c (h_cut (left_ne_zero_of_mul hi))
  obtain ⟨u', hu', hu'_box⟩ :
      ∃ u' ∈ S.classUnipotent c', S.ratToInf u' * ((S.ratToInf γ)⁻¹ * y) ∈ S.boxedPoints :=
    exists_classUnipotent_mul_mem_boxedPoints c' (h_cut (star_ne_zero.1 (right_ne_zero_of_mul hi)))
  have h_near : S.IsNear (u * γ * u'⁻¹) :=
    ⟨S.ratToInf u * y, hu_box, by simpa [mul_assoc] using hu'_box⟩
  rw [← leadingMinor_frameGram_besselU_mul (inv_mem hu.1) (inv_mem hu'.1), inv_inv]
  exact h_near.norm_map_leadingMinor_sq_le _ _

/-- Let `S` satisfy the standing hypotheses `New.Filling.IsAdmissible`. Let `u`, `u'` be rational
points of the group 𝖴 = `besselU` of block upper unitriangular isometries. Let `σ` fix the vectors
`e_a`, `e*_a` of the `ϱ = 𝔰.ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`). Let `p ϱ = h(z, σ z)` be the
last diagonal entry of `S.frameProducts σ`. Write `w_p` for the Weyl element `weylElem 𝔰.ϱ p`. Let
`γ = u⁻¹ (w_p σ) u'` be a term over `(c, s, c')` (`S.termsOver c s c'`): `h_c⁻¹ γ h_c'` lies in `K`
and has reduction `s`. Suppose that its amplitude `S.amplitude .cut c c' γ` for the cut Bessel
function W♭ is nonzero. Then for every `a ≤ ϱ` the entry `p a` lies in 𝒯 = `S.entrySet`, the finite
set of quotients of two elements of `S.boundedNonzeroIntegers`. -/
lemma entry_mem_entrySet [WeilData E]
    [S.IsAdmissible] {c c' : S.Classes} {s : S.ResidueGL} {u u' σ : S.G E}
    {p : ℕ → Eˣ} (hu : u ∈ besselU) (hu' : u' ∈ besselU) (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hθ : S.frameProducts σ 𝔰.top 𝔰.top = p 𝔰.ϱ)
    (hγ : u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u' ∈ S.termsOver c s c')
    (h_amp : S.amplitude .cut c c' (u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u') ≠ 0)
    {a : ℕ} (ha : a ≤ 𝔰.ϱ) : p a ∈ S.entrySet := by
  -- The minors are the products of the first entries, and `p a` is a quotient of two of them.
  have h_prod (l : Fin (𝔰.n + 1)) : ∏ j ∈ Finset.range l, (p j).val ∈ S.boundedNonzeroIntegers := by
    have h_minor : leadingMinor (S.frameProducts (u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u')) l =
        ∏ j ∈ Finset.range l, (p j).val :=
      (leadingMinor_frameGram_besselU_mul hu hu' l).trans
        (leadingMinor_weylElem_mul_of_last_entry hσ hθ l)
    rw [← h_minor]
    exact leadingMinor_mem_boundedNonzeroIntegers hγ h_amp
      (by simp [h_minor, Finset.prod_eq_zero_iff])
  refine (Finite.mem_toFinset _).2 ⟨_, h_prod ⟨a + 1, by lia⟩, _, h_prod ⟨a, by lia⟩, ?_⟩
  rw [Finset.prod_range_succ, mul_div_cancel_left₀ _ (by simp [Finset.prod_eq_zero_iff])]

/-- For a star-stable set of places `T`, `integralOff T` is closed under `star`. -/
instance isStarStable_integralOff : IsStarStable (integralOff T) where
  star_mem {a} ha := by
    rw [← sub_adeleOfLocal_mem_iff T] at ha ⊢
    rw [← star_evalPlaces, adeleOfLocal_star, ← star_sub]
    exact star_mem_Ô ha

section

/-- Let `T` be a finite set of finite places, stable under conjugation; integral off `T` means
integral at every finite place outside `T`. Let `u`, `u'` be rational points of the unipotent group
`besselU`. Let `σ` fix the vectors `e_a`, `e*_a` of the `ϱ = 𝔰.ϱ` hyperbolic pairs
(`floorGroup 𝔰.ϱ`). Let the inverses of the entries `p a`, `a < ϱ`, be integral off `T`. Suppose
`γ = u⁻¹ (w_p σ) u'` is a term over `(c, s, c')` (`S.termsOver c s c'`): `h_c⁻¹ γ h_c'` lies in `K`
and has reduction `s`. Then the translates `h_c⁻¹ u h_c` and `h_c⁻¹ σ h_c'` (`translateByClassReps`)
are integral off `T`. -/
lemma isIntegralOff_of_mem_termsOver {c c' : S.Classes} {s : S.ResidueGL} {u u' σ : S.G E}
    {p : ℕ → Eˣ} (hu : u ∈ besselU) (hu' : u' ∈ besselU) (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hp : ∀ a : Fin 𝔰.ϱ, (p a)⁻¹.val ∈ ratIntegralOff T)
    (hγ : u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u' ∈ S.termsOver c s c') :
    S.IsIntegralOff T (S.translateByClassReps c c u) ∧
      S.IsIntegralOff T (S.translateByClassReps c c' σ) := by
  obtain ⟨k, -, hk⟩ : ∃ k : S.latticeStabilizer, S.reduction k = s ∧
      k.val = S.translateByClassReps c c' (u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u') := hγ
  have h_int : S.IsIntegralOff T k.val := (mem_latticeStabilizer_iff.1 k.prop).1
  rw [hk, translateByClassReps_inv_mul_mul, translateByClassReps_weylElem_mul] at h_int
  obtain ⟨h_left, h_mid, -⟩ := big_cell_factors_mem_intGL S.isUnimodular_latticeMiddle.splitGram
    (hu.translateByClassReps_mem_besselU c) (hu'.translateByClassReps_mem_besselU c')
    (translateByClassReps_mem_floorGroup hσ c c') hp h_int
  exact ⟨h_left, h_mid⟩

/-- Suppose the entries `p a`, `a < ϱ`, and their inverses are integral off `T`, and `h_c⁻¹ σ h_c'`
(`translateByClassReps c c' σ`) is integral off `T`. Then so is `h_c⁻¹ (w_p σ) h_c'`, where
`w_p = weylElem 𝔰.ϱ p`. -/
lemma isIntegralOff_weylElem_mul {c c' : S.Classes} {σ : S.G E} {p : ℕ → Eˣ}
    (hp : ∀ a < 𝔰.ϱ, (p a).val ∈ ratIntegralOff T ∧ (p a)⁻¹.val ∈ ratIntegralOff T)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' σ)) :
    S.IsIntegralOff T (S.translateByClassReps c c' (weylElem 𝔰.ϱ p * σ)) := by
  rw [translateByClassReps_weylElem_mul]
  refine mul_mem (weylOn_mem_intGL S.isUnimodular_latticeMiddle.splitGram fun a ha ↦ ?_) h_off
  rw [Ring.inverse_unit]
  exact hp a ha

variable (S T) in
/-- The properties of the element `σ` that names the link `Λ` over `(c, s, c')`: it fixes the
hyperbolic planes, the last diagonal entry `t` of its frame products lies in 𝒯 with `t t̄ - N²`
totally positive, and its translate is integral off `T`. The element `k` is a lift of `s`. -/
structure NamesLink (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes)
    (Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)) (t : Eˣ) (σ : S.G E)
    (k : S.latticeStabilizer) : Prop where
  /-- `σ` fixes the hyperbolic planes. -/
  mem_floorGroup : σ ∈ floorGroup 𝔰.ϱ
  /-- `t` is the last diagonal entry of the frame products of `σ`. -/
  frameProducts_top_top : S.frameProducts σ 𝔰.top 𝔰.top = t
  /-- `t t̄ - N²` is totally positive. -/
  sq_lt_norm_sq (v : InfinitePlace E) : S.N ^ 2 < ‖Φ v t.1‖ ^ 2
  /-- `k` reduces to `s`. -/
  reduction_eq : S.reduction k = s
  /-- `Λ` is the link of `w_1 σ`, which is that of `w_p σ` for every head `p`. -/
  link_eq : Λ = link (weylElem 𝔰.ϱ 1 * σ)
  /-- The last entry lies in 𝒯. -/
  mem_entrySet : t ∈ S.entrySet
  /-- The translate `h_c⁻¹ σ h_c'` is integral off `T`. -/
  isIntegralOff : S.IsIntegralOff T (S.translateByClassReps c c' σ)

/-- Let `σ` fix the vectors `e_a`, `e*_a` of the `ϱ = 𝔰.ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`), and
let `θ = h(z, σ z)` be the last diagonal entry of the matrix `S.frameProducts σ` of products of the
frame with its image under `σ`. Let `N = S.N` be the prime with `h(z, z) = -N`. If `θ θ̄ ≠ N²`, then
`N² < |θ|²` at every infinite place `v`, read through its chosen embedding `Φ v`. -/
lemma sq_lt_norm_sq_last_frameProducts {σ : S.G E} (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hθ : S.frameProducts σ 𝔰.top 𝔰.top * star (S.frameProducts σ 𝔰.top 𝔰.top) - S.N ^ 2 ≠ 0)
    (v : InfinitePlace E) :
    S.N ^ 2 < ‖Φ v (S.frameProducts σ 𝔰.top 𝔰.top)‖ ^ 2 := by
  let θ : E := S.frameProducts σ 𝔰.top 𝔰.top
  let ω : 𝔰.κ → E := fun j ↦ σ.val.val (𝔰.indexX₀ j) 𝔰.z
  -- The difference equals `N ω̄ · ω`, so it is nonnegative, hence positive, at each infinite place.
  have h_norm : S.N * star ω ⬝ᵥ ω = θ * star θ - S.N ^ 2 :=
    mul_star_dotProduct_eq_last_frameProducts hσ
  have h_nonneg : 0 ≤ Φ v (θ * star θ - S.N ^ 2) := by
    rw [← h_norm]
    simp [dotProduct, conj_mul']
    -- The goal is `0 ≤ N ∑ j, ‖ω j‖²` at the place `v`.
    positivity
  have h_pos : 0 < Φ v (θ * star θ - S.N ^ 2) := ((map_ne_zero (Φ v)).2 hθ).lt_of_le' h_nonneg
  simpa [θ, mul_conj', sq] using (Complex.lt_def.1 h_pos).1

/-- For `σ` fixing the `ϱ` hyperbolic pairs, the map `(p, u, u') ↦ u (w_p σ) u'⁻¹` is injective,
where `u`, `u'` are rational points of 𝖴 = `besselU` and `p` is a `ϱ`-tuple with entries in 𝒯 =
`S.entrySet`, completed by the last entry `t` (`padTuple`). -/
lemma injective_bigCellTerm {σ : S.G E} (hσ : σ ∈ floorGroup 𝔰.ϱ) (t : Eˣ) :
    Injective fun i : (Fin 𝔰.ϱ → S.entrySet) × (S.ratMiddle E).besselU × (S.ratMiddle E).besselU ↦
      i.2.1.val * (weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (i.1 a).val) t) * σ) * i.2.2.val⁻¹ :=
  fun _ _ h ↦ by simpa [Prod.ext_iff, funext_iff, padTuple] using big_cell_unique hσ h

/-- The Weyl element depends only on the entries of its tuple below `ϱ`, so these may be completed
by any last entry `t`. -/
lemma weylElem_padTuple (p : ℕ → Eˣ) (t : Eˣ) :
    (weylElem 𝔰.ϱ p : S.G E) = weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ p a) t) :=
  weylElem_congr fun a ha ↦ by simp [padTuple, ha]

end

/-- Let `S` satisfy the standing hypotheses `New.Filling.IsAdmissible`. Let `σ` fix the vectors
`e_a`, `e*_a` of the `ϱ = 𝔰.ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`), let `t` be the last diagonal
entry of `S.frameProducts σ`, and let `u`, `u'` lie in the unipotent group `besselU`. Let
`γ = u⁻¹ (w_p σ) u'` be a term over `(c, s, c')`, and suppose that its amplitude for the cut Bessel
function W♭, the integral of `W♭(y) ⊗ W♭(γ⁻¹ y)^*` against the cutoffs of `c`, `c'` over the points
`y` at infinity, is nonzero. Then `t` and the entries `p a`, `a < ϱ`, lie in 𝒯 = `S.entrySet`, the
finite set of quotients of two elements of `S.boundedNonzeroIntegers`. -/
lemma head_and_last_mem_entrySet [WeilData E] [S.IsAdmissible] {c c' : S.Classes} {s : S.ResidueGL}
    {u u' σ : S.G E} {p : ℕ → Eˣ} {t : Eˣ} (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (ht : S.frameProducts σ 𝔰.top 𝔰.top = t) (hu : u ∈ besselU) (hu' : u' ∈ besselU)
    (hγ : u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u' ∈ S.termsOver c s c')
    (h_amp : S.amplitude .cut c c' (u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u') ≠ 0) :
    (∀ a : Fin 𝔰.ϱ, p a ∈ S.entrySet) ∧ t ∈ S.entrySet := by
  rw [weylElem_padTuple p t] at hγ h_amp
  have h_mem {a : ℕ} (ha : a ≤ 𝔰.ϱ) : padTuple (fun a : Fin 𝔰.ϱ ↦ p a) t a ∈ S.entrySet :=
    entry_mem_entrySet hu hu' hσ (by simp [padTuple, ht]) hγ h_amp ha
  exact ⟨fun a ↦ by simpa [padTuple] using h_mem a.2.le, by simpa [padTuple] using h_mem le_rfl⟩

/-- Let `σ` fix the vectors `e_a`, `e*_a` of the `ϱ = 𝔰.ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`). Let
`θ = h(z, σ z)` be the last diagonal entry of the matrix `S.frameProducts σ` of products of the
frame with its image, and suppose `θ θ̄ ≠ N²` for `N = S.N = -h(z, z)`. Let `u`, `u'` lie in the
group 𝖴 = `besselU` of block upper unitriangular isometries, and take the Weyl element
`w_p = weylElem 𝔰.ϱ p`, with `e_a ↦ p_a e*_a` and `e*_a ↦ e_a / p̄_a` for `a < ϱ`. Then
`γ = u (w_p σ) u'⁻¹` lies in `S.termsOfLink Λ` for the link `Λ` (`New.link`) of `w_1 σ`: the link of
`γ` is `Λ`, and `termDisc γ = D D̄ - N² D' D̄'` is nonzero, with `D`, `D'` the last two leading
minors of `S.frameProducts γ`. -/
lemma mem_termsOfLink_bigCell {σ : S.G E} {Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)}
    (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hθ : S.frameProducts σ 𝔰.top 𝔰.top * star (S.frameProducts σ 𝔰.top 𝔰.top) - S.N ^ 2 ≠ 0)
    (hΛ : Λ = link (weylElem 𝔰.ϱ 1 * σ)) (p : ℕ → Eˣ) {u u' : S.G E}
    (hu : u ∈ besselU) (hu' : u' ∈ besselU) :
    u * (weylElem 𝔰.ϱ p * σ) * u'⁻¹ ∈ S.termsOfLink Λ := by
  -- Both conditions hold for `w_p σ` and are invariant under 𝖴 on either side.
  rw [← inv_inv u]
  constructor
  · rw [termDisc, frameDisc_frameGram_inv_mul_mul_of_mem_besselU (inv_mem hu) (inv_mem hu'),
      frameDisc_weylElem_mul hσ]
    exact mul_ne_zero (by simp [Finset.prod_eq_zero_iff]) hθ
  · rw [link_inv_mul_mul_of_mem_besselU (inv_mem hu) (inv_mem hu'), hΛ,
      link_weylElem_mul_eq_iff hσ hσ]

/-- A sum of amplitudes is a finite sum of orbit sums over 𝖴 × 𝖴, with 𝖴 = `besselU`. Let `S`
satisfy the standing hypotheses `New.Filling.IsAdmissible`, and let the elements of the finite set
𝒯 = `S.entrySet` be units off the set of places `T`. The terms over `(c, s, c')` are the rational
`γ` with `h_c⁻¹ γ h_c'` in the group `K = S.latticeStabilizer` of integral points and of reduction
`s`; let the leading minors `D_0, …, D_ϱ` of their matrices `S.frameProducts γ` be nonzero. Let `A`
be the sum `amplitudeSum` of the amplitudes, for the cut Bessel function, of the terms with
`termDisc γ = |D_{ϱ+1}|² - N² |D_ϱ|² ≠ 0` and link `Λ`, and suppose `A ≠ 0`. Then there are `t ∈ 𝒯`,
`σ` and `k ∈ K` with the properties `NamesLink`: `σ` fixes the `ϱ` hyperbolic pairs, `t` is the
last diagonal entry of `S.frameProducts σ`, `t t̄ - N²` is totally positive, `Λ` is the link of
`w_1 σ`, `h_c⁻¹ σ h_c'` is integral off `T`, and `k` reduces to `s`. Moreover `A` is the sum, over
the `ϱ`-tuples `p` in 𝒯 followed by `t` (`padTuple`), of the sums `cosetAmplitude` of the amplitudes
of the terms `u w_p σ u'⁻¹` with `u`, `u'` in 𝖴. -/
lemma exists_amplitudeSum_eq_sum_cosetAmplitude [WeilData E] [S.IsAdmissible] {c c' : S.Classes}
    {s : S.ResidueGL} {Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)}
    (h_entry_units : ∀ t ∈ S.entrySet, t.val ∈ ratIntegralOff T ∧ t⁻¹.val ∈ ratIntegralOff T)
    (h_sum_ne : S.amplitudeSum .cut (S.termsOfLink Λ) c s c' ≠ 0)
    (h_minors : ∀ γ ∈ S.termsOver c s c', ∀ l : Fin 𝔰.n,
      leadingMinor (S.frameProducts γ) l.castSucc ≠ 0) :
    ∃ (t : Eˣ) (σ : S.G E) (k : S.latticeStabilizer), S.NamesLink T c s c' Λ t σ k ∧
      S.amplitudeSum .cut (S.termsOfLink Λ) c s c' = ∑ p : Fin 𝔰.ϱ → S.entrySet,
        S.cosetAmplitude .cut c s c'
          (weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) t) * σ) := by
  classical
  -- Take a contributing term γ₀ and write γ₀ = u₀⁻¹ w_{p₀} σ u₀' in the big cell. The contributing
  -- terms γ over (c, s, c') with link Λ and `termDisc γ ≠ 0` are among the u w_p σ u'⁻¹ with p in
  -- 𝒯, each occurring once; sum over (u, u') for fixed p.
  obtain ⟨⟨γ₀, ⟨h_disc₀, hΛ⟩, hγ₀⟩, h_amp₀⟩ :
      ∃ γ : ↥(S.termsOfLink Λ ∩ S.termsOver c s c'), S.amplitude .cut c c' γ.1 ≠ 0 := by
    by_contra! h_zero
    exact h_sum_ne (by simp [amplitudeSum, h_zero])
  obtain ⟨u₀, hu₀, u₀', hu₀', p₀, σ, hσ, rfl⟩ := exists_big_cell_decomp (h_minors _ hγ₀)
  have h_link : Λ = link (weylElem 𝔰.ϱ 1 * σ) := by
    rw [← hΛ, link_inv_mul_mul_of_mem_besselU hu₀ hu₀', link_weylElem_mul_eq_iff hσ hσ]
  -- With θ the last diagonal entry of `S.frameProducts σ`, the number θ θ̄ - N² is a factor of
  -- `termDisc γ₀`, which is nonzero.
  let θ : E := S.frameProducts σ 𝔰.top 𝔰.top
  have hθ_norm : θ * star θ - S.N ^ 2 ≠ 0 := by
    rw [termDisc, frameDisc_frameGram_inv_mul_mul_of_mem_besselU hu₀ hu₀',
      frameDisc_weylElem_mul hσ] at h_disc₀
    exact right_ne_zero_of_mul h_disc₀
  have hθ_gt (v : InfinitePlace E) : S.N ^ 2 < ‖Φ v θ‖ ^ 2 :=
    sq_lt_norm_sq_last_frameProducts hσ hθ_norm v
  have hθ_ne : θ ≠ 0 := fun h_zero ↦ by
    simpa [h_zero, (sq_nonneg _).not_gt] using hθ_gt Classical.ofNonempty
  let t : Eˣ := Units.mk0 θ hθ_ne
  let δ (i : (Fin 𝔰.ϱ → S.entrySet) × (S.ratMiddle E).besselU × (S.ratMiddle E).besselU) : S.G E :=
    i.2.1.val * (weylElem 𝔰.ϱ (padTuple (fun a ↦ (i.1 a).val) t) * σ) * i.2.2.val⁻¹
  let a : S.G E → EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
    (S.termsOfLink Λ ∩ S.termsOver c s c').indicator (S.amplitude .cut c c')
  -- Every contributing term is a value of δ: it lies in the big cell, and the link fixes σ.
  have hδ_onto (γ : S.G E) (hγ : γ ∈ S.termsOfLink Λ ∩ S.termsOver c s c')
      (h_amp : S.amplitude .cut c c' γ ≠ 0) : γ ∈ range δ := by
    obtain ⟨⟨-, hγ_link⟩, hγ_over⟩ := hγ
    obtain ⟨u, hu, u', hu', p, τ, hτ, rfl⟩ := exists_big_cell_decomp (h_minors γ hγ_over)
    obtain rfl : τ = σ := (link_weylElem_mul_eq_iff hτ hσ).1
      ((link_inv_mul_mul_of_mem_besselU hu hu').symm.trans (hγ_link.trans h_link))
    obtain ⟨hp, -⟩ := head_and_last_mem_entrySet (t := t) hσ rfl hu hu' hγ_over h_amp
    refine ⟨(fun a ↦ ⟨p a, hp a⟩, ⟨u, hu⟩⁻¹, ⟨u', hu'⟩⁻¹), ?_⟩
    simp [δ, ← weylElem_padTuple]
  have h_sum : HasSum (a ∘ δ) (S.amplitudeSum .cut (S.termsOfLink Λ) c s c') := by
    have h_zero (γ : S.G E) (hγ : γ ∉ range δ) : a γ = 0 :=
      indicator_apply_eq_zero.2 fun h ↦ not_not.1 (mt (hδ_onto γ h) hγ)
    rw [Injective.hasSum_iff (g := δ) (injective_bigCellTerm hσ t) h_zero]
    exact hasSum_subtype_iff_indicator.1 (summable_amplitude _ c s c').hasSum
  obtain ⟨h_head₀, ht⟩ := head_and_last_mem_entrySet (t := t) hσ rfl hu₀ hu₀' hγ₀ h_amp₀
  have h_off : S.IsIntegralOff T (S.translateByClassReps c c' σ) :=
    (isIntegralOff_of_mem_termsOver hu₀ hu₀' hσ (fun a ↦ (h_entry_units _ (h_head₀ a)).2) hγ₀).2
  obtain ⟨k, hk, -⟩ := hγ₀
  refine ⟨t, σ, k,
    { mem_floorGroup := hσ, frameProducts_top_top := rfl,
      sq_lt_norm_sq := hθ_gt, reduction_eq := hk,
      link_eq := h_link, mem_entrySet := ht, isIntegralOff := h_off }, ?_⟩
  have h_fiber (p : Fin 𝔰.ϱ → S.entrySet) : ∑' q, (a ∘ δ) (p, q) =
      S.cosetAmplitude .cut c s c' (weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).val) t) * σ) := by
    refine tsum_congr fun ⟨u, u'⟩ ↦ ?_
    have h_mem : δ (p, u, u') ∈ S.termsOfLink Λ :=
      mem_termsOfLink_bigCell hσ hθ_norm h_link _ u.prop u'.prop
    simp only [a, δ, Function.comp_apply, indicator, mem_inter_iff, h_mem, true_and]
  simp_rw [← h_fiber]
  exact (h_sum.prod_fiberwise fun p ↦ (h_sum.summable.prod_factor p).hasSum).unique
    (hasSum_fintype _)

/-! ### Global against local: levels, moduli and characters -/

/-- For a finite adele `t` and a tuple `x` of finite adeles, the vector `vectorOfLastEntry` of their
projections to `T`, formed with the projection of `S.piN`, is the projection of their vector
`vectorOfLastEntry`. -/
theorem vectorOfLastEntry_evalPlaces (t : 𝔸f E) (x : 𝔰.κ → 𝔸f E) :
    vectorOfLastEntry (S.piN.map (evalPlaces T)) (evalPlaces T t) (evalPlaces T ∘ x) =
      evalPlaces T ∘ vectorOfLastEntry S.piN t x := by
  -- Coordinate by coordinate: `evalPlaces T` is a ring homomorphism that commutes with `star`.
  apply funext
  simp [Sum.forall, vectorOfLastEntry, besselLatticeBasis, middleInclusionMatrix, mulVec,
    dotProduct,
    Matrix.diagonal, apply_ite (evalPlaces T), ← star_evalPlaces, -Units.val_inv_eq_inv_val]

/-- The projection to `T` of h_c⁻¹ w_p σ h_c' is w_p times the projection of h_c⁻¹ σ h_c'. -/
lemma toPlaces_translateByClassReps_weylElem_mul {σ : (S.ratMiddle E).G} {p : ℕ → Eˣ}
    (c c' : S.Classes) :
    S.toPlaces T (S.translateByClassReps c c' (weylElem 𝔰.ϱ p * σ)) =
      weylElem 𝔰.ϱ (Units.map (ratToPlaces T) ∘ p) *
        S.toPlaces T (S.translateByClassReps c c' σ) := by
  -- Move the adelic Weyl element to the left and project it entry by entry.
  set q : ℕ → (LocProd T)ˣ := Units.map (ratToPlaces T) ∘ p
  rw [translateByClassReps_weylElem_mul, map_mul]
  congr 1
  -- The name `q` keeps `simp` from unfolding the units on the right.
  ext : 3
  simp [toPlaces, U.map, weylElem, weylOn, apply_ite (evalPlaces T), -star_algebraMap_finAdele,
    -Units.val_inv_eq_inv_val]
  rfl

variable [P : IntegralPlace (LocProd T)]
  {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

/-- Let `P` be a structure of a finite place on the product of the completions at `T`, with modulus
`P.modulus`. Let `x` and `x⁻¹` lie in the ring `ratIntegralOff T` of `T`-integers of `E`. Then the
square root of `P.modulus` at the component `evalPlaces T x` of `x` at `T` is the inverse of the
product of the absolute values `‖Φ v x‖` over the infinite places `v`, with `Φ v` the chosen
embedding. -/
theorem _root_.New.Floors.IntegralPlace.modulus_evalPlaces_rpow_half {x : Eˣ}
    (hx : x.val ∈ ratIntegralOff T ∧ x⁻¹.val ∈ ratIntegralOff T) :
    P.modulus (evalPlaces T x.val) ^ (2⁻¹ : ℝ) = (∏ v : InfinitePlace E, ‖Φ v x.val‖ₑ)⁻¹ := by
  obtain ⟨hx_int, hx_inv⟩ := hx
  let u : (LocProd T)ˣ := x.map (ratToPlaces T).1
  -- The product formula: the inequality `sqrt_genIndex_le_prod_norm` for `x` and for `x⁻¹` gives
  -- equality.
  have h_prod : √(genIndex u.1) = ∏ v : InfinitePlace E, ‖Φ v x.1‖ := by
    refine (sqrt_genIndex_le_prod_norm T x.ne_zero hx_int).antisymm ?_
    simpa [u, genIndex_eq_inv_prod_norm] using
      inv_anti₀ (Real.sqrt_pos.2 (genIndex_pos u⁻¹))
        (sqrt_genIndex_le_prod_norm T x⁻¹.ne_zero hx_inv)
  have h_modulus : P.modulus (evalPlaces T x.val) = (ENNReal.ofReal √(genIndex u.1) ^ 2)⁻¹ :=
    inv_eq_iff_eq_inv.1 (P.inv_modulus_eq_sqrt_genIndex_sq u)
  rw [h_modulus, h_prod]
  simp [inv_rpow, ← rpow_natCast_mul, ofReal_prod_of_nonneg]

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). A finite adelic point `x` lies in the principal level `K(M)` exactly when it is integral
off `T` and its projection to `T` lies in the group `K(M) = F.congruenceSubgroup`. -/
theorem IsFillingData.mem_principalLevel_iff [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] :
    x ∈ S.principalLevel ↔ S.IsIntegralOff T x ∧ S.toPlaces T x ∈ F.congruenceSubgroup := by
  rw [principalLevel_eq_unitaryLevel, mem_unitaryLevel_iff hM_inv.out, ← hF.levelUnit_eq]

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). Two elements `k`, `l` of the group `K` of integral points have the same reduction modulo
`M` exactly when their projections to `T` are in the same left coset of
`K(M) = F.congruenceSubgroup`. -/
theorem IsFillingData.reduction_eq_iff [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] (k l : S.latticeStabilizer) :
    S.reduction k = S.reduction l ↔ (S.toPlaces T k)⁻¹ * S.toPlaces T l ∈ F.congruenceSubgroup := by
  obtain ⟨l, rfl⟩ : ∃ a : S.latticeStabilizer, k * a = l := mul_left_surjective k l
  simpa [principalLevel, mem_latticeStabilizer_iff.mp l.prop] using hF.mem_principalLevel_iff
    (x := l)

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). For a finite adelic point `x` integral off `T`, the character `P.ψ` at the sum of the
simple root coordinates of its projection, divided by `F.levelUnit`, is the unipotent character of
`S` at `x`. -/
theorem IsFillingData.psi_simpleRootSum_eq_unipotentChar [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] (h_off : S.IsIntegralOff T x) :
    P.ψ (F.levelUnit⁻¹.val * simpleRootSum (S.toPlaces T x)) = S.unipotentChar x := by
  have h_int : S.ideleM⁻¹.val * simpleRootSum x ∈ integralOff T :=
    mul_mem hM_inv.out (sum_mem fun _ _ ↦ h_off.isIntMatrix _ _)
  calc
    _ = S.charOnPlaces T (evalPlaces T (S.ideleM⁻¹.val * simpleRootSum x)) := by
      simp [hF.levelUnit_eq, hF.psi_eq, simpleRootSum, toPlaces, U.map]
    _ = _ := S.charOnPlaces_evalPlaces T h_int

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). Then `P.modulus F.levelUnit` is `(M ^ f)⁻¹ ^ 2`, with `M` read as the natural number
`S.M` and `f` the number of infinite places of `E`. -/
theorem IsFillingData.modulus_levelUnit [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] :
    P.modulus F.levelUnit = (S.M ^ numInfPlaces E : ℝ≥0∞)⁻¹ ^ 2 := by
  -- The product formula for `S.ideleM`, which is a unit off `T`, squared.
  have h_rat : P.modulus F.levelUnit ^ (2⁻¹ : ℝ) = (S.M ^ numInfPlaces E : ℝ≥0∞)⁻¹ := by
    simpa [hF.levelUnit_eq, ideleM_val, ← ofReal_norm] using
      P.modulus_evalPlaces_rpow_half ⟨((mem_Ô_iff T).1 S.ideleM_mem).2, hM_inv.out⟩
  rw [← h_rat, ← rpow_natCast, Nat.cast_ofNat, rpow_inv_rpow two_ne_zero]

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). Let 𝖴 = `besselU` be the group of block upper unitriangular isometries. The order
`S.unipotentOrder` of the reduction modulo `M` of the integral points of 𝖴, times the measure
`F.unipotentMass` of 𝖴 ∩ K(M) at `T`, is one. Here `K(M) = F.congruenceSubgroup` consists of the
integral points congruent to `1` modulo `M`. -/
theorem IsFillingData.unipotentOrder_mul_unipotentMass_eq_one [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] :
    S.unipotentOrder * F.unipotentMass = 1 := by
  -- By `modulus_levelUnit` the floor `l` has volume `(M ^ f)⁻¹ ^ (2 d + 1)`, with
  -- `f = numInfPlaces E` and `d = k + 1 + 2 (ϱ - (l + 1))`; sum the exponents.
  have h_sum (n : ℕ) :
      ∑ l ∈ .range n, (2 * (𝔰.k + 1 + 2 * (n - (l + 1))) + 1) = n * (2 * 𝔰.k + 2 * n + 1) := by
    induction n with
    | zero => simp
    | succ n ih => grind [Finset.sum_range_succ']
  simp [-Nat.cast_mul, PlaceData.unipotentMass, PlaceData.floorModulus, hF.modulus_levelUnit,
    ← rpow_natCast_mul, ← pow_mul _ 2, ← pow_succ, Finset.prod_pow_eq_pow_sum]
  rw [pow_mul, h_sum, ← mul_pow]
  simp [ENNReal.mul_inv_cancel, Nat.Prime.ne_zero, -Nat.cast_mul]

/-! ### Counting images modulo `M` by measures -/

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). Let `B` be a subgroup of the finite adelic unitary group and `μ` an s-finite measure on
the unitary group over the product `LocProd T` of the completions at `T`. Suppose that almost every
point for `μ` is the projection (`toPlaces`) of an element of `B` integral off `T`, and that `μ` is
invariant under right translation by the projections of the elements of `B`. Then the order of the
image `S.reducedImage B` modulo `M` of the integral points of `B`, times the measure of the
principal congruence subgroup `K(M) = F.congruenceSubgroup`, is the measure of the group
`unitaryLevel P.integers 1 _` of integral points at `T`. -/
theorem IsFillingData.card_reducedImage_mul_measure_congruenceSubgroup_eq [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] {B : Subgroup S.GFin}
    {μ : Measure (U (S.latticeMiddle (LocProd T)).splitGram)} [SFinite μ]
    (h_supp : ∀ᵐ z : U (S.latticeMiddle (LocProd T)).splitGram ∂μ,
      ∃ x ∈ B, S.toPlaces T x = z ∧ S.IsIntegralOff T x)
    (h_inv : ∀ x ∈ B, μ ∗ₘ Measure.dirac (S.toPlaces T x) = μ) :
    Nat.card (S.reducedImage B) * μ F.congruenceSubgroup =
      μ (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) := by
  classical
  -- Choose lifts `k s ∈ B ∩ K` of the `s ∈ S.reducedImage B`. Almost everywhere, the integral
  -- points are the disjoint union of the cosets `C s = K(M) (k s)⁻¹`, all of measure `μ K(M)`.
  have h_lift (s : S.reducedImage B) :
      ∃ k : S.latticeStabilizer, k.val ∈ B ∧ S.reduction k = s := s.2
  choose k hkB hk_red using h_lift
  let C (s : S.reducedImage B) : Set (U (S.latticeMiddle (LocProd T)).splitGram) :=
    (· * S.toPlaces T (k s)) ⁻¹' F.congruenceSubgroup
  have hC_meas (s : S.reducedImage B) : MeasurableSet (C s) :=
    measurable_mul_const _ P.measurableSet_unitaryLevel
  have hC_vol (s : S.reducedImage B) : μ (C s) = μ F.congruenceSubgroup := by
    nth_rw 2 [← h_inv _ (hkB s)]
    rw [μ.mconv_dirac, μ.map_apply (by fun_prop) P.measurableSet_unitaryLevel]
  have hC_disj : Pairwise (onFun Disjoint C) := by
    refine fun s t hst ↦ disjoint_left.2 fun z hs ht ↦ hst (Subtype.ext ?_)
    rw [← hk_red s, ← hk_red t, hF.reduction_eq_iff]
    simpa using mul_mem (inv_mem hs.out) ht.out
  have h_cover : ⋃ s, C s =ᵐ[μ]
      (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram : Set _) := by
    refine eventuallyEqSet_iff.2 (h_supp.mono ?_)
    rintro _ ⟨x, hx, rfl, hx_off⟩
    refine mem_iUnion.trans ⟨fun ⟨s, hs⟩ ↦ ?_, fun hxK ↦ ?_⟩
    · exact (mul_mem_cancel_right (mem_latticeStabilizer_iff.1 (k s).prop).2).1
        (P.unitaryLevel_le_unitaryLevel_one hs)
    · -- The point `x` lies in `S.latticeStabilizer`; take for `s` the reduction of `x⁻¹`.
      lift x to S.latticeStabilizer using mem_latticeStabilizer_iff.2 ⟨hx_off, hxK⟩
      refine ⟨⟨S.reduction x⁻¹, x⁻¹, inv_mem hx, rfl⟩, ?_⟩
      simpa [C] using (hF.reduction_eq_iff x⁻¹ _).1 (by simp [hk_red])
  rw [← measure_congr h_cover, measure_iUnion hC_disj hC_meas]
  simp [hC_vol, Nat.card_eq_fintype_card]

/-! ### Double cosets and the Kloosterman sum -/

omit P in
/-- Let `γ = w_p σ` with `σ` fixing the `ϱ` hyperbolic pairs of the basis. Let 𝖴 = `besselU` be the
unipotent group and `𝖴_c(M) = S.classUnipotent c` the group of its rational points `u` with
`h_c⁻¹ u h_c ≡ 1` modulo `M`. Let `r` and `r'` list rational points of 𝖴 without repetition, with
exactly one in each of the cosets `u 𝖴_c(M)` and `u' 𝖴_c'(M)` for which `u⁻¹ γ u'` is a term. Let
`W = S.besselFn side` be the full or the cut Bessel function on the points at infinity. Then the sum
`cosetAmplitude` of the amplitudes of the terms `u γ u'⁻¹` is the sum, over the pairs of
representatives that give a term `δ`, of the orbital integrals `∫ W(y) ⊗ W(δ⁻¹ y)^* dy`. -/
lemma hasSum_besselOrbitalIntegral_cosetAmplitude [WeilData E]
    [S.IsAdmissible] {side : FullOrCut} {σ : S.G E}
    (hσ : σ ∈ floorGroup 𝔰.ϱ) (p : ℕ → Eˣ) {c c' : S.Classes} {s : S.ResidueGL} {ι ι' : Type}
    {r : ι → S.G E} {r' : ι' → S.G E} (hr : ∀ w : ι, r w ∈ besselU) (hr' : ∀ w : ι', r' w ∈ besselU)
    (r_inj : Injective r) (r'_inj : Injective r')
    (h_rep : ∀ u ∈ besselU, ∀ u' ∈ besselU,
      u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u' ∈ S.termsOver c s c' →
        (∃! v : S.classUnipotent c, u * v.val⁻¹ ∈ range r) ∧
        ∃! v' : S.classUnipotent c', u' * v'.val⁻¹ ∈ range r') :
    HasSum
      (fun w : ι × ι' ↦ (S.termsOver c s c').indicator
        (fun δ : S.G E ↦ besselOrbitalIntegral volume
          (fun y : InfinitePlace E → 𝔰.G₁ ↦ WithLp.toLp 2 (S.besselFn side y)) (S.ratToInf δ))
        ((r w.1)⁻¹ * (weylElem 𝔰.ϱ p * σ) * r' w.2))
      (S.cosetAmplitude side c s c' (weylElem 𝔰.ϱ p * σ)) := by
  -- The group `𝖴_c(M) × 𝖴_c'(M)` acts freely on the terms in `X = 𝖴 γ 𝖴`, and each orbit contains
  -- one `δ w`. So the cutoffs may be replaced by the indicator of the set of the `δ w`.
  set γ : S.G E := weylElem 𝔰.ϱ p * σ
  let f (x : (S.ratMiddle E).besselU × (S.ratMiddle E).besselU) : S.G E := x.1.val * γ * x.2.val⁻¹
  have f_inj : Injective f := fun _ _ h ↦ (big_cell_unique hσ h).2
  have f_move (u u' : (S.ratMiddle E).besselU)
      (x : (S.ratMiddle E).besselU × (S.ratMiddle E).besselU) :
      f (u * x.1, u' * x.2) = u * f x * u'.val⁻¹ := by simp [f, mul_assoc]
  let X : Set (S.G E) := range f
  have hX : S.IsStable X := fun u hu u' hu' δ ↦
    ⟨fun ⟨x, hx⟩ ↦ ⟨_, (f_move ⟨u, hu⟩ ⟨u', hu'⟩ x).trans (by simp [hx, mul_assoc])⟩,
      fun ⟨x, hx⟩ ↦ ⟨_, (f_move ⟨u, hu⟩⁻¹ ⟨u', hu'⟩⁻¹ x).trans (by simp [hx])⟩⟩
  have h_block : S.amplitudeSum side X c s c' = S.cosetAmplitude side c s c' γ := by
    rw [amplitudeSum, tsum_subtype _ (S.amplitude side c c'),
      ← f_inj.tsum_eq (support_indicator_subset.trans inter_subset_left), ← indicator_indicator]
    exact tsum_congr fun x ↦ indicator_of_mem (mem_range_self x) _
  let δ (w : ι × ι') : S.G E := (r w.1)⁻¹ * γ * r' w.2
  have δ_eq (w : ι × ι') : δ w = f (⟨r w.1, hr w.1⟩⁻¹, ⟨r' w.2, hr' w.2⟩⁻¹) := by simp [δ, f]
  have δ_inj : Injective δ := fun w w' h ↦ by
    simpa [δ_eq, f_inj.eq_iff, Prod.ext_iff, r_inj.eq_iff, r'_inj.eq_iff] using h
  have h_one (x : S.G E) (hx : x ∈ X ∩ S.termsOver c s c') :
      ∑' v : S.classUnipotent c × S.classUnipotent c',
        (range δ).indicator (1 : S.G E → ℝ≥0∞) (v.1 * x * v.2⁻¹) = 1 := by
    obtain ⟨⟨⟨u, u'⟩, rfl⟩, h_over⟩ := hx
    have h_iff (v : S.classUnipotent c × S.classUnipotent c') : v.1 * f (u, u') * v.2⁻¹ ∈ range δ ↔
        u.val⁻¹ * v.1.val⁻¹ ∈ range r ∧ u'.val⁻¹ * v.2.val⁻¹ ∈ range r' := by
      have h_move : v.1 * f (u, u') * v.2⁻¹ = f (⟨v.1, v.1.prop.1⟩ * u, ⟨v.2, v.2.prop.1⟩ * u') :=
        (f_move ⟨v.1, v.1.prop.1⟩ ⟨v.2, v.2.prop.1⟩ (u, u')).symm
      rw [h_move]
      simp only [mem_range, δ_eq, f_inj.eq_iff, Prod.exists, Prod.mk.injEq, inv_eq_iff_eq_inv,
        Subtype.ext_iff, exists_and_left, exists_and_right]
      simp
    obtain ⟨⟨v, hv, v_unique⟩, v', hv', v'_unique⟩ :=
      h_rep _ (inv_mem u.2) _ (inv_mem u'.2) (by simpa [f] using h_over)
    rw [tsum_eq_single (v, v'), indicator_of_mem ((h_iff (v, v')).2 ⟨hv, hv'⟩), Pi.one_apply]
    refine fun z hz ↦ indicator_of_notMem (fun h_mem ↦ hz ?_) _
    exact Prod.ext (v_unique _ ((h_iff z).1 h_mem).1) (v'_unique _ ((h_iff z).1 h_mem).2)
  obtain ⟨h_sum, h_int, -⟩ := hasSum_amplitudeSum_of_cutoff (side := side) hX c s c'
    (fun x _ ↦ (range δ).indicator 1 x) (fun x hx _ ↦ h_one x hx) fun _ ↦ measurable_const
  -- Only the `δ w` contribute, each with one integral over the infinite points.
  let g (x : S.G E) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
    ∫ y, ((range δ).indicator (1 : S.G E → ℝ≥0∞) x).toReal • S.besselKernel side x y
  have h_zero (x : S.G E) (hx : x ∉ range δ) : (X ∩ S.termsOver c s c').indicator g x = 0 :=
    indicator_apply_eq_zero.2 fun _ ↦ by simp [g, indicator_of_notMem hx]
  rw [← h_block]
  refine ((δ_inj.hasSum_iff h_zero).2 (hasSum_subtype_iff_indicator.1 h_sum)).congr_fun fun w ↦ ?_
  by_cases hw : δ w ∈ S.termsOver c s c'
  · have h_mem : δ w ∈ X ∩ S.termsOver c s c' := ⟨⟨_, (δ_eq w).symm⟩, hw⟩
    rw [indicator_of_mem hw, Function.comp_apply, indicator_of_mem h_mem]
    ext i
    rw [eval_integral_piLp (h_int ⟨δ w, h_mem⟩).eval_piLp i]
    simp [besselOrbitalIntegral, besselKernel]
  · rw [indicator_of_notMem hw, Function.comp_apply, indicator_of_notMem fun h ↦ hw h.2]

/-- Let `F` be a filling datum at `T` (`hF`), that is, a large lattice datum on the completions at
`T` whose modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off
`T` (`hM_inv`). Let `k` be a point of `S.latticeStabilizer`, with reduction `S.reduction k` modulo
`M`. Let `γ` be a rational element whose translate `S.translateByClassReps c c' γ = h_c⁻¹ γ h_c'` is
integral off `T` (`h_off`). Then `γ` lies in `S.termsOver c (S.reduction k) c'` exactly when the
projection of its translate to `T` lies in `S.toPlaces T k · K(M)`, with
`K(M) = F.congruenceSubgroup`. Lying in `S.termsOver` means the translate is integral with reduction
`S.reduction k`. -/
lemma IsFillingData.mem_termsOver_iff [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)]
    {c c' : S.Classes} {γ : S.G E} (k : S.latticeStabilizer)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' γ)) :
    γ ∈ S.termsOver c (S.reduction k) c' ↔
      (S.toPlaces T k)⁻¹ * S.toPlaces T (S.translateByClassReps c c' γ) ∈ F.congruenceSubgroup := by
  constructor
  · rintro ⟨l, h_red, hl⟩
    rw [← hl, ← hF.reduction_eq_iff, h_red]
  · intro h
    have h_int : S.translateByClassReps c c' γ ∈ S.latticeStabilizer :=
      mem_latticeStabilizer_iff.2 ⟨h_off, (mul_mem_cancel_left
        (inv_mem (mem_latticeStabilizer_iff.1 k.2).2)).1 (P.unitaryLevel_le_unitaryLevel_one h)⟩
    exact ⟨⟨_, h_int⟩, ((hF.reduction_eq_iff k ⟨_, h_int⟩).2 h).symm, rfl⟩

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). Let `S` satisfy the standing hypotheses `New.Filling.IsAdmissible`, let 𝖴 = `besselU` be
the group of block upper unitriangular isometries, and put `K(M) = F.congruenceSubgroup` and
`𝖴_c(M) = S.classUnipotent c`. The translate `S.translateByClassReps c c u = h_c⁻¹ u h_c`, read at
`T`, matches the cosets `u 𝖴_c(M)` of the points `u` of 𝖴 over `E` whose translate is integral off
`T` with the cosets of `𝖴 ∩ K(M)` in 𝖴 at `T`. This is stated by a list `r` of rational
representatives, one for each coset at `T`. -/
lemma IsFillingData.exists_injective_mem_besselU_and_isIntegralOff [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] [S.IsAdmissible] (c : S.Classes) :
    ∃ r : F.UnipotentCosets → S.G E,
      Injective r ∧
      (∀ w : F.UnipotentCosets, r w ∈ besselU) ∧
      (∀ w : F.UnipotentCosets, S.IsIntegralOff T (S.translateByClassReps c c (r w))) ∧
      (∀ w : F.UnipotentCosets,
        w.out.val⁻¹ * S.toPlaces T (S.translateByClassReps c c (r w)) ∈ F.congruenceSubgroup) ∧
      ∀ u ∈ besselU, S.IsIntegralOff T (S.translateByClassReps c c u) →
        ∃! v : S.classUnipotent c, u * v.val⁻¹ ∈ range r := by
  let pos (u : S.G E) : S.GFin := S.translateByClassReps c c u
  -- Lift a point at `T` by `1` off `T`, and approximate the lift by a rational point.
  have h_dense (w : F.UnipotentCosets) : ∃ u ∈ besselU,
      S.IsIntegralOff T (pos u) ∧ w.out.val⁻¹ * S.toPlaces T (pos u) ∈ F.congruenceSubgroup := by
    obtain ⟨x, hx, hx_off, hx_unip, -⟩ := S.exists_isIntegralOff_toPlaces_eq w.out.val
    obtain ⟨u, hu, hux, -⟩ := exists_rat_approx_unipotentChar_eq c (hx_unip w.out.2)
    obtain ⟨h_off, h_level⟩ := hF.mem_principalLevel_iff.1 hux
    exact ⟨u, hu, (mul_mem_cancel_left (inv_mem hx_off)).1 h_off, by simpa [hx] using h_level⟩
  choose r hr r_off r_level using h_dense
  refine ⟨r, fun w w' h ↦ PlaceData.unipotentCosets_eq_of_inv_mul_mem ?_, hr, r_off, r_level,
    fun u hu h_off ↦ ?_⟩
  · simpa [h] using mul_mem (r_level w) (inv_mem (r_level w'))
  -- The point `u` lies in `r w 𝖴_c(M)` exactly when `w` is the coset of its translate at `T`.
  let u₀ : (S.latticeMiddle (LocProd T)).besselU :=
    ⟨S.toPlaces T (pos u), (hu.translateByClassReps_mem_besselU c).map_mem_agreeWithOneOn _⟩
  let w₀ : F.UnipotentCosets := u₀
  have hw₀ : (S.toPlaces T (pos u))⁻¹ * w₀.out.val ∈ F.congruenceSubgroup :=
    PlaceData.inv_mul_out_mem (F := F) u₀
  have h_coset (w : F.UnipotentCosets) : (r w)⁻¹ * u ∈ S.classUnipotent c ↔ w = w₀ := by
    have h_unip : (r w)⁻¹ * u ∈ S.classUnipotent c ↔ (pos (r w))⁻¹ * pos u ∈ S.principalLevel := by
      simp [pos, classUnipotent, translateByClassReps, mul_assoc, mul_mem (inv_mem (hr w)) hu]
    have h_int : S.IsIntegralOff T ((pos (r w))⁻¹ * pos u) := mul_mem (inv_mem (r_off w)) h_off
    rw [h_unip, hF.mem_principalLevel_iff, and_iff_right h_int, map_mul, map_inv]
    refine ⟨fun h ↦ PlaceData.unipotentCosets_eq_of_inv_mul_mem ?_, ?_⟩
    · simpa [mul_assoc] using mul_mem (mul_mem (r_level w) h) hw₀
    · rintro rfl
      simpa [mul_assoc] using inv_mem (mul_mem hw₀ (r_level w₀))
  refine ⟨⟨(r w₀)⁻¹ * u, (h_coset w₀).2 rfl⟩, ⟨w₀, by simp⟩, ?_⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩
  obtain rfl : v = (r w)⁻¹ * u := by simp [hw]
  simp only [(h_coset w).1 hv]

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). For a rational point `u` of 𝖴 = `besselU` whose translate `h_c⁻¹ u h_c` is integral off
`T`, the finite Bessel function `P.extendedBesselChar F.levelUnit` at the projection of the
translate is the character `S.unipotentChar` at the finite part of `u`. -/
lemma IsFillingData.extendedBesselChar_toPlaces_translateByClassReps [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)]
    {c : S.Classes} {u : S.G E} (hu : u ∈ besselU)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c u)) :
    P.extendedBesselChar F.levelUnit (S.toPlaces T (S.translateByClassReps c c u)) = S.unipotentChar
      (S.ratToFin u) := by
  have hu' : S.translateByClassReps c c u ∈ besselU := hu.translateByClassReps_mem_besselU c
  -- The character is trivial on the integral points off `T`, and conjugation by `h_c` keeps it.
  rw [P.extendedBesselChar_eq (u := S.toPlaces T (S.translateByClassReps c c u))
    (hu'.map_mem_agreeWithOneOn _)
      (by simp),
    hF.psi_simpleRootSum_eq_unipotentChar h_off,
    unipotentChar_eq_of_mem_principalLevel hu' (ratToFin_mem_besselU_iff.mpr hu) c.out
      (by simp [translateByClassReps, mul_assoc])]

omit P in
/-- Phases at the infinite places. Let `W = S.besselFn side` be the full or the cut Bessel function
at infinity (`side : FullOrCut`), and `J(γ) = ∫ W(y) ⊗ W(γ⁻¹ y)^* dy` the orbital integral
`besselOrbitalIntegral`. Let `u`, `u'` be rational points of the group 𝖴 = `besselU` of block upper
unitriangular isometries, and let `γ` be rational. Then `J(S.ratToInf (u⁻¹ γ u')) = ψ(u) conj ψ(u')
J(S.ratToInf γ)`, where `ψ(u) = S.unipotentChar (S.ratToFin u)` is the character of 𝖴 at the image
of `u` at the finite places. -/
lemma besselOrbitalIntegral_ratToInf_besselU_mul {side : FullOrCut} {u u' : S.G E}
    (hu : u ∈ besselU) (hu' : u' ∈ besselU) (γ : S.G E) :
    besselOrbitalIntegral volume (fun y : InfinitePlace E → 𝔰.G₁ ↦
      WithLp.toLp 2 (S.besselFn side y))
        (S.ratToInf (u⁻¹ * γ * u')) =
      (S.unipotentChar (S.ratToFin u) * star (S.unipotentChar (S.ratToFin u'))) •
        besselOrbitalIntegral volume
          (fun y : InfinitePlace E → 𝔰.G₁ ↦ WithLp.toLp 2 (S.besselFn side y)) (S.ratToInf γ) := by
  let χ : ℂ := S.unipotentChar (S.ratToFin u) * star (S.unipotentChar (S.ratToFin u'))
  have h_norm (x : S.GFin) : ‖S.unipotentChar x‖ = 1 := norm_selfDualChar
  have h_ne (x : S.GFin) : S.unipotentChar x ≠ 0 := norm_ne_zero_iff.1 (by simp [h_norm])
  have h_kernel (y : InfinitePlace E → 𝔰.G₁) :
      S.besselKernel side (u⁻¹ * γ * u') y = χ • S.besselKernel side γ (S.ratToInf u * y) := by
    have h_move := besselKernel_besselU_mul (side := side) hu hu' (u⁻¹ * γ * u') y
    rw [show u * (u⁻¹ * γ * u') * u'⁻¹ = γ by group] at h_move
    simp only [χ]
    rw [h_move, smul_smul, Complex.star_def, ← Complex.inv_eq_conj (h_norm _), mul_mul_mul_comm,
      mul_inv_cancel₀ (h_ne _), inv_mul_cancel₀ (h_ne _), one_mul, one_smul]
  ext i
  calc
    _ = ∫ y, S.besselKernel side (u⁻¹ * γ * u') y i := rfl
    _ = χ * ∫ y, S.besselKernel side γ (S.ratToInf u * y) i := by
      simp only [h_kernel, PiLp.smul_apply, smul_eq_mul, integral_const_mul]
    _ = χ * ∫ y, S.besselKernel side γ y i := by
      rw [integral_mul_left_eq_self (S.besselKernel side γ · i)]

variable [WeilData E]

/-- Let `F` be a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose
modulus `F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T`
(`hM_inv`). Let `γ = w_p σ`, with the inverses of the entries `p a`, `a < ϱ`, integral off `T`, `σ`
fixing the `ϱ` hyperbolic pairs and `h_c⁻¹ γ h_c'` integral off `T`. Let `x` and `s` be the
projections to `T` of `h_c⁻¹ γ h_c'` and of the integral point `k`, and `k̄` the reduction of `k`.
The Kloosterman sum `F.kloostermanSum x s` is the sum of `χ(u) conj χ(u')` over the cosets `u`, `u'`
in `𝖴 / (𝖴 ∩ K(M))` at `T` with `u⁻¹ x u' ∈ s K(M)`, where `χ` is the character of 𝖴 = `besselU`.
Then the orbit sum `New.Filling.cosetAmplitude` of `γ` over `(c, k̄, c')` is this sum times the
orbital integral of `γ` at the infinite places, for the full or the cut Bessel function
`S.besselFn side`. -/
theorem IsFillingData.cosetAmplitude_eq_kloostermanSum_smul [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] [S.IsAdmissible] {side : FullOrCut}
    {σ : S.G E} {p : ℕ → Eˣ} {c c' : S.Classes} (k : S.latticeStabilizer) (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hp : ∀ a : Fin 𝔰.ϱ, (p a)⁻¹.val ∈ ratIntegralOff T)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' (weylElem 𝔰.ϱ p * σ))) :
    S.cosetAmplitude side c (S.reduction k) c' (weylElem 𝔰.ϱ p * σ) =
      F.kloostermanSum (S.toPlaces T (S.translateByClassReps c c' (weylElem 𝔰.ϱ p * σ)))
        (S.toPlaces T k) •
        besselOrbitalIntegral volume
          (fun y : InfinitePlace E → 𝔰.G₁ ↦ WithLp.toLp 2 (S.besselFn side y))
          (S.ratToInf (weylElem 𝔰.ϱ p * σ)) := by
  classical
  set γ : S.G E := weylElem 𝔰.ϱ p * σ
  obtain ⟨r, r_inj, hr, r_off, r_level, r_rep⟩ :=
    hF.exists_injective_mem_besselU_and_isIntegralOff c
  obtain ⟨r', r'_inj, hr', r'_off, r'_level, r'_rep⟩ :=
    hF.exists_injective_mem_besselU_and_isIntegralOff c'
  -- In a term `u⁻¹ γ u'` over `(c, k̄, c')`, `u` and `u'` have translates integral off `T`.
  have h_int (u : S.G E) (hu : u ∈ besselU) (u' : S.G E) (hu' : u' ∈ besselU)
      (h_over : u⁻¹ * γ * u' ∈ S.termsOver c (S.reduction k) c') :
      S.IsIntegralOff T (S.translateByClassReps c c u) ∧
        S.IsIntegralOff T (S.translateByClassReps c' c' u') := by
    obtain ⟨h_left, -⟩ := isIntegralOff_of_mem_termsOver hu hu' hσ hp h_over
    obtain ⟨l, -, hl⟩ := h_over
    have h_all : S.IsIntegralOff T l.val := (mem_latticeStabilizer_iff.1 l.2).1
    rw [hl, translateByClassReps_inv_mul_mul] at h_all
    exact ⟨h_left, (mul_mem_cancel_left (mul_mem (inv_mem h_left) h_off)).1 h_all⟩
  -- Unfolding: each double coset gives one orbital integral at the infinite places.
  have h_sum := hasSum_besselOrbitalIntegral_cosetAmplitude (side := side) hσ p hr hr' r_inj r'_inj
    fun u hu u' hu' h_over ↦ (h_int u hu u' hu' h_over).imp (r_rep u hu) (r'_rep u' hu')
  -- Rational and local pairs: `(r w)⁻¹ γ (r' w')` is a term over `(c, k̄, c')` exactly when
  -- `(w, w')` is a pair in the sum at `T`.
  let x : (S.latticeMiddle (LocProd T)).G := S.toPlaces T (S.translateByClassReps c c' γ)
  let s : (S.latticeMiddle (LocProd T)).G := S.toPlaces T k
  have h_pair (w w' : F.UnipotentCosets) :
      (r w)⁻¹ * γ * r' w' ∈ S.termsOver c (S.reduction k) c' ↔
        s⁻¹ * (w.out.val⁻¹ * x * w'.out.val) ∈ F.congruenceSubgroup := by
    have h_term : S.IsIntegralOff T (S.translateByClassReps c c' ((r w)⁻¹ * γ * r' w')) := by
      rw [translateByClassReps_inv_mul_mul]
      exact mul_mem (mul_mem (inv_mem (r_off w)) h_off) (r'_off w')
    have h_conj : s⁻¹ * (w.out.val⁻¹ * S.toPlaces T (S.translateByClassReps c c (r w))) * s⁻¹⁻¹ ∈
        F.congruenceSubgroup :=
      conj_mem_unitaryLevel (inv_mem (mem_latticeStabilizer_iff.1 k.2).2) (r_level w)
    rw [hF.mem_termsOver_iff k h_term, ← mul_mem_cancel_left h_conj,
      ← mul_mem_cancel_right (inv_mem (r'_level w')), translateByClassReps_inv_mul_mul]
    simp [x, s, mul_assoc]
  -- Phases: the factor of a pair is the term of the Kloosterman sum.
  have h_phase {d : S.Classes} {u : S.G E} {w : F.UnipotentCosets} (hu : u ∈ besselU)
      (hu_off : S.IsIntegralOff T (S.translateByClassReps d d u))
      (hw : w.out.val⁻¹ * S.toPlaces T (S.translateByClassReps d d u) ∈ F.congruenceSubgroup) :
      S.unipotentChar (S.ratToFin u) = P.extendedBesselChar F.levelUnit w.out.val := by
    rw [← hF.extendedBesselChar_toPlaces_translateByClassReps hu hu_off,
      P.extendedBesselChar_eq_of_inv_mul_mem hw]
  ext i
  rw [PiLp.smul_apply, smul_eq_mul, PlaceData.kloostermanSum, ← tsum_mul_right]
  refine ((EuclideanSpace.proj i).hasSum h_sum).tsum_eq.symm.trans (tsum_congr fun w ↦ ?_)
  by_cases hw : (r w.1)⁻¹ * γ * r' w.2 ∈ S.termsOver c (S.reduction k) c'
  · rw [indicator_of_mem hw, ite_eq_left ((h_pair w.1 w.2).1 hw),
      besselOrbitalIntegral_ratToInf_besselU_mul (hr _) (hr' _),
      h_phase (hr _) (r_off _) (r_level _), h_phase (hr' _) (r'_off _) (r'_level _)]
    rfl
  · rw [indicator_of_notMem hw, ite_eq_right (mt (h_pair w.1 w.2).2 hw), map_zero, zero_mul]

/-- Unfolding, for either of the Bessel functions at infinity. Let `S` be admissible, and let `F` be
a filling datum at `T` (`hF`): a large lattice datum on the completions at `T` whose modulus
`F.levelUnit` is the component of `M = p₀p₁ = S.ideleM`. Let `M⁻¹` be integral off `T` (`hM_inv`).
Put `K(M) = F.congruenceSubgroup`. Let `γ = w_p σ`, with `w_p = weylElem 𝔰.ϱ p`. Suppose the
inverses of the entries `p i`, `i < ϱ`, are integral off `T`, `σ` fixes the `ϱ` hyperbolic pairs,
and `h_c⁻¹ γ h_c'` is integral off `T`, for class representatives `h_c`, `h_c'` of `c`, `c'`. Let
`Z` be a group between `K(M)` and the integral points at `T`. Let `k ∈ S.latticeStabilizer`, and let
the cosets `a`, `b` of `Z.Cosets` satisfy `k⁻¹ a b⁻¹ ∈ K(M)`. Let `q` and `l` be the projections to
`T` of `p` and of `h_c⁻¹ σ h_c'`, and let `κ = F.headDensity 𝔰.ϱ q 1` be the density, a product of
powers of the `P.modulus (q i)`, `i < ϱ`. Then `F.scaledOrbitalIntegral Z q l⁻¹` is `κ` times the
orbital integral of the finite Bessel vector of `Z` at `w_q l`. Its entry `(a, b)` times the
integral `New.besselOrbitalIntegral` of `γ` at the infinite places is `κ` times the measure of
`K(M)` times the orbit sum `New.Filling.cosetAmplitude` of `γ` over `(c, k̄, c')`, with `k̄` the
reduction of `k`. -/
theorem IsFillingData.scaledOrbitalIntegral_smul_eq_cosetAmplitude [hF : S.IsFillingData T F]
    [hM_inv : Fact (S.ideleM⁻¹.val ∈ integralOff T)] [S.IsAdmissible] {side : FullOrCut}
    {σ : S.G E} {p : ℕ → Eˣ} {c c' : S.Classes} {Z : F.IntermediateGroup} {k : S.latticeStabilizer}
    (hσ : σ ∈ floorGroup 𝔰.ϱ) (hp : ∀ a : Fin 𝔰.ϱ, (p a)⁻¹.val ∈ ratIntegralOff T)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' (weylElem 𝔰.ϱ p * σ))) {a b : Z.Cosets}
    (hab : (S.toPlaces T k)⁻¹ * a.out.val * b.out.val⁻¹ ∈ F.congruenceSubgroup) :
    let q : ℕ → (LocProd T)ˣ := Units.map (ratToPlaces T) ∘ p
    let γ : S.G E := weylElem 𝔰.ϱ p * σ
    F.scaledOrbitalIntegral Z q (S.toPlaces T (S.translateByClassReps c c' σ))⁻¹ (a, b) •
        besselOrbitalIntegral volume (fun y : InfinitePlace E → 𝔰.G₁ ↦
          WithLp.toLp 2 (S.besselFn side y)) (S.ratToInf γ) =
      (F.headDensity 𝔰.ϱ q 1).toReal • F.groupMeasure.real F.congruenceSubgroup •
        S.cosetAmplitude side c (S.reduction k) c' γ := by
  -- Both the entry at `T` and the orbit sum contain the Kloosterman sum.
  intro q γ
  rw [PlaceData.scaledOrbitalIntegral, inv_inv, ← toPlaces_translateByClassReps_weylElem_mul,
    PiLp.smul_apply, smul_assoc,
    IntegralPlace.IsLargeLatticeData.besselOrbitalIntegral_besselVector_apply Z _ hab, smul_assoc,
    hF.cosetAmplitude_eq_kloostermanSum_smul k hσ hp h_off]

end New.Filling
