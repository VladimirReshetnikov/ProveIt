import New.Spanning.Bessel.OpenCellPairing
import New.Spanning.RemainingTerms.SchurOrbit
import New.Spanning.Unfolding.TermStructure

/-!
# The orbit bound: a bound for a block of amplitudes; the second moment of a set of terms

Let `S : New.Filling E 𝔰` be filling data. The block `New.Filling.amplitudeSum S side T c s c'` is
the sum of the amplitudes of the rational elements of `T` that lie over the classes `c`, `c'` with
reduction `s` in `New.Filling.ResidueGL S`. The argument `side : New.FullOrCut` selects the full or
the cut Bessel functions. Write `ν` for `New.Filling.unipotentCovolume S`, the covolume of the
unipotent group of a class, `d₁` for `New.Filling.identitySecondMoment S` and `b` for the size
parameter `S.b ≥ 1`. The file defines the second moment of a family of blocks and proves that its
square root is subadditive. Its main result bounds the norm of a single block by ν times the sum of
the orbit bounds of the near orbits.

## Main definitions and results

* `New.Filling.secondMoment A Ω`: for a family of blocks `A c s c'`, the sum of the squared norms of
  the blocks with `s ∈ Ω`, divided by `ν²`.
* `New.Filling.secondMoment_sub_cut_le`: the second moment of the difference between the blocks of
  `U` and those for the cut functions is at most `b⁻⁴⁰` times `identitySecondMoment`.
* `New.Filling.enorm_integral_besselKernel_le`: the bound for one term on the open cell, from the
  bound `New.BesselSystem.enorm_integral_pairKernel_cut_le` for a family of real points.
* `New.Filling.enorm_amplitudeSum_le_orbitBound_top`: the bound for a block when
  `New.Filling.termDisc` vanishes nowhere on `T`; it rests on a change of weight
  (`New.Filling.hasSum_amplitudeSum_of_cutoff`) and the bound for one term.
* `New.Filling.enorm_amplitudeSum_le_orbitBound`: one bound for a stable set of terms of one cell
  rank `j` (`New.Filling.HasCellRank`), none of cell rank `0` over the block. Terms with large
  `New.Filling.termDiscNorm` use the open cell, the others are summed by
  `New.Filling.tsum_amplitudeMajorant_orbit_le`.
* `New.Filling.enorm_amplitudeSum_le_tsum_termSize`: a cut block of a stable subset of
  `New.Filling.remainingTerms` is at most `ν` times the sum of the sizes of its near
  representatives.

Notions from other files:
* `New.Filling.termsOver`: The rational γ such that h_c⁻¹ γ h_c' is integral and has reduction s,
  where h_c is the representative of the class c.
* `New.Filling.ResidueGL`: The finite group of reductions, a product of general linear groups over
  the residue fields at the chosen places.
* `New.Filling.termDisc`: The element 𝗀(γ) = |D_{ϱ+1}|² − N²|D_ϱ|² of E, formed from the last two
  leading minors of the matrix of products between the frame and its image under γ; N = S.N.
* `New.Filling.IsNear`: Some archimedean point y has both y and γ⁻¹ y among the boxed points;
  `New.Filling.IsNearRepresentative` says also that γ is the chosen element of its orbit.
* `New.Filling.IsAdmissible`: The standing hypotheses on the filling data, mostly size inequalities
  between its parameters.

## Relation to the literature

See `New.Spanning.RemainingTerms.Sum` for related work.
-/

/-!
## Second moment of a set of terms and transfer to cut Bessel functions

The second moment `New.Filling.secondMoment` sums the squared norms of the blocks, divided by `ν²`.
-/

section SecondMoment

open MeasureTheory ENNReal Finset

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {V : Type*}
  {S : Filling E 𝔰} [NormedAddCommGroup V]

open scoped Classical in
/-- The second moment 𝖤(A, Ω) of a family of blocks `A c s c'` in a normed group: ν⁻² times the sum
over classes c, c' and s ∈ Ω of the squared norm of `A c s c'`, with ν = `S.unipotentCovolume`. -/
noncomputable def secondMoment (A : S.Classes → S.ResidueGL → S.Classes → V) (Ω : Set S.ResidueGL) :
    ℝ :=
  ∑ c : S.Classes, ∑ c' : S.Classes, ∑ s : S.ResidueGL with s ∈ Ω,
    ‖A c s c'‖ ^ 2 / S.unipotentCovolume ^ 2

/-- The sum, over classes `c`, `c'`, reductions `s ∈ Ω` and submodules `Λ`, of the squared norm of
the block over `(c, s, c')` of the terms `γ` of `T` with `New.link γ = Λ`, for the cut Bessel
function. It takes values in `ℝ≥0∞` and, unlike `New.Filling.secondMoment`, is not divided by
`ν²`. -/
noncomputable def linkSecondMoment (T : Set (S.G E)) (Ω : Set S.ResidueGL) : ℝ≥0∞ :=
  ∑' (c : S.Classes) (c' : S.Classes) (s : Ω)
    (Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)),
    ‖S.amplitudeSum .cut (T ∩ link ⁻¹' {Λ}) c s.val c'‖ₑ ^ 2

/-- The blocks (sums of amplitudes over two classes and a reduction) of a set `T` of rational
elements are the sums of the blocks of `T ∩ Uᶜ` and of `T ∩ U`. -/
lemma amplitudeSum_eq_inter_compl_add_inter [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (T U : Set (S.G E)) {side : FullOrCut} :
    S.amplitudeSum side T = S.amplitudeSum side (T ∩ Uᶜ) + S.amplitudeSum side (T ∩ U) := by
  funext c s c'
  have h_union : T ∩ S.termsOver c s c' =
      (T ∩ Uᶜ ∩ S.termsOver c s c') ∪ (T ∩ U ∩ S.termsOver c s c') := by grind
  simp only [Pi.add_apply, amplitudeSum, tsum_congr_set_coe _ h_union]
  exact (summable_amplitude ..).tsum_union_disjoint (by grind) (summable_amplitude ..)

lemma secondMoment_nonneg {A : S.Classes → S.ResidueGL → S.Classes → V} {Ω : Set S.ResidueGL} :
    0 ≤ secondMoment A Ω := by
  unfold secondMoment
  positivity

/-- Minkowski's inequality for the second moment: for families `A`, `B` of vectors `A c s c'` in
`V`, indexed by `S.Classes × S.ResidueGL × S.Classes`, `√(secondMoment (A + B) Ω) ≤ √(secondMoment A
Ω) + √(secondMoment B Ω)`. -/
lemma sqrt_secondMoment_add_le {A B : S.Classes → S.ResidueGL → S.Classes → V}
    {Ω : Set S.ResidueGL} :
    √(secondMoment (A + B) Ω) ≤ √(secondMoment A Ω) + √(secondMoment B Ω) := by
  classical
  -- The square root of the second moment is a multiple of the norm in an `ℓ²` space of blocks.
  let vec (A : S.Classes → S.ResidueGL → S.Classes → V) :
      PiLp 2 fun _ : S.Classes × S.Classes × Ω ↦ V :=
    WithLp.toLp 2 fun ⟨c, c', s⟩ ↦ A c s c'
  have h_norm (A : S.Classes → S.ResidueGL → S.Classes → V) :
      √(secondMoment A Ω) = ‖vec A‖ / S.unipotentCovolume := by
    rw [PiLp.norm_eq_of_L2, ← Real.sqrt_sq S.unipotentCovolume_pos.le,
      ← Real.sqrt_div' _ (sq_nonneg _)]
    simp [secondMoment, vec, Fintype.sum_prod_type, Finset.sum_div,
      sum_subtype (p := (· ∈ Ω)) (Finset.univ.filter (· ∈ Ω)) (by simp)]
  simp only [h_norm, ← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le (vec A) (vec B)) S.unipotentCovolume_pos.le

/-- For a set `U` of rational elements and fixed `c`, `s`, consider the amplitude sums
`S.amplitudeSum .full U c s c'` and `S.amplitudeSum .cut U c s c'`. The norms of their differences
have sum over `c'` at most `ν b ^ (-k³ f) / 2`. Here `ν` is `S.unipotentCovolume`, `b = S.b` is the
size parameter, `k = 𝔰.k` and `f` is the number of infinite places of `E`. -/
lemma sum_norm_amplitudeSum_sub_cut_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (U : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) :
    ∑ c' : S.Classes, ‖S.amplitudeSum .full U c s c' - S.amplitudeSum .cut U c s c'‖ ≤
      S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * Core.numInfPlaces E))⁻¹ / 2 := by
  -- The amplitudes converge absolutely, and the integrals of the norm of the difference of the
  -- kernels, summed over `c'` and the terms, are small.
  have h_integrable (side : FullOrCut) (c' : S.Classes) (γ : ↥(U ∩ S.termsOver c s c')) :
      Integrable fun y ↦
        (S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y)).toReal •
          S.besselKernel side γ y :=
    integrable_toReal_smul (by fun_prop) (by fun_prop)
      ((ENNReal.le_tsum γ).trans_lt
        ((ENNReal.le_tsum c').trans_lt (tsum_amplitudeMajorant_lt_top U c s)))
  have h_block (c' : S.Classes) :
      ‖S.amplitudeSum .full U c s c' - S.amplitudeSum .cut U c s c'‖ₑ ≤
        ∑' γ : ↥(U ∩ S.termsOver c s c'),
          ∫⁻ y, S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) *
            ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ := by
    simp only [amplitudeSum, ← Summable.tsum_sub, summable_amplitude]
    simp only [amplitude, ← integral_sub, h_integrable, ← smul_sub]
    grw [enorm_tsum_le_tsum_enorm, enorm_integral_le_lintegral_enorm, enorm_toReal_smul_le]
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 1 ≤ S.b := S.one_le_b
  rw [← ofReal_le_ofReal_iff (by positivity), ofReal_sum_of_nonneg (by simp)]
  simp only [ofReal_norm]
  exact (Finset.sum_le_sum fun c' _ ↦ h_block c').trans
    (by simpa using tsum_lintegral_enorm_besselKernel_sub_cut_le (side := .full) U c s)

/-- The cardinality of `S.ResidueGL` times `S.b ^ 40` is at most `(S.b ^ (𝔰.k ^ 3 * f) * 2) ^ 2`,
where `f` is the number of infinite places of `E`. -/
lemma card_residueGL_mul_b_pow_le :
    (Fintype.card S.ResidueGL : ℝ) * S.b ^ 40 ≤
      (S.b ^ (𝔰.k ^ 3 * Core.numInfPlaces E) * 2) ^ 2 := by
  -- `ResidueGL` is a product over the chosen places of general linear groups of degree
  -- `r = 2 ϱ + k + 1` over fields with `levelPrime i` elements, so `|ResidueGL| ≤ M ^ (r² f)` with
  -- `M = levelPrime 0 * levelPrime 1 ≤ b ^ 23`; and `23 r² f + 40 ≤ 2 k³ f` as `k` is large.
  have hb : 1 ≤ S.b := S.one_le_b
  set k : ℕ := 𝔰.k
  set f : ℕ := numInfPlaces E
  have h_group : (Fintype.card S.ResidueGL : ℝ) ≤
      (((S.levelPrime 0 * S.levelPrime 1 : ℕ) : ℝ) ^ (2 * 𝔰.ϱ + k + 1) ^ 2) ^ f := by
    grw [Fintype.card_eq_nat_card, Nat.card_pi, Nat.card_pi.le, card_GL_le _]
    simp [card_resField_eq_levelPrime, S.card_chosenPlaces, ← mul_pow, -Nat.cast_mul, k, f, two_mul,
      add_assoc, add_comm, add_left_comm]
  have h_exp : 23 * (2 * 𝔰.ϱ + k + 1) ^ 2 * f + 40 ≤ k ^ 3 * f * 2 := by
    have hkf : k ≤ f := S.k_le_f
    obtain ⟨r, hr : 1000 * (2 * 𝔰.ϱ + 2) + r = k⟩ := S.thousand_mul_le_k.dest
    rw [← hr] at hkf ⊢
    lia
  calc
    _ ≤ ((S.b ^ 23) ^ (2 * 𝔰.ϱ + k + 1) ^ 2) ^ f * S.b ^ 40 := by grw [h_group, M_le_b_pow]
    _ = S.b ^ (23 * (2 * 𝔰.ϱ + k + 1) ^ 2 * f + 40) := by ring
    _ ≤ S.b ^ (k ^ 3 * f * 2) := by gcongr
    _ ≤ _ := by grw [pow_mul, ← le_mul_of_one_le_right (by positivity) one_le_two]

/-- For a set `U` of rational elements, passing from the Bessel function to its cut changes the
blocks over the reductions in `Ω` little: the sum over classes `c`, `c'` and `s ∈ Ω` of the squared
norms of the differences of the blocks, divided by the square of the covolume
`ν = S.unipotentCovolume`, is at most `b⁻⁴⁰` times `identitySecondMoment`. -/
lemma secondMoment_sub_cut_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (U : Set (S.G E)) {Ω : Set S.ResidueGL} :
    secondMoment (S.amplitudeSum .full U - S.amplitudeSum .cut U) Ω ≤
      (S.b ^ 40)⁻¹ * S.identitySecondMoment := by
  -- Each row `(c, s)` of the difference has square norm at most `η²`; the number of reductions `s`
  -- times `η²` is at most `b⁻⁴⁰ unipotentCovolume²`, and the number of classes `c` is at most
  -- `identitySecondMoment`.
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 1 ≤ S.b := S.one_le_b
  set f : ℕ := numInfPlaces E
  set η : ℝ := S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * f))⁻¹ / 2 with hη
  have h_classes : (Fintype.card S.Classes : ℝ) ≤ S.identitySecondMoment := by
    -- The reduced image is nonempty, and `sourceDim` is a positive multiple of the class number.
    grw [identitySecondMoment, sourceDim, ← Nat.card_pos.succ_le,
      ← le_mul_of_one_le_right' NeZero.one_le]
    simp
  calc
    _ ≤ (∑ c, ∑ s, ∑ c', ‖S.amplitudeSum .full U c s c' - S.amplitudeSum .cut U c s c'‖ ^ 2) /
        S.unipotentCovolume ^ 2 := by
      grw [secondMoment, filter_subset]
      simp [Finset.sum_div, Finset.sum_comm (s := (Finset.univ : Finset S.ResidueGL))]
    _ ≤ (∑ c : S.Classes, ∑ s : S.ResidueGL, η ^ 2) / S.unipotentCovolume ^ 2 := by
      gcongr with c _ s
      -- The sum of squares of a row is at most the square of its sum.
      grw [sum_sq_le_sq_sum_of_nonneg (by simp), sum_norm_amplitudeSum_sub_cut_le U c s]
    _ = Fintype.card S.Classes * (Fintype.card S.ResidueGL * η ^ 2) / S.unipotentCovolume ^ 2 := by
      simp
    _ ≤ S.identitySecondMoment * ((S.b ^ (𝔰.k ^ 3 * f) * 2) ^ 2 / S.b ^ 40 * η ^ 2) /
        S.unipotentCovolume ^ 2 := by
      grw [← h_classes, (le_div_iff₀ (by positivity)).2 card_residueGL_mul_b_pow_le]
    _ = (S.b ^ 40)⁻¹ * S.identitySecondMoment := by simp [hη, field]

end New.Filling

end SecondMoment

/-!
## Bound for a block of amplitudes of a stable set

The norm of a block is bounded under `New.Filling.IsAdmissible`, for the cut Bessel functions
(`New.FullOrCut.cut`) and a set `T` stable under the unipotent group on both sides
(`New.Filling.IsStable`).
-/

section SizeOfBlocks

open DoubleCoset MeasureTheory Matrix Finset Set ENNReal

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {T : Set (S.G E)}

/-- Let `p γ = γ w` with `p` in `U⁰_c` (the elements of the unipotent group `U_c` of the class `c`
that fix the frame) and `w` in `U_c'`. If `𝗀(γ) = S.termDisc γ`, formed from the last two leading
minors of the frame products of `γ`, is nonzero, then `w = 1`. Hence `p = 1`: the stabilizer in
`U⁰_c` of the coset `γ U_c'` is trivial. -/
lemma eq_one_of_mul_eq_mul_of_termDisc_ne_zero {c c' : S.Classes} {γ w p : S.G E}
    (hγ : S.termDisc γ ≠ 0) (hp : p ∈ S.classUnipotent₀ c) (hw : w ∈ S.classUnipotent c')
    (h_eq : p * γ = γ * w) : w = 1 := by
  -- As `p` fixes the frame, `w` fixes the frame of `δ = γ⁻¹`, whose matrix of products with the
  -- standard frame is invertible. So `w` fixes vectors `B` whose dual coordinates form the
  -- identity matrix.
  obtain ⟨hw_unip, -⟩ := hw
  have h_conj : w * γ⁻¹ = γ⁻¹ * p := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h_eq, mul_inv_cancel_right]
  have h_det : (S.frameProducts γ⁻¹).det ≠ 0 := by
    rw [frameProducts, frameGram_inv, det_conjTranspose, star_ne_zero]
    exact ((termDisc_pos_or_eq_zero γ).resolve_right hγ).2
  generalize γ⁻¹ = δ at h_conj h_det
  let toMatrix (g : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := g.1.1
  have h_fix : toMatrix w * frameImage (toMatrix δ) = frameImage (toMatrix δ) := by
    refine frameImage_mul.symm.trans ?_
    rw [h_conj]
    exact frameImage_mul_of_mem_besselU0 hp.2
  have h_inv : (S.frameProducts δ * (S.frameProducts δ)⁻¹).submatrix
      (Fin.castSucc : Fin 𝔰.ϱ → Fin (𝔰.ϱ + 1)) Fin.castSucc = 1 := by
    rw [mul_nonsing_inv _ h_det.isUnit, submatrix_one _ (Fin.castSucc_injective _)]
  apply eq_one_of_mem_besselU_of_fix
    (B := frameImage (toMatrix δ) * (S.frameProducts δ)⁻¹.submatrix id .castSucc) hw_unip
  · rw [← Matrix.mul_assoc, h_fix]
  · simpa [toMatrix, frameGram, splitGram, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.one_apply]
      using h_inv

open scoped Classical in
/-- Let `ρ` choose a representative in each double coset of `U⁰_c = S.classUnipotent₀ c` and
`U_c' = S.classUnipotent c'`, and let `γ` have `S.termDisc γ ≠ 0`. Then exactly one pair `(a, b)` in
these groups carries `γ` to the representative `a γ b⁻¹` of its double coset; this is written as a
sum of indicators equal to 1. -/
lemma tsum_ite_representative_eq_one {c c' : S.Classes}
    {ρ : DoubleCoset.Quotient (S.classUnipotent₀ c) (S.classUnipotent c') → S.G E}
    (hρ : ∀ q : DoubleCoset.Quotient (S.classUnipotent₀ c : Set (S.G E))
      (S.classUnipotent c' : Set (S.G E)),
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') (ρ q) = q) {γ : S.G E}
    (hγ : S.termDisc γ ≠ 0) :
    ∑' (a : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c)) (b : S.classUnipotent c'),
      (if ρ ⟦(a : S.classUnipotent c) * γ * (b : S.G E)⁻¹⟧ =
          (a : S.classUnipotent c) * γ * (b : S.G E)⁻¹ then (1 : ℝ≥0∞) else 0) = 1 := by
  obtain ⟨u, hu, u', hu', h_rep⟩ : ∃ u ∈ S.classUnipotent₀ c, ∃ u' ∈ S.classUnipotent c',
      ρ (DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ) = u * γ * u' :=
    (DoubleCoset.eq ..).mp (hρ _).symm
  have rep_eq (a : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c))
      (b : S.classUnipotent c') :
      ρ ⟦(a : S.classUnipotent c) * γ * (b : S.G E)⁻¹⟧ = u * γ * u' := by
    have h_same : DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ =
        DoubleCoset.mk _ _ ((a : S.classUnipotent c) * γ * (b : S.G E)⁻¹) :=
      (DoubleCoset.eq ..).mpr ⟨_, a.prop, _, b⁻¹.prop, rfl⟩
    exact (congrArg ρ h_same.symm).trans h_rep
  simp_rw [rep_eq, ← ENNReal.tsum_prod]
  let a₀ : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c) := ⟨⟨u, hu.1⟩, hu⟩
  rw [tsum_eq_single (a₀, (⟨u', hu'⟩ : S.classUnipotent c')⁻¹) ?_]
  · simp [a₀]
  rintro ⟨a, b⟩ h_ne
  refine ite_eq_right fun h_eq ↦ h_ne ?_
  have h_conj : u⁻¹ * (a : S.classUnipotent c) * γ = γ * (u' * b) := by
    -- Multiply the equation of the representatives by `u⁻¹` on the left and by `b` on the right.
    simpa [mul_assoc] using congrArg (fun g : S.G E ↦ u⁻¹ * g * (b : S.G E)) h_eq.symm
  have hw : u' * b = 1 :=
    eq_one_of_mul_eq_mul_of_termDisc_ne_zero hγ (mul_mem (inv_mem hu) a.prop)
      (mul_mem hu' b.prop) h_conj
  rw [hw, mul_one, mul_eq_right, inv_mul_eq_one] at h_conj
  exact Prod.ext (Subtype.ext (Subtype.ext h_conj.symm))
    (Subtype.ext (eq_inv_of_mul_eq_one_right hw))

variable [S.IsAdmissible]

/-- **Open cell.** Let `W` be the cut Bessel vector on the archimedean points, so that the kernel
`S.besselKernel .cut γ y` is the tensor `W(y) ⊗ W(γ⁻¹ y)^*`; with `.full` the uncut vector is meant.
A point `y` lies in the cut at the place `v` (`InCut`) if its size `besselLength` is at most
`b ^ (6 n + 2)`, where `b = S.b` is the size parameter and `n = ϱ + 1`. It lies in the box
(`frameBox`) if it moves the frame to vectors `y⁻¹ f_a` of norm at most `ρ = S.frameBoxRadius`. Let
`γ` be near, that is, some `y` has `y` and `γ⁻¹ y` both reduced (`reducedPoints`) and in the cut at
every place, and let `𝗀(γ) = S.termDisc γ ≠ 0`. Let the weight `ω ≤ 1` be measurable, left invariant
under the fixer of the frame, and zero at the points that at some place lie in the cut but not in
the box. Let `ε²` bound the product over `v` of the numbers `pairingBoundSq`: explicit bounds for
the squared local pairing, in terms of the local value of `𝗀`, the radius `ρ`, and the degree and
the dimension of the Bessel system `S.besselSystem v`. Then the integral of `ω` times the cut kernel
has norm at most `ε` plus the integral of `ω` times the norm of the difference of the full and the
cut kernel. -/
theorem enorm_integral_besselKernel_le [HasPrimitiveRoot5040 E] {γ : S.G E} (h_near : S.IsNear γ)
    (h_disc : S.termDisc γ ≠ 0) {ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞}
    (ω_meas : Measurable ω) (ω_le : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁, ω y ≤ 1)
    (ω_inv : ∀ t y : NumberField.InfinitePlace E → 𝔰.G₁,
      (∀ v : NumberField.InfinitePlace E, t v ∈ besselFixer) → ω (t * y) = ω y)
    (ω_box : ∀ (y : NumberField.InfinitePlace E → 𝔰.G₁) (v : NumberField.InfinitePlace E),
      ω y ≠ 0 → InCut (y v) S.b → y v ∈ frameBox S.frameBoxRadius)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_pairingBound : ∏ v : NumberField.InfinitePlace E,
      pairingBoundSq (S.ratToInf γ v) (S.besselSystem v).deg
      S.frameBoxRadius (Fintype.card (S.besselSystem v).Index) ≤ ε ^ 2) :
    ‖∫ y : NumberField.InfinitePlace E → 𝔰.G₁, (ω y).toReal • S.besselKernel .cut γ y‖ₑ ≤
      .ofReal ε +
      ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁,
        ω y * ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ := by
  obtain ⟨y₀, y₀_boxed, γy₀_boxed⟩ :
      ∃ y₀ ∈ S.boxedPoints, (S.ratToInf γ)⁻¹ * y₀ ∈ S.boxedPoints := h_near
  have h_kernel (σ : FullOrCut) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselKernel σ γ y = BesselSystem.pairKernel S.besselSystem σ (S.ratToInf γ) y := by
    ext
    simp [besselKernel, besselFn, BesselSystem.pairKernel, prod_mul_distrib]
  have h_pos (v : NumberField.InfinitePlace E) :
      0 < RealPlace.gramDiscReal (realFrameGram (S.ratToInf γ v)) := by
    simp [gramDiscReal_realFrameGram_ratToInf, prod_pos, h_disc]
  have h_radius (_ : NumberField.InfinitePlace E) : S.b ^ (6 * 𝔰.n + 2) ≤ S.frameBoxRadius :=
    pow_right_mono₀ S.one_le_b (by nlinarith [S.ten_pow_five_le_varrho])
  -- Apply the bound for one pairing to the weight `φ`, which is `ω` with complex values.
  let φ (z : NumberField.InfinitePlace E → 𝔰.G₁) : ℂ := (ω z).toReal
  have φ_meas : Measurable φ := by fun_prop
  have φ_le (z : NumberField.InfinitePlace E → 𝔰.G₁) : ‖φ z‖ ≤ 1 := by
    simp [φ, toReal_le_of_le_ofReal, ω_le]
  have φ_enorm_le (z : NumberField.InfinitePlace E → 𝔰.G₁) : ‖φ z‖ₑ ≤ ω z := by
    simpa [φ, ← ofReal_norm] using ofReal_toReal_le
  have φ_inv (t z : NumberField.InfinitePlace E → 𝔰.G₁)
      (ht : ∀ v : NumberField.InfinitePlace E, t v ∈ besselFixer) : φ (t * z) = φ z := by
    simp only [φ, ω_inv t z ht]
  have φ_box (z : NumberField.InfinitePlace E → 𝔰.G₁)
      (hz : φ z • BesselSystem.pairKernel S.besselSystem .cut (S.ratToInf γ) z ≠ 0)
      (v : NumberField.InfinitePlace E) : z v ∈ frameBox S.frameBoxRadius := by
    have hω_ne : ω z ≠ 0 := fun h_zero ↦ hz (by simp [φ, h_zero])
    have h_kernel_ne : S.besselKernel .cut γ z ≠ 0 := by
      rw [h_kernel]
      exact right_ne_zero_of_smul hz
    obtain ⟨h_cut, -⟩ := inCut_of_besselKernel_ne_zero h_kernel_ne v
    exact ω_box z v hω_ne h_cut
  obtain ⟨-, h_integral_le⟩ := BesselSystem.enorm_integral_pairKernel_cut_le S.besselSystem h_pos
    (mem_frameBox_of_mem_boxedPoints y₀_boxed) (mem_frameBox_of_mem_boxedPoints γy₀_boxed)
    h_radius φ_meas φ_le φ_inv φ_box
  have h_sqrt_le : √(∏ v : NumberField.InfinitePlace E,
      pairingBoundSq (S.ratToInf γ v) (S.besselSystem v).deg
        S.frameBoxRadius (Fintype.card (S.besselSystem v).Index)) ≤ ε :=
    Real.sqrt_le_iff.2 ⟨hε, h_pairingBound⟩
  simp only [h_kernel, ← Complex.coe_smul]
  refine h_integral_le.trans ?_
  gcongr with z
  exact φ_enorm_le z

/-- Let `U_c` be the unipotent group of the class `c` and `U⁰_c` its subgroup fixing the frame. An
archimedean point `y` is reduced if the entries above the diagonal of the matrix `S.ratTriangle y`
lie in a fixed set of representatives modulo `M 𝓞_E`, and boxed if moreover its size `besselLength`
is at most `b ^ (6 n + 2)` at every infinite place. If the cut Bessel kernel `W(y) ⊗ W(γ⁻¹ y)^*` of
`γ` is nonzero at a reduced point `y`, then the double coset `U⁰_c γ U_c'` contains an element `δ`
that is near and is the chosen element of its smaller double coset `U⁰_c δ U⁰_c'`. -/
lemma exists_isNearRepresentative_of_besselKernel_ne_zero [HasPrimitiveRoot5040 E]
    {c c' : S.Classes} {γ : S.G E}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : S.besselKernel .cut γ y ≠ 0)
    (h_reduced : S.reducedIndicator y ≠ 0) :
    ∃ δ : S.G E, S.IsNearRepresentative c c' δ ∧
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') δ =
        DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ := by
  -- Translate `γ⁻¹ y` into the boxed points by `u ∈ U_c'` and take the chosen element of the orbit
  -- of `γ u⁻¹`.
  have h_cut (v : NumberField.InfinitePlace E) :
      InCut (y v) S.b ∧ InCut (((S.ratToInf γ)⁻¹ * y) v) S.b :=
    inCut_of_besselKernel_ne_zero hy v
  obtain ⟨u, hu, u_box⟩ : ∃ u ∈ S.classUnipotent c',
      S.ratToInf u * ((S.ratToInf γ)⁻¹ * y) ∈ S.boxedPoints :=
    exists_classUnipotent_mul_mem_boxedPoints c' fun v ↦ (h_cut v).2
  have h_near : S.IsNear (γ * u⁻¹) :=
    ⟨y, mem_boxedPoints_of_reducedIndicator_ne_zero h_reduced fun v ↦ (h_cut v).1,
      by simpa [mul_assoc] using u_box⟩
  obtain ⟨a, ha, b, ⟨hb_unip, hb_fix⟩, out_eq⟩ : ∃ a ∈ S.classUnipotent₀ c,
      ∃ b ∈ S.classUnipotent₀ c', (DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent₀ c')
        (γ * u⁻¹)).out = a * (γ * u⁻¹) * b :=
    (DoubleCoset.eq ..).1 (DoubleCoset.out_eq' ..).symm
  refine ⟨a * (γ * u⁻¹) * b,
    ⟨h_near.mul_of_mem_besselU0 ha.2 hb_fix, by simp [← out_eq]⟩, ?_⟩
  exact ((DoubleCoset.eq ..).2 ⟨a, ha, u⁻¹ * b, mul_mem (inv_mem hu) hb_unip, by group⟩).symm

/-- The element `𝗀(γ) = |D_{ϱ+1}|² - N² |D_ϱ|²` (`termDisc γ`), formed from the last two leading
minors of the matrix of frame products, is an algebraic integer for a rational `γ` in
`S.termsOver c s c'`. -/
lemma isIntegral_termDisc {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') : IsIntegral ℤ (S.termDisc γ) := by
  have h_entries : ∀ i k, IsIntegral ℤ (S.frameProducts γ i k) := isIntegral_frameProducts hγ
  have h_det : IsIntegral ℤ (S.frameProducts γ).det := IsIntegral.det h_entries
  have h_minor : IsIntegral ℤ (leadingMinor (S.frameProducts γ) 𝔰.top.castSucc) :=
    IsIntegral.det fun i k ↦ h_entries _ _
  exact (h_det.mul (map_isIntegral_int (starRingEnd E) h_det)).sub
    (((isIntegral_natCast ..).pow 2).mul (h_minor.mul (map_isIntegral_int (starRingEnd E) h_minor)))

/-- If no element `δ` of the double coset `U⁰_c γ U_c'` is near and the chosen element of
`U⁰_c δ U⁰_c'` (`IsNearRepresentative`), then the cut Bessel kernel of `γ` is zero at every reduced
point `y`, that is, wherever `S.reducedIndicator y ≠ 0`. -/
lemma toReal_smul_besselKernel_eq_zero [HasPrimitiveRoot5040 E] {c c' : S.Classes} {γ : S.G E}
    (h_none : ∀ δ : S.G E, S.IsNearRepresentative c c' δ →
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') δ ≠
        DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ)
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    (S.reducedIndicator y).toReal • S.besselKernel .cut γ y = 0 := by
  by_contra hy
  have h_kernel : S.besselKernel .cut γ y ≠ 0 := right_ne_zero_of_smul hy
  obtain ⟨δ, hδ, h_same⟩ := exists_isNearRepresentative_of_besselKernel_ne_zero (c := c) (c' := c')
    h_kernel fun h_zero ↦ hy (by simp [h_zero])
  exact h_none δ hδ h_same

open scoped Classical in
omit [S.IsAdmissible] in
/-- Let `T` be a set of rational elements with `𝗀 = termDisc ≠ 0` that is stable under the rational
unipotent group on both sides, and let `ρ` choose a representative in each double coset
`U⁰_c γ U_c'`, where `U_c = S.classUnipotent c` and `U⁰_c` is its subgroup fixing the frame. Let
`ω` be a partition of unity in boxes for `U_c` modulo `U⁰_c`; the property used is that
`∑ x ∈ U_c, a x * ω (x y) = 1` for every weight `a` whose sum over each coset `U⁰_c x` is one. Then
for `γ ∈ T` the sum of `ω (u y)` over the pairs `(u, u')` in `U_c × U_c'` for which `u γ u'⁻¹` is
the representative of its double coset equals one. -/
lemma tsum_representative_weight_eq_one {c c' : S.Classes}
    {ρ : DoubleCoset.Quotient (S.classUnipotent₀ c) (S.classUnipotent c') → S.G E}
    (hρ : ∀ q : DoubleCoset.Quotient (G := S.G E) (S.classUnipotent₀ c) (S.classUnipotent c'),
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') (ρ q) = q)
    {ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞} (hω : S.IsBoxPartitionOfUnity c ω)
    (hT : S.IsStable T) (h_disc : ∀ γ ∈ T, S.termDisc γ ≠ 0) {γ : S.G E} (hγ : γ ∈ T)
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    ∑' u : S.classUnipotent c × S.classUnipotent c',
      (if ρ ⟦u.1 * γ * u.2⁻¹⟧ = u.1 * γ * u.2⁻¹ then 1 else 0) *
        ω (S.ratToInf u.1 * y) = 1 := by
  let repIndicator (g : S.G E) : ℝ≥0∞ := if ρ ⟦g⟧ = g then 1 else 0
  let repCount (x : S.classUnipotent c) : ℝ≥0∞ :=
    ∑' u : S.classUnipotent c', repIndicator (x * γ * (u : S.G E)⁻¹)
  -- The sum of `repCount` over each coset of `U⁰_c` is one, so the partition property applies.
  have h_coset (x : S.classUnipotent c) :
      ∑' b : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c), repCount (b.1 * x) = 1 := by
    have h_mem : x * γ ∈ T := by simpa using (hT _ (inv_mem x.prop).1 1 (one_mem _) γ).2 hγ
    simpa [repCount, repIndicator, mul_assoc] using
      tsum_ite_representative_eq_one hρ (h_disc _ h_mem)
  have h_sum : ∑' x : S.classUnipotent c, repCount x * ω (S.ratToInf x * y) = 1 :=
    hω.tsum_mul_eq_one _ repCount h_coset
  rw [ENNReal.tsum_prod']
  simpa [repCount, repIndicator, ← ENNReal.tsum_mul_right] using h_sum

variable [HasPrimitiveRoot5040 E]

open scoped Classical in
/-- The bound for a block through the open cell. Let `T` be a set of rational elements, invariant
under the rational unipotent group on both sides, on which `𝗀 = termDisc` does not vanish. The terms
over `(c, s, c')` are the `γ` with `h_c⁻¹ γ h_c'` integral and of reduction `s`, and the cut block
`amplitudeSum` is the sum of their amplitudes, the integrals of the cut Bessel kernel against the
cutoffs of `c` and `c'`. Its norm is at most the covolume `ν = unipotentCovolume` times a sum over
the terms `γ` that are near and are the chosen element of their double coset `U⁰_c γ U⁰_c'`, with
`U⁰_c` the group of the unipotent elements of the class `c` fixing the frame. The summand is
`orbitBound j x`, an explicit constant times `x ^ (-k / 2)`, at the top rank `j = ⊤ = ϱ + 1` and at
`x = termDiscNorm γ`, the product of the `|𝗀(γ)|_v` over the infinite places. -/
lemma enorm_amplitudeSum_le_orbitBound_top (hT : S.IsStable T)
    (h_disc : ∀ γ ∈ T, S.termDisc γ ≠ 0) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'),
      if S.IsNearRepresentative c c' γ then
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound ⊤ (S.termDiscNorm γ))
      else 0 := by
  -- Unfold so that one term `γ` of each double coset `U⁰_c γ U_c'` contributes, with the weight
  -- `ω y`, the indicator of the reduced points. The open cell bounds its integral.
  let ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞ := S.reducedIndicator
  have hω_partition : S.IsBoxPartitionOfUnity c ω := isBoxPartitionOfUnity_reducedIndicator c
  have ω_box (y : NumberField.InfinitePlace E → 𝔰.G₁) (v : NumberField.InfinitePlace E)
      (hy : ω y ≠ 0) (h_cut : InCut (y v) S.b) : y v ∈ frameBox S.frameBoxRadius := by
    simpa only [mul_one] using
      hω_partition.mem_frameBox hy zero_le_one (h_cut.trans_eq (mul_one _).symm)
  -- In each double coset choose a representative, one with `IsNearRepresentative` if there is one.
  choose ρ hρ using fun q : DoubleCoset.Quotient (G := S.G E) (S.classUnipotent₀ c)
    (S.classUnipotent c') ↦
    exists_maximalFor_of_wellFoundedGT (fun γ : S.G E ↦
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ = q)
        (S.IsNearRepresentative c c') q.exists_rep
  let repIndicator (γ : S.G E) : ℝ≥0∞ := if ρ ⟦γ⟧ = γ then 1 else 0
  let φ (γ : S.G E) (y : NumberField.InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ := repIndicator γ * ω y
  have φ_sum (γ : S.G E) (hγ : γ ∈ T ∩ S.termsOver c s c')
      (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      ∑' u : S.classUnipotent c × S.classUnipotent c',
        φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1 :=
    tsum_representative_weight_eq_one (fun q ↦ (hρ q).1) hω_partition hT h_disc hγ.1 y
  obtain ⟨ω_meas, -, -, ω_le, ω_inv⟩ := hω_partition
  have h_cut_sum : HasSum (fun γ : ↥(T ∩ S.termsOver c s c') ↦
      ∫ y, (φ γ y).toReal • S.besselKernel .cut γ y) (S.amplitudeSum .cut T c s c') :=
    (hasSum_amplitudeSum_of_cutoff hT c s c' φ φ_sum (by fun_prop)).1
  have h_tail : ∑' γ : ↥(T ∩ S.termsOver c s c'), ∫⁻ y,
        φ γ y * ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ ≤
      ENNReal.ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) :=
    (hasSum_amplitudeSum_of_cutoff (side := .full) hT c s c' φ φ_sum (by fun_prop)).2.2
  grw [← h_cut_sum.tsum_eq, enorm_tsum_le_tsum_enorm]
  gcongr with γ
  obtain ⟨hγT, hγ_over⟩ := γ.2
  by_cases! h_rep : ρ ⟦γ⟧ ≠ γ
  · simp [φ, repIndicator, h_rep]
  -- Replace the weight by `ω y`, as `γ` is the representative.
  have φ_eq (y : NumberField.InfinitePlace E → 𝔰.G₁) : φ γ y = ω y := by
    simp [φ, repIndicator, h_rep]
  simp only [φ_eq]
  split_ifs with h_nearRep
  · -- `𝗀(γ)` is a nonzero algebraic integer, so its norm is at least `1`. The pairing bound and the
    -- cost of removing the cut are each at most half of the covolume times the orbit bound.
    have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
    obtain ⟨h_near, -⟩ := h_nearRep
    set ε : ℝ := S.unipotentCovolume * S.orbitBound ⊤ (S.termDiscNorm γ) / 2 with h_eps
    have h_one_le : 1 ≤ S.termDiscNorm γ :=
      one_le_prod_norm_Φ (isIntegral_termDisc hγ_over) (h_disc γ hγT)
    have hε : 0 ≤ ε := by simp only [h_eps, orbitBound]; positivity
    calc
      _ ≤ .ofReal ε + ∫⁻ y, ω y * ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ :=
        enorm_integral_besselKernel_le h_near (h_disc γ hγT) ω_meas ω_le ω_inv ω_box hε
          (prod_pairingBoundSq_le h_one_le)
      _ ≤ .ofReal ε + .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
        gcongr
        simpa only [φ_eq] using (ENNReal.le_tsum γ).trans h_tail
      _ ≤ .ofReal ε + .ofReal ε := by grw [h_near.inv_pow_le_orbitBound h_one_le]
      _ = _ := by rw [← ofReal_add hε hε, add_halves]
  · -- The representative `γ` is maximal for `IsNearRepresentative` in its double coset and fails
    -- it, so no element of the double coset satisfies it, and the integrand vanishes.
    obtain ⟨-, h_maximal⟩ := hρ ⟦γ⟧
    have h_none (δ : S.G E) (hδ : S.IsNearRepresentative c c' δ) :
        DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') δ ≠ DoubleCoset.mk _ _ γ.1 :=
      fun h_same ↦ h_nearRep (by simpa [h_rep] using h_maximal h_same (fun _ ↦ hδ) hδ)
    simp [ω, toReal_smul_besselKernel_eq_zero h_none]

/-- If the majorant `S.amplitudeMajorant .cut c c' γ` of the amplitude of `γ` over the classes `c`,
`c'` is nonzero, then `γ` is near (`S.IsNear γ`): some archimedean point `y` has both `y` and
`γ⁻¹ y` in `S.boxedPoints`. -/
lemma isNear_of_amplitudeMajorant_ne_zero {c c' : S.Classes} {γ : S.G E}
    (hγ : S.amplitudeMajorant .cut c c' γ ≠ 0) : S.IsNear γ := by
  by_contra h_far
  -- If `γ` is not near, the boxed cutoffs at `y` and at `γ⁻¹ y` are never both nonzero, so the
  -- first factor in the bound of Schur's test vanishes.
  have h_cutoff (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.boxCutoff c y = 0 ∨ S.boxCutoff c' ((S.ratToInf γ)⁻¹ * y) = 0 := by
    by_contra! ⟨hy, hγy⟩
    exact h_far ⟨y, mem_of_indicator_ne_zero hy, mem_of_indicator_ne_zero hγy⟩
  have h_integral : S.schurIntegral c c' γ 0 = 0 := by
    rw [schurIntegral, ← lintegral_zero]
    refine lintegral_congr fun y ↦ ?_
    obtain hy | hγy := h_cutoff y
    · simp [hy]
    · simp [schurWeight, hγy]
  have h_schur : S.amplitudeMajorant .cut c c' γ ^ 2 ≤
      S.schurIntegral c c' γ 0 * S.schurIntegral c' c γ⁻¹ 0 := amplitudeMajorant_sq_le 0
  rw [h_integral, zero_mul] at h_schur
  exact pow_ne_zero 2 hγ (nonpos_iff_eq_zero.1 h_schur)

open scoped Classical in
/-- The bound for a block by Schur's test. Write `D_l(γ)` for the leading minors of the matrix of
products of the frame with its image under `γ`, and `f` for the number of infinite places. Let `T`
be stable under the rational unipotent group on both sides, with all elements of cell rank `j`: the
two flags share vectors from the index `j` on, `D_j ≠ 0`, and `𝗀 = termDisc` is nonzero exactly if
`j = ϱ + 1`. Suppose that on `T` the norm `termDiscNorm` of `𝗀` is at most `N ^ f * minorNorm j`,
where `minorNorm j` is the norm of `D_j`, divided by `N ^ (2 f)` at the top rank, and that no
element of `T` over `(c, s, c')` has cell rank `0`. Then the cut block is at most the covolume
`ν = unipotentCovolume` times a sum over the near terms `γ` that are the chosen element of their
double coset `U⁰_c γ U⁰_c'` under the frame-fixing unipotent groups. The summand is
`orbitBound j x`, an explicit constant depending on `j` times `x ^ (-k / 2)`, at
`x = maxGauge j c c' γ`. -/
lemma enorm_amplitudeSum_le_of_termDiscNorm_le (hT : S.IsStable T) {j : Fin (𝔰.ϱ + 2)}
    (h_cell : ∀ γ ∈ T, S.HasCellRank j γ)
    (h_disc_le : ∀ γ ∈ T, S.termDiscNorm γ ≤ S.N ^ numInfPlaces E * S.minorNorm j γ)
    {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes}
    (h_not_rank_zero : ∀ γ ∈ T ∩ S.termsOver c s c', ¬S.HasCellRank 0 γ) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'),
      if S.IsNearRepresentative c c' γ then
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ))
      else 0 := by
  -- Sum the absolute amplitudes orbit by orbit.
  set X : Set (S.G E) := T ∩ S.termsOver c s c'
  have h_out (g : S.G E) : ∃ u ∈ S.classUnipotent₀ c, ∃ v ∈ S.classUnipotent₀ c',
      (DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent₀ c') g).out = u * g * v :=
    (DoubleCoset.eq ..).1 (DoubleCoset.out_eq' ..).symm
  choose u hu v hv out_eq using h_out
  have rep_mem (γ : X) : u γ * γ.1 * v γ ∈ X := by
    obtain ⟨hγT, hγ_over⟩ := γ.2
    -- An element of `U⁰_c` lies in the unipotent group and over the block `(c, 1, c)`.
    obtain ⟨⟨hu_mem, hu_over⟩, -⟩ := hu γ
    obtain ⟨⟨hv_mem, hv_over⟩, -⟩ := hv γ
    exact ⟨(hT (u γ)⁻¹ (inv_mem hu_mem) _ hv_mem _).2 hγT,
      by simpa using termsOver.mul (.mul hu_over hγ_over) hv_over⟩
  -- `rep γ` is the chosen element of the orbit of `γ`.
  let rep (γ : X) : X := ⟨u γ * γ.1 * v γ, rep_mem γ⟩
  have fibre_le (δ : X) : ∑' γ : rep ⁻¹' {δ}, S.amplitudeMajorant .cut c c' γ ≤
      if S.IsNearRepresentative c c' δ then
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' δ))
      else 0 := by
    by_cases h_zero : ∑' γ : rep ⁻¹' {δ}, S.amplitudeMajorant .cut c c' γ = 0
    · simp [h_zero]
    -- If the sum is nonzero, some `γ` in the orbit has a nonzero amplitude majorant, so it is near.
    obtain ⟨⟨γ, rfl⟩, hγ⟩ := ENNReal.summable.tsum_ne_zero_iff.1 h_zero
    have h_nearRep : S.IsNearRepresentative c c' (rep γ) :=
      ⟨(isNear_of_amplitudeMajorant_ne_zero hγ).mul_of_mem_besselU0 (hu γ).2 (hv γ).2,
        by simp [rep, ← out_eq]⟩
    obtain ⟨hδT, hδ_over⟩ := rep_mem γ
    have hj : j ≠ 0 := fun hj ↦ h_not_rank_zero γ γ.2 (by simpa [hj] using h_cell γ γ.2.1)
    have fibre_sub : Subtype.val '' (rep ⁻¹' {rep γ}) ⊆
        doubleCoset (rep γ : S.G E) (S.classUnipotent₀ c) (S.classUnipotent₀ c') := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : rep γ = u x * x.1 * v x := congrArg Subtype.val hx.symm
      rw [hx', doubleCoset_eq_of_mem (mem_doubleCoset.2 ⟨u x, hu x, v x, hv x, rfl⟩)]
      exact mem_doubleCoset_self ..
    rw [ite_eq_left h_nearRep]
    calc
      _ ≤ ∑' x : doubleCoset (rep γ : S.G E) (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
          S.amplitudeMajorant .cut c c' x :=
        (tsum_image _ Subtype.val_injective.injOn).symm.trans_le (tsum_mono_subtype _ fibre_sub)
      _ ≤ _ := tsum_amplitudeMajorant_orbit_le hδ_over (h_cell _ hδT) hj (h_disc_le _ hδT)
  calc
    _ ≤ ∑' γ : X, S.amplitudeMajorant .cut c c' γ :=
      enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun _ ↦ enorm_amplitude_le ..)
    _ = ∑' δ : X, ∑' γ : rep ⁻¹' {δ}, S.amplitudeMajorant .cut c c' γ := (tsum_fiberwise _ rep).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fibre_le

/-- Write `D_l(γ)` for the leading minors of the matrix of products of the frame with its image
under `γ`, `𝗀 = |D_{ϱ+1}|² - N² |D_ϱ|²`, and `f` for the number of infinite places. Let `T` be
stable under the rational unipotent group on both sides, with all elements of cell rank `j`, and
with no element of cell rank `0` over `(c, s, c')`. Then the cut block is at most the covolume
`ν = unipotentCovolume` times a sum over the near terms `γ` that are the chosen element of their
double coset `U⁰_c γ U⁰_c'` under the frame-fixing unipotent groups. The summand is
`orbitBound j x`, an explicit constant depending on `j` times `x ^ (-k / 2)`, at
`x = maxGauge j c c' γ`. This is the larger of the norm `termDiscNorm` of `𝗀` and
`N ^ f * minorNorm j`, divided by the lattice indices `isotropicRowsIndex j` at `h_c⁻¹ γ h_c'` and
at its inverse. The sum is empty, and the block is `0`, unless `s` agrees: integral unipotent `u`,
`u'` whose reductions satisfy `u s = s u'` have the same value of the character `unipotentChar`. -/
lemma enorm_amplitudeSum_le_orbitBound (hT : S.IsStable T) {j : Fin (𝔰.ϱ + 2)}
    (h_cell : ∀ γ ∈ T, S.HasCellRank j γ) {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes}
    (h_not_rank_zero : ∀ γ ∈ T ∩ S.termsOver c s c', ¬S.HasCellRank 0 γ) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤
      ∑' γ : {γ ∈ T ∩ S.termsOver c s c' | S.Agrees s ∧ S.IsNearRepresentative c c' γ},
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ)) := by
  classical
  -- On the set `K` of terms where the norm of `𝗀` exceeds `N ^ f * minorNorm j` use the open cell;
  -- off `K` use Schur's test.
  by_cases! hs : ¬S.Agrees s
  · simp [amplitudeSum_eq_zero_of_not_agrees, hT, hs]
  let bound (γ : S.G E) : ℝ≥0∞ :=
    if S.IsNearRepresentative c c' γ then .ofReal
      (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ))
    else 0
  let K : Set (S.G E) := {γ | S.N ^ numInfPlaces E * S.minorNorm j γ < S.termDiscNorm γ}
  have K_stable : S.IsStable K := by
    simp +contextual [IsStable, K, minorNorm, termDiscNorm,
      frameDisc_frameGram_inv_mul_mul_of_mem_besselU,
      leadingMinor_frameGram_besselU_mul]
  have on_stable : S.IsStable (T ∩ K) := fun u hu u' hu' γ ↦
    and_congr (hT u hu u' hu' γ) (K_stable u hu u' hu' γ)
  have off_stable : S.IsStable (T ∩ Kᶜ) := fun u hu u' hu' γ ↦
    and_congr (hT u hu u' hu' γ) (K_stable u hu u' hu' γ).not
  have disc_ne (γ : S.G E) (hγ : γ ∈ K) : S.termDisc γ ≠ 0 := fun h_zero ↦ hγ.out.not_ge <| by
    rw [show S.termDiscNorm γ = 0 by simp [termDiscNorm, h_zero], minorNorm]
    positivity
  have on_K : ‖S.amplitudeSum .cut (T ∩ K) c s c'‖ₑ ≤
      ∑' γ : ↥(T ∩ K ∩ S.termsOver c s c'), bound γ := by
    refine (enorm_amplitudeSum_le_orbitBound_top on_stable (fun γ hγ ↦ disc_ne γ hγ.2) c s c').trans
      (ENNReal.tsum_le_tsum fun ⟨γ, ⟨hγT, hγK⟩, _⟩ ↦ ?_)
    -- A term with `𝗀 ≠ 0` has the top cell rank, where the indices are `1`.
    have h_ne : S.termDisc γ ≠ 0 := disc_ne γ hγK
    obtain rfl : j = ⊤ := by grind [HasCellRank]
    simp [bound, (h_cell γ hγT).maxGauge_eq, isotropicRowsIndex_top, hγK.out.le]
  have off_K : ‖S.amplitudeSum .cut (T ∩ Kᶜ) c s c'‖ₑ ≤
      ∑' γ : ↥(T ∩ Kᶜ ∩ S.termsOver c s c'), bound γ :=
    enorm_amplitudeSum_le_of_termDiscNorm_le off_stable (fun γ hγ ↦ h_cell γ hγ.1)
      (fun γ hγ ↦ not_lt.1 hγ.2) fun γ ⟨⟨hγT, _⟩, hγ_over⟩ ↦ h_not_rank_zero γ ⟨hγT, hγ_over⟩
  calc
    _ ≤ ∑' γ : ↥(T ∩ Kᶜ ∩ S.termsOver c s c' ∪ T ∩ K ∩ S.termsOver c s c'), bound γ := by
      rw [amplitudeSum_eq_inter_compl_add_inter T K,
        ENNReal.summable.tsum_union_disjoint (by grind) ENNReal.summable]
      exact (enorm_add_le ..).trans (add_le_add off_K on_K)
    _ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'), bound γ := tsum_mono_subtype bound (by grind)
    _ = _ := by
      rw [_root_.tsum_subtype _ bound,
        _root_.tsum_subtype _ fun γ ↦
          ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ))]
      -- Both sums agree, as `s` agrees and `bound` vanishes unless `IsNearRepresentative` holds.
      exact tsum_congr fun γ ↦ by grind [indicator]

/-- For a function `f` on the rational elements, the amplitude sum `S.amplitudeSum side T c s c'` is
the sum over `i` of the amplitude sums `S.amplitudeSum side (T ∩ f ⁻¹' {i}) c s c'` of the
fibres. -/
lemma hasSum_amplitudeSum_fibre {side : FullOrCut} {ι : Type} (f : S.G E → ι) (c : S.Classes)
    (s : S.ResidueGL) (c' : S.Classes) :
    HasSum (fun i : ι ↦ S.amplitudeSum side (T ∩ f ⁻¹' {i}) c s c')
      (S.amplitudeSum side T c s c') := by
  refine ((summable_amplitude ..).hasSum.tsum_fiberwise
    fun γ : ↥(T ∩ S.termsOver c s c') ↦ f γ).congr_fun fun i ↦ ?_
  -- Both sides sum the amplitudes over the same set of terms, written in two ways.
  have h_set : {γ | f γ = i ∧ γ ∈ T ∧ γ ∈ S.termsOver c s c'} =
      T ∩ f ⁻¹' {i} ∩ S.termsOver c s c' := by grind
  simp [amplitudeSum, ← tsum_image, _root_.tsum_subtype, Set.image, h_set]

/-- For a function `f` on the rational elements, the norm of the cut amplitude sum
`S.amplitudeSum .cut T c s c'` is at most the sum over `i` of the norms of the cut amplitude sums of
the fibres `T ∩ f ⁻¹' {i}` at the same `c`, `s`, `c'`. -/
lemma enorm_amplitudeSum_le_tsum_fibre {ι : Type} (f : S.G E → ι) (c : S.Classes) (s : S.ResidueGL)
    (c' : S.Classes) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤ ∑' i : ι, ‖S.amplitudeSum .cut (T ∩ f ⁻¹' {i}) c s c'‖ₑ := by
  grw [← (hasSum_amplitudeSum_fibre f c s c').tsum_eq, enorm_tsum_le_tsum_enorm]

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- Every element of `Γ* = S.remainingTerms` has a cell rank, namely `S.cellRank γ`. -/
lemma hasCellRank_cellRank_of_mem {γ : S.G E} (hγ : γ ∈ S.remainingTerms) :
    S.HasCellRank (S.cellRank γ) γ := by
  obtain h_disc | ⟨h_agree, h_disc, -⟩ := mem_remainingTerms_iff.1 hγ
  · exact (hasCellRank_last h_disc).hasCellRank_cellRank
  · obtain ⟨j, hj⟩ := h_agree.exists_hasCellRank h_disc
    exact hj.hasCellRank_cellRank

/-- **Size.** Let `S` be admissible filling data of shape `𝔰` over a CM field `E` with a primitive
root of unity of order 5040. The set `Γ* = S.remainingTerms` consists of the rational `γ` with
`𝗀(γ) = S.termDisc γ ≠ 0`, and of those with `𝗀(γ) = 0` that move the isotropic space `⟨e₁, …, e_ϱ⟩`
and for which the unipotent character takes the same value at unipotent `u`, `u'` with `u γ = γ u'`.
Let `T ⊆ Γ*` be stable under the rational unipotent group on both sides, and fix classes `c`, `c'`
and a reduction `s`. The norm of the cut block is at most the covolume `unipotentCovolume` times the
sum of the sizes of the near representatives. These are the terms of `T` over the block that are
near, are the chosen element of their orbit `U⁰_c γ U⁰_c'` and have a cell rank `j ≤ ϱ + 1`,
provided `s` agrees; otherwise there are none. -/
theorem enorm_amplitudeSum_le_tsum_termSize (hT : S.IsStable T) (h_sub : T ⊆ S.remainingTerms)
    (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤
      ∑' γ : S.nearRepresentativesOver T c s c',
        .ofReal (S.unipotentCovolume * S.termSize c c' γ) := by
  -- Sort the terms by their cell rank and bound each part.
  let size (γ : S.G E) : ℝ≥0∞ := .ofReal (S.unipotentCovolume * S.termSize c c' γ)
  grw [enorm_amplitudeSum_le_tsum_fibre S.cellRank c s c', ← ENNReal.tsum_fiberwise _
    fun γ : S.nearRepresentativesOver T c s c' ↦ S.cellRank γ]
  refine ENNReal.tsum_le_tsum fun j ↦ ?_
  let part : Set (S.G E) := T ∩ S.cellRank ⁻¹' {j}
  have h_stable : S.IsStable part := by
    intro u hu u' hu' γ
    have h_iff (i : Fin (𝔰.ϱ + 2)) : S.HasCellRank i (u⁻¹ * γ * u') ↔ S.HasCellRank i γ :=
      S.isStable_hasCellRank i u hu u' hu' γ
    have cellRank_eq : S.cellRank (u⁻¹ * γ * u') = S.cellRank γ := by
      simp only [cellRank, h_iff]
    simp [part, cellRank_eq, hT u hu u' hu' γ]
  have h_cell : ∀ γ ∈ part, S.HasCellRank j γ := by
    rintro γ ⟨hγT, rfl : S.cellRank γ = j⟩
    exact hasCellRank_cellRank_of_mem (h_sub hγT)
  have h_not_rank_zero : ∀ γ ∈ part ∩ S.termsOver c s c', ¬S.HasCellRank 0 γ := by
    rintro γ ⟨⟨hγT, -⟩, -⟩ h_zero
    exact h_zero.normOnePairOccursFrom.notMem_remainingTerms (h_sub hγT)
  grw [enorm_amplitudeSum_le_orbitBound h_stable h_cell h_not_rank_zero]
  -- The terms in this bound are near representatives of `T` with cell rank `j`.
  let near : Set (S.G E) :=
    {γ ∈ part ∩ S.termsOver c s c' | S.Agrees s ∧ S.IsNearRepresentative c c' γ}
  have near_mem (γ : near) : (γ : S.G E) ∈ S.nearRepresentativesOver T c s c' := by
    obtain ⟨γ, ⟨⟨hγT, -⟩, hγ_over⟩, hs, h_nearRep⟩ := γ
    exact ⟨⟨hγT, hγ_over⟩, hs, h_nearRep, hasCellRank_cellRank_of_mem (h_sub hγT)⟩
  have near_rank (γ : near) : S.cellRank γ = j := by
    obtain ⟨γ, ⟨⟨-, h_rank⟩, -⟩, -⟩ := γ
    exact h_rank
  let incl (γ : near) : (fun γ : S.nearRepresentativesOver T c s c' ↦ S.cellRank γ) ⁻¹' {j} :=
    ⟨⟨γ, near_mem γ⟩, near_rank γ⟩
  have incl_injective : incl.Injective := fun γ γ' h ↦ by grind
  calc
    _ = ∑' γ : near, size γ := tsum_congr fun γ ↦ by simp only [size, termSize, near_rank γ]
    _ ≤ _ := tsum_comp_le_tsum_of_injective incl_injective fun γ ↦ size γ.1

end New.Filling

end SizeOfBlocks
