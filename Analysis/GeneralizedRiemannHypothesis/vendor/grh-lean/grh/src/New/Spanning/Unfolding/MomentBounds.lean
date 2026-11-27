import New.Spanning.MainTerm.EnergyEstimate
import New.Spanning.SecondMoment.PositiveType
import New.Spanning.Unfolding.SquareExpansion

/-!
# The second moment over the whole group

This file proves the bound on the sum of the second moments of the operators `P_s = P* s P` over the
whole group, stated in terms of their blocks. It bounds the contribution of the cosets of `R̄₀` and
that of the elements that are not open.

The blocks of `P_s` are the complex conjugates of the sums `amplitudeSum` over all terms, divided by
`unipotentCovolume`, so `‖P_s‖²` (Hilbert–Schmidt norm) is the `secondMoment` of these sums at `s`.
In the same way the terms in the Bessel subgroup `R₀ = besselS` give `r_ψ(s)`, and those off it give
`P_s - r_ψ(s)`. The operator `r_ψ(s)` is `New.Filling.besselTranslate`; the passage from operators
to blocks is `New.Filling.HasAmplitudeBlocks`.

We write `R̄₀` for `reducedImage besselS`, `D_X` for `sourceDim`, `𝒟_id` for `identitySecondMoment`,
`𝒟_main` for `mainSecondMoment`, `b` for the parameter `S.b` of the filling, `p_i` for
`levelPrime i`, `M = p₀ p₁` for the level, `f` for the number of infinite places, `k = |κ|`,
`n = ϱ + 1` for the length of the frame, `e₁` for its vector of index `0` and `δ_l` for the leading
minors of `frameGram`. In `InScalarCoset ζ s` the scalar `ζ` is an integral adele, acting through
its residues.

## Main definitions and results

* `New.Filling.sum_secondMoment_le`: `∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main`, if `s ↦ ‖P_s‖²` has positive
  type and `‖P_1‖² ≤ 2 D_X`.
* `New.Filling.secondMoment_univ_eq_secondMoment_compl_besselS`: if `Ω` is disjoint from the
  reduction `R̄₀` of the Bessel subgroup, then the terms in the Bessel subgroup give `0` over `Ω`,
  so all terms and the terms off the Bessel subgroup have the same second moment over `Ω`.

Notions from other files:
* `termsOver c s c'`: the rational `γ` such that `h_c⁻¹ γ h_c'` (`translateByClassReps`) is integral
  with reduction `s`; such a `γ` lies over the block `(c, s, c')`.
* `amplitudeSum side T c s c'`: the sum of the amplitudes of the elements of `T` over that block.
* `secondMoment A Ω`: the sum of `‖A c s c'‖² / unipotentCovolume²` over all classes `c`, `c'` and
  `s ∈ Ω`.
* `reducedImage A`: the image in the finite group `ResidueGL` of the integral elements of `A`.
-/

namespace New

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

namespace Filling

/-! ### The second moment over the whole group -/

/-- The second moment of a family of blocks at one element `σ`: `unipotentCovolume⁻²` times the sum
of the squared norms of the blocks over `σ`. -/
lemma secondMoment_singleton {V : Type} [NormedAddCommGroup V]
    (A : S.Classes → S.ResidueGL → S.Classes → V) (σ : S.ResidueGL) :
    secondMoment A {σ} = ∑ c : S.Classes, ∑ c' : S.Classes,
      ‖A c σ c'‖ ^ 2 / S.unipotentCovolume ^ 2 :=
  sum_congr rfl fun c _ ↦ sum_congr rfl fun c' _ ↦
    sum_eq_single_of_mem σ (by simp) (by simp +contextual)

/-- The second moment of a family of blocks over a set `Ω` is the sum of its second moments at the
elements of `Ω`. -/
lemma secondMoment_eq_sum_secondMoment_singleton {V : Type} [NormedAddCommGroup V]
    (A : S.Classes → S.ResidueGL → S.Classes → V) (Ω : Set S.ResidueGL) [DecidablePred (· ∈ Ω)] :
    secondMoment A Ω = ∑ s : S.ResidueGL with s ∈ Ω, secondMoment A {s} := by
  simp only [secondMoment_singleton]
  rw [secondMoment, sum_comm_cycle]
  congr!

/-- If `Ω` is disjoint from the reduction `R̄₀` of the Bessel subgroup, then the terms in the Bessel
subgroup give `0` over `Ω`, so all terms and the terms off the Bessel subgroup have the same second
moment over `Ω`. -/
lemma secondMoment_univ_eq_secondMoment_compl_besselS [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {Ω : Set S.ResidueGL} (hΩ : ∀ s ∈ Ω, s ∉ S.reducedImage besselS) :
    secondMoment (S.amplitudeSum .full Set.univ) Ω =
      secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω := by
  classical
  rw [amplitudeSum_eq_inter_compl_add_inter Set.univ (S.ratMiddle E).besselS, Set.univ_inter,
    Set.univ_inter]
  refine sum_congr rfl fun c _ ↦ sum_congr rfl fun c' _ ↦ sum_congr rfl fun s hs ↦ ?_
  simp only [Pi.add_apply, amplitudeSum_besselS_eq_zero (hΩ s (mem_filter.1 hs).2), add_zero]

open scoped Classical in
/-- At most `M ^ f #R̄₀` elements lie in a coset of the reduction `R̄₀` of the Bessel subgroup by an
integral scalar (`InScalarCoset`), as only the residues of the scalar at the chosen places
matter. -/
lemma card_inScalarCoset_le : #{s : S.ResidueGL | ∃ ζ : Ô E, S.InScalarCoset ζ s} ≤
    S.M ^ Core.numInfPlaces E * Nat.card (S.reducedImage besselS) := by
  -- An element `s = ζ t` is determined by the residues of `ζ` and by `t`.
  have h_scalar (s : {s : S.ResidueGL // ∃ ζ : Ô E, S.InScalarCoset ζ s}) :
      ∃ (ζ : Ô E) (t : S.ResidueGL), t ∈ S.reducedImage besselS ∧ ∀ (i : Fin 2)
        (w : S.chosenPlaces i),
        (s.1 i w).1 = New.reduceAt w.1 ζ • (t i w).1 := s.2
  choose ζ t ht h_eq using h_scalar
  let φ (s : {s : S.ResidueGL // ∃ ζ : Ô E, S.InScalarCoset ζ s}) :
      (∀ (i : Fin 2) (w : S.chosenPlaces i), ResField w.1) × S.reducedImage besselS :=
    (fun _ w ↦ New.reduceAt w.1 (ζ s), ⟨t s, ht s⟩)
  have hφ : φ.Injective := fun s s' h ↦ by
    obtain ⟨h_res, h_t⟩ := Prod.ext_iff.1 h
    refine Subtype.ext (funext₂ fun i w ↦ Units.ext ?_)
    rw [h_eq, h_eq, show New.reduceAt w.1 (ζ s) = New.reduceAt w.1 (ζ s') from congrFun₂ h_res i w,
      show t s = t s' from congrArg Subtype.val h_t]
  rw [← Fintype.card_subtype, card_eq_nat_card]
  refine (Nat.card_le_card_of_injective φ hφ).trans_eq ?_
  simp only [Nat.card_prod, Nat.card_pi, card_resField_eq_levelPrime, prod_const, card_univ,
    S.card_chosenPlaces, Fin.prod_univ_two, mul_pow]

/-- Let the filling `S` be admissible (`IsAdmissible`), which includes the bound
`b^(11kf) 𝒟_id ≤ 𝒟_main`. Then `b^(5kf) 𝒟_id ≤ b^(-6ka) 𝒟_main` for any set `places` of chosen
places above the level prime `p₀` (`chosenPlaces 0`), where `a = #places`. -/
lemma pow_mul_identitySecondMoment_le_mul_mainSecondMoment [hS : S.IsAdmissible]
    (places : Finset (S.chosenPlaces 0)) :
    S.b ^ (5 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #places * S.mainSecondMoment := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_places : #places ≤ Core.numInfPlaces E :=
    places.card_le_univ.trans_eq (S.card_chosenPlaces 0)
  rw [inv_pow, le_inv_mul_iff₀ (by positivity)]
  calc _ ≤ (S.b ^ (6 * 𝔰.k)) ^ Core.numInfPlaces E *
        (S.b ^ (5 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment) := by
        gcongr
        exact one_le_pow₀ hb
    _ = S.b ^ (11 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment := by ring
    _ ≤ S.mainSecondMoment := hS.mul_identitySecondMoment_le

/-- For each chosen place `w` above `p₀`, let `vectors w` be a nonzero vector of the span of the
frame modulo `w`. If its Boolean is `true`, it is taken modulo the conjugate of `w` instead. Let `s`
fix all of them. So `meetNorm s`, the product of the norms of the places at which `s` meets, is at
least `levelPrime 0 ^ numInfPlaces E`. -/
lemma levelPrime_pow_le_meetNorm_of_mem_fixer [S.IsAdmissible]
    {vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w} {s : S.ResidueGL}
    (hs : s ∈ S.fixer univ vectors) : S.levelPrime 0 ^ Core.numInfPlaces E ≤ S.meetNorm s := by
  classical
  let φ (w : S.chosenPlaces 0) : (Σ j : Fin 2, S.chosenPlaces j) × Bool := (⟨0, w⟩, (vectors w).1)
  have hφ : φ.Injective := fun w w' h ↦ by simpa [φ] using congrArg Prod.fst h
  have h_meet : ∀ p ∈ univ.image φ, S.MeetsAt s p :=
    forall_mem_image.2 fun w hw ↦ meetsAt_of_mem_vectorFixer (mem_fixer.1 hs w hw)
  refine le_trans ?_ (prod_le_meetNorm h_meet)
  rw [prod_image hφ.injOn]
  simp [φ, S.card_chosenPlaces]

open scoped Classical in
/-- Let `E` contain a primitive `5040`-th root of unity and let the filling data `S` be admissible
(`IsAdmissible`). For `s` in `ResidueGL`, write `‖P_s‖²` for the `secondMoment` at `s` of the
amplitude sums of all terms. If `‖P_s‖² ≤ 2 D_X` for all `s`, with `D_X = sourceDim`, then the sum
of `‖P_s‖²` over the cosets of the reduction `R̄₀` of the Bessel subgroup by integral scalars
(`InScalarCoset`) is at most `2 M ^ f 𝒟_id`. -/
lemma sum_secondMoment_inScalarCoset_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (h_le : ∀ s : S.ResidueGL, secondMoment (S.amplitudeSum .full Set.univ) {s} ≤ 2 * S.sourceDim) :
    ∑ s : S.ResidueGL with ∃ ζ : Ô E, S.InScalarCoset ζ s,
        secondMoment (S.amplitudeSum .full Set.univ) {s} ≤
      2 * S.M ^ Core.numInfPlaces E * S.identitySecondMoment :=
  calc _ ≤ #{s : S.ResidueGL | ∃ ζ : Ô E, S.InScalarCoset ζ s} • (2 * S.sourceDim : ℝ) :=
        sum_le_card_nsmul _ _ _ fun s _ ↦ h_le s
    _ ≤ _ := by
      grw [nsmul_eq_mul, card_inScalarCoset_le, identitySecondMoment]
      exact le_of_eq (by push_cast; ring)

/-- Let the filling `S` be admissible (`IsAdmissible`). Then `8 M ^ f 𝒟_id ≤ b^(-6kf) 𝒟_main`, as
`b^(11kf) 𝒟_id ≤ 𝒟_main`, `8 M ^ f ≤ b (b²³) ^ f` and `23 f + 1 ≤ 5 k f`. -/
lemma eight_mul_M_pow_mul_identitySecondMoment_le [S.IsAdmissible] :
    8 * S.M ^ Core.numInfPlaces E * S.identitySecondMoment ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment := by
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_exp : 23 * Core.numInfPlaces E + 1 ≤ 5 * (𝔰.k * Core.numInfPlaces E) := by
    nlinarith [S.thousand_mul_le_k, NeZero.one_le (n := Core.numInfPlaces E)]
  have hb : 1000 ≤ S.b := S.thousand_le_b
  calc _ ≤ S.b * (S.b ^ 23) ^ Core.numInfPlaces E * S.identitySecondMoment := by
        grw [M_le_b_pow, show (8 : ℝ) ≤ S.b by linarith]
    _ ≤ S.b ^ (5 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment := by
      grw [← pow_mul, ← pow_succ', pow_le_pow_right₀ S.one_le_b h_exp]
    _ ≤ _ := pow_mul_identitySecondMoment_le_mul_mainSecondMoment univ

/-- Let the filling `S` be admissible (`IsAdmissible`). The bound `(b^(2f) / p₀^f)^k 𝒟_main` on sums
over links is at most an eighth of `b^(-6kf) 𝒟_main`, as `b¹⁰ ≤ p₀` (`le_levelPrime`). -/
lemma div_levelPrime_pow_mul_mainSecondMoment_le [S.IsAdmissible] :
    (S.b ^ (2 * Core.numInfPlaces E) / (S.levelPrime 0 ^ Core.numInfPlaces E : ℕ)) ^ 𝔰.k *
        S.mainSecondMoment ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment / 8 := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_eight : 8 ≤ S.b ^ (2 * (𝔰.k * Core.numInfPlaces E)) := by
    grw [← S.forty_le_k_mul_numInfPlaces, ← two_le_b]
    norm_num
  calc _ ≤ (S.b ^ (2 * Core.numInfPlaces E) / (S.b ^ 10) ^ Core.numInfPlaces E) ^ 𝔰.k *
        S.mainSecondMoment := by grw [Nat.cast_pow, ← le_levelPrime]
    _ = (S.b ^ (2 * (𝔰.k * Core.numInfPlaces E)))⁻¹ *
        ((S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment) := by
      rw [card_univ, S.card_chosenPlaces, inv_pow, div_pow]
      field
    _ ≤ _ := by grw [← div_eq_inv_mul, h_eight]

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). Let `D_X = sourceDim` be the number of pairs of a class and a coordinate, and
suppose `‖P_s‖² ≤ 2 D_X` for all `s`. At each of the `f` chosen places `w` above `p₀`, `vectors w`
is a `FrameVector`: a nonzero vector in the span of the frame `e₁, …, e_ϱ, z`, taken modulo `w` or
modulo its conjugate. Then the sum over the group `fixer` of the `s` that fix all these vectors
satisfies `∑ ‖P_s‖² ≤ b^(-6kf) 𝒟_main`. -/
lemma secondMoment_fixer_univ_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w)
    (h_le : ∀ s : S.ResidueGL, secondMoment (S.amplitudeSum .full Set.univ) {s} ≤ 2 * S.sourceDim) :
    secondMoment (S.amplitudeSum .full Set.univ) (S.fixer univ vectors) ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment := by
  -- The scalar cosets are small. Off them the expansion of the squares applies, and its sums over
  -- links are small because every `s` in the fixer meets at `f` places above `p₀`.
  classical
  have hb : 1 ≤ S.b := S.one_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  set target : ℝ := (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment
  have h_id_le_target : 8 * S.M ^ Core.numInfPlaces E * S.identitySecondMoment ≤ target :=
    eight_mul_M_pow_mul_identitySecondMoment_le
  let β (s : S.ResidueGL) : ℝ := secondMoment (S.amplitudeSum .full Set.univ) {s}
  let Ω : Set S.ResidueGL := {s | s ∈ S.fixer univ vectors ∧ ¬∃ ζ : Ô E, S.InScalarCoset ζ s}
  -- The scalar cosets have at most `M ^ f #R̄₀` elements, each with `β s ≤ 2 D_X`.
  have h_cosets : ∑ s : S.ResidueGL with ∃ ζ : Ô E, S.InScalarCoset ζ s, β s ≤ target / 2 :=
    (sum_secondMoment_inScalarCoset_le h_le).trans (by linarith [show 0 ≤ target by positivity])
  -- On `Ω` the sums over links give at most `linkBound ≤ b^(-8kf) 𝒟_main`, as `b¹⁰ ≤ p₀`.
  let linkBound : ℝ := (S.b ^ (2 * Core.numInfPlaces E) /
    (S.levelPrime 0 ^ Core.numInfPlaces E : ℕ)) ^ 𝔰.k * S.mainSecondMoment
  have h_links : linkBound ≤ target / 8 := div_levelPrime_pow_mul_mainSecondMoment_le
  have h_id : (S.b ^ 15)⁻¹ ^ 2 * S.identitySecondMoment ≤ target / 8 := by
    have h_inv : (S.b ^ 15)⁻¹ ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hb))
    grw [h_inv, ← h_id_le_target, ← one_le_pow₀ (Nat.one_le_cast.2 (one_le_two.trans two_le_M))]
    linarith
  have h_rest : ∑ s : S.ResidueGL with s ∈ Ω, β s ≤ target / 2 := by
    have h_avoid : S.AvoidsScalarCosets Ω := fun ζ h_int _ _ s hs h ↦ hs.2 ⟨⟨ζ, h_int⟩, h⟩
    have h_off : ∀ s ∈ Ω, s ∉ S.reducedImage besselS :=
      fun s hs h ↦ hs.2 ⟨1, inScalarCoset_one h⟩
    calc _ = secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω := by
          rw [← secondMoment_eq_sum_secondMoment_singleton,
            secondMoment_univ_eq_secondMoment_compl_besselS h_off]
      _ ≤ (√linkBound + (S.b ^ 15)⁻¹ * √S.identitySecondMoment) ^ 2 := by
        rw [← Real.sqrt_le_left (by positivity)]
        exact sqrt_secondMoment_compl_besselS_le h_avoid (by positivity)
          (linkSecondMoment_le_of_le_meetNorm
          (pow_ne_zero _ (S.levelPrime_prime_and_ne 0).1.ne_zero)
          fun s hs ↦ levelPrime_pow_le_meetNorm_of_mem_fixer hs.1)
      _ ≤ 2 * (linkBound + (S.b ^ 15)⁻¹ ^ 2 * S.identitySecondMoment) := by
        grw [add_sq_le, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt h_id_nonneg]
      _ ≤ target / 2 := by linarith [h_links, h_id]
  calc _ = ∑ s : S.ResidueGL with s ∈ S.fixer univ vectors ∧ ∃ ζ : Ô E, S.InScalarCoset ζ s, β s +
        ∑ s : S.ResidueGL with s ∈ Ω, β s := by
        rw [secondMoment_eq_sum_secondMoment_singleton,
          ← sum_filter_add_sum_filter_not _ fun s : S.ResidueGL ↦ ∃ ζ : Ô E, S.InScalarCoset ζ s,
          filter_filter, filter_filter]
        congr!
    _ ≤ ∑ s : S.ResidueGL with ∃ ζ : Ô E, S.InScalarCoset ζ s, β s + ∑ s : S.ResidueGL with s ∈ Ω,
      β s := by
      gcongr
      · exact fun s _ _ ↦ secondMoment_nonneg
      · exact And.right
    _ ≤ target := by linarith [h_cosets, h_rest]

/-- Let the filling `S` be admissible (`IsAdmissible`) and assume Weil data on `E`. Over the open
`s` that fix the given nonzero vectors of the span of the frame at a set of `a` chosen places above
`p₀` (`fixer`) we have `∑ ‖P_s‖² ≤ (1 + 4 b⁻⁴) b^(-6ka) 𝒟_main`. The element `s` is open if at some
chosen place above `p₀` no leading minor of size less than `n = ϱ + 1` of `frameGram`, the matrix of
the products of the frame with its image under `s`, vanishes. -/
lemma secondMoment_fixer_isOpenElement_le [S.IsAdmissible] [WeilData E]
    (places : Finset (S.chosenPlaces 0))
    (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w) :
    secondMoment (S.amplitudeSum .full Set.univ)
        {s : S.ResidueGL | s ∈ S.fixer places vectors ∧ S.IsOpenElement s} ≤
      (1 + 4 / S.b ^ 4) * ((S.b ^ (6 * 𝔰.k))⁻¹ ^ #places * S.mainSecondMoment) := by
  -- No open element lies in a scalar coset, so the expansion and the main term apply.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have hb₁ : 1 ≤ S.b := S.one_le_b
  set target : ℝ := (S.b ^ (6 * 𝔰.k))⁻¹ ^ #places * S.mainSecondMoment with h_target_def
  have h_id : S.identitySecondMoment ≤ target := (le_mul_of_one_le_left identitySecondMoment_nonneg
    (one_le_pow₀ hb₁)).trans (pow_mul_identitySecondMoment_le_mul_mainSecondMoment places)
  have h_target_nonneg : 0 ≤ target := identitySecondMoment_nonneg.trans h_id
  set Ω : Set S.ResidueGL := {s | s ∈ S.fixer places vectors ∧ S.IsOpenElement s}
  have h_avoid : S.AvoidsScalarCosets Ω :=
    fun ζ h_int _ _ s hs h_coset ↦ h_coset.not_isOpenElement hs.2
  have h_off : ∀ s ∈ Ω, s ∉ S.reducedImage besselS :=
    fun s hs h ↦ (inScalarCoset_one h).not_isOpenElement hs.2
  -- With `x = b⁻⁴` we have `(1 + x)^(1/2) ≤ 1 + x / 2` and `b⁻¹⁵ ≤ x / 2`.
  have hx₀ : 0 ≤ (S.b ^ 4)⁻¹ := by positivity
  have hx : (S.b ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hb₁)
  have h_small : (S.b ^ 15)⁻¹ ≤ (S.b ^ 4)⁻¹ / 2 := by
    field_simp
    linarith [le_self_pow₀ hb₁ (by norm_num : 11 ≠ 0)]
  have h_bound : √(secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω) ≤
      (1 + (S.b ^ 4)⁻¹) * √target :=
    calc _ ≤ √((1 + (S.b ^ 4)⁻¹) * target) + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
          refine sqrt_secondMoment_compl_besselS_le h_avoid (by positivity) ?_
          rw [h_target_def, ← mul_assoc]
          exact linkSecondMoment_isOpenElement_le places vectors
      _ ≤ (1 + (S.b ^ 4)⁻¹ / 2) * √target + (S.b ^ 4)⁻¹ / 2 * √target := by
        grw [Real.sqrt_mul (by positivity), Real.sqrt_one_add_le (by linarith), h_small, h_id]
      _ = (1 + (S.b ^ 4)⁻¹) * √target := by ring
  calc _ ≤ (1 + (S.b ^ 4)⁻¹) ^ 2 * target := by
        grw [secondMoment_univ_eq_secondMoment_compl_besselS h_off, (Real.sqrt_le_iff.1 h_bound).2,
          mul_pow, Real.sq_sqrt h_target_nonneg]
    _ ≤ (1 + 4 / S.b ^ 4) * target := by
      gcongr
      rw [div_eq_mul_inv]
      nlinarith

/-- Let the filling `S` be admissible (`IsAdmissible`). For `l < n = ϱ + 1` we have
`p₀ ^ (l + r / 2) ≤ b ^ (6 k)`. Here `p₀ = levelPrime 0`, `b = S.b`, `k = |κ|`, and `r` is the rank
of the space, that is, the number of indices in `𝔰.BesselIndex`. -/
lemma levelPrime_pow_mul_sqrt_le [S.IsAdmissible] (l : Fin 𝔰.n) :
    (S.levelPrime 0 : ℝ) ^ l.val * √(S.levelPrime 0 ^ card 𝔰.BesselIndex) ≤ S.b ^ (6 * 𝔰.k) := by
  -- Square, and use `p₀ ≤ b¹¹`, `r = k + 2 n - 1` and `2000 n ≤ k`.
  have hb : 1 ≤ S.b := S.one_le_b
  have h_exp : 11 * (l.1 * 2 + card 𝔰.BesselIndex) ≤ 6 * 𝔰.k * 2 := by
    have h_rank : card 𝔰.BesselIndex = 2 * 𝔰.ϱ + 𝔰.k + 1 := by simp +arith
    linarith [S.thousand_mul_le_k, (l.2 : l.1 < 𝔰.ϱ + 1)]
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  calc _ = (S.levelPrime 0 : ℝ) ^ (l.1 * 2 + card 𝔰.BesselIndex) := by
        rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_add]
    _ ≤ S.b ^ (11 * (l.1 * 2 + card 𝔰.BesselIndex)) := by grw [S.levelPrime_le 0, ← pow_mul]
    _ ≤ (S.b ^ (6 * 𝔰.k)) ^ 2 := by grw [h_exp, ← pow_mul]

open scoped Classical in
/-- Let the filling `S` be admissible (`IsAdmissible`), with large parameter `b = S.b` and with
`k = 𝔰.k` the rank of `X₀`. Let `β ≥ 0` on `ResidueGL` have positive type. Let `Γ` be a subgroup and
`w` a chosen place above `p₀`. The frame consists of the `ϱ + 1` basis vectors `e₁, …, e_ϱ, z`, and
a `FrameVector` at `w` is a nonzero vector of their span, taken modulo `w` or modulo its conjugate.
Suppose that the stabilizer in `Γ` of any such vector carries at most a proportion `b^(-6k)` of the
sum of `β` over `Γ`. Let `l < 𝔰.n`, and let `δ_l` be the leading minor of size `l` of the
`frameGram` of the component `s 0 w` over the residue field at `w`. Then the `s` in `Γ` with
`δ_l = 0` carry at most a proportion `3 / b¹⁰`. -/
lemma sum_leadingMinor_eq_zero_le [S.IsAdmissible] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {β : S.ResidueGL → ℝ} (h_nonneg : ∀ s : S.ResidueGL, 0 ≤ β s)
      {u : S.ResidueGL → V}
    (h_posType : ∀ a b : S.ResidueGL, ⟪u a, u b⟫_ℂ = β (a⁻¹ * b)) {Γ : Subgroup S.ResidueGL}
    {w : S.chosenPlaces 0}
    (h_stab : ∀ d : S.FrameVector w, ∑ s : Γ with s.val ∈ S.vectorFixer w d, β s.val ≤
      (∑ s : Γ, β s.val) / S.b ^ (6 * 𝔰.k)) (l : Fin 𝔰.n) :
    ∑ s : Γ with leadingMinor ((S.latticeMiddle (ResField (w : FinPlace E))).frameGram
        (s.val 0 w).val) l.castSucc = 0, β s.val ≤
      3 * (∑ s : Γ, β s.val) / S.b ^ 10 := by
  -- `δ_l` is the determinant of the pairings of the first `l` frame vectors with their images.
  have hb : 0 < S.b := b_pos
  set total : ℝ := ∑ s : Γ, β s.1
  set stabFactor : ℝ := S.b ^ (6 * 𝔰.k)
  have h_total_nonneg : 0 ≤ total := sum_nonneg fun s _ ↦ h_nonneg s
  -- The group `Γ` acts on the lattice modulo `w`; the residue field has `p₀` elements.
  let π : Γ →* GL 𝔰.BesselIndex (ResField w.1) := MonoidHom.mk' (fun s ↦ s.1 0 w) (by simp)
  have h_card : card (ResField w.1) = S.levelPrime 0 :=
    card_eq_nat_card.trans (card_resField_eq_levelPrime S 0 w)
  -- The columns of `e` are the first `l` frame vectors, those of `J * e` their linear forms.
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField w.1) :=
    (S.latticeMiddle (ResField w.1)).splitGram
  let e : Matrix 𝔰.BesselIndex (Fin l.castSucc) (ResField w.1) :=
    frameImage 1 * inclMatrix (ResField w.1) (Fin.castLE l.castSucc.is_le)
  have h_det (s : Γ) : ((J * e)ᵀ * (π s).1 * e).det =
      leadingMinor ((S.latticeMiddle (ResField w.1)).frameGram (s.1 0 w).1) l.castSucc := by
    let ι : Fin l.castSucc → 𝔰.BesselIndex := 𝔰.besselFrame ∘ Fin.castLE l.castSucc.is_le
    rw [show e = inclMatrix (ResField w.1) ι from mul_inclMatrix _ _, mul_inclMatrix,
      mul_inclMatrix, transpose_submatrix, transpose_splitGram]
    rfl
  -- The stabilizer of a vector, or of a form, fixes a vector modulo `w`, or modulo its conjugate.
  have h_le_of_fixes (d : S.FrameVector w) (p : Γ → Prop) [DecidablePred p]
      (hp : ∀ s : Γ, p s → s.1 ∈ S.vectorFixer w d) :
      ∑ s : Γ with p s, β s.1 ≤ total / stabFactor :=
    (sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun s _ h ↦ hp s h)
      fun s _ _ ↦ h_nonneg s).trans (h_stab d)
  have h_coord (v : Fin l.castSucc → ResField w.1) (hv : v ≠ 0) :
      inclMatrix (ResField w.1) (Fin.castLE l.castSucc.is_le) *ᵥ v ≠ 0 :=
    (map_ne_zero_iff _ (inclMatrix_mulVecLin_injective (Fin.castLEEmb l.castSucc.is_le) _)).2 hv
  have h_fix_vector (v : Fin l.castSucc → ResField w.1) (hv : v ≠ 0) :
      ∑ s with e *ᵥ v = π s • e *ᵥ v, β s.1 ≤ total / stabFactor := by
    refine h_le_of_fixes ⟨false, _, h_coord v hv⟩ _ fun s hs ↦ ?_
    rw [mem_vectorFixer_false, mulVec_mulVec v]
    exact hs.symm
  have h_fix_form (v : Fin l.castSucc → ResField w.1) (hv : v ≠ 0) :
      ∑ s with (J * e) *ᵥ v = invTransposeGL (π s) • (J * e) *ᵥ v, β s.1 ≤ total / stabFactor := by
    refine h_le_of_fixes ⟨true, _, h_coord v hv⟩ _ fun s hs ↦ ?_
    rw [mem_vectorFixer_true, mulVec_mulVec v, mulVec_mulVec v]
    exact hs.symm
  rw [le_div_iff₀' (by positivity)]
  calc _ ≤ card (ResField w.1) * ∑ s with ((J * e)ᵀ * (π s).1 * e).det = 0, β s.1 := by
        simp only [h_det, h_card]
        exact mul_le_mul_of_nonneg_right (S.le_levelPrime 0) (sum_nonneg fun s _ ↦ h_nonneg s)
    _ ≤ 2 * total + card (ResField w.1) ^ card (Fin l.castSucc) *
        √(card (ResField w.1) ^ card 𝔰.BesselIndex) * (total / stabFactor) :=
      card_mul_sum_det_eq_zero_le π e (J * e) (fun s ↦ h_nonneg s) (fun a b ↦ h_posType a b) _
        (by positivity) h_fix_vector h_fix_form
    _ ≤ 2 * total + stabFactor * (total / stabFactor) := by
      grw [h_card, Fintype.card_fin, Fin.val_castSucc, levelPrime_pow_mul_sqrt_le]
    _ = 3 * total := by field

open scoped Classical in
/-- Let the filling `S` be admissible (`IsAdmissible`), with `k = 𝔰.k` the rank of `X₀` and `S.b`
its large parameter. Let `β ≥ 0` on `ResidueGL` have positive type: `β (a⁻¹ * b) = ⟪u a, u b⟫` for
all `a`, `b`, for a map `u` into an inner product space. Let `Γ` be a subgroup of `ResidueGL` and
`w` a chosen place above `p₀`. Suppose that for every nonzero vector of the span of the frame,
modulo `w` or its conjugate, the elements of `Γ` that fix it (`vectorFixer`) carry at most a
proportion `S.b^(-6k)` of the sum of `β` over `Γ`. Then the elements of `Γ` that are not open carry
at most a proportion `S.b⁻⁴` of that sum. -/
lemma sum_not_isOpenElement_le [S.IsAdmissible] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {β : S.ResidueGL → ℝ} (h_nonneg : ∀ s : S.ResidueGL, 0 ≤ β s)
      {u : S.ResidueGL → V}
    (h_posType : ∀ a b : S.ResidueGL, ⟪u a, u b⟫_ℂ = β (a⁻¹ * b)) {Γ : Subgroup S.ResidueGL}
    {w : S.chosenPlaces 0}
    (h_stab : ∀ d : S.FrameVector w, ∑ s : Γ with s.val ∈ S.vectorFixer w d, β s.val ≤
      (∑ s : Γ, β s.val) / S.b ^ (6 * 𝔰.k)) :
    ∑ s : Γ with ¬S.IsOpenElement s.val, β s.val ≤ (S.b ^ 4)⁻¹ * ∑ s : Γ, β s.val := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_total_nonneg : 0 ≤ ∑ s : Γ, β s.1 := sum_nonneg fun s _ ↦ h_nonneg s
  let δ (l : Fin 𝔰.n) (s : S.ResidueGL) : ResField w.1 :=
    leadingMinor ((S.latticeMiddle (ResField w.1)).frameGram (s 0 w).1) l.castSucc
  calc
    _ ≤ ∑ l : Fin 𝔰.n, ∑ s : Γ with δ l s.val = 0, β s.val := by
      simp only [sum_filter]
      rw [sum_comm]
      refine sum_le_sum fun s _ ↦ ?_
      split_ifs with hs
      · exact sum_nonneg fun l _ ↦ ite_nonneg (h_nonneg s) le_rfl
      · obtain ⟨l, hl⟩ : ∃ l : Fin 𝔰.n, δ l s.val = 0 := by_contra fun h ↦ hs ⟨w, not_exists.1 h⟩
        refine le_trans ?_ (single_le_sum (fun l _ ↦ ite_nonneg (h_nonneg s) le_rfl) (mem_univ l))
        rw [ite_eq_left hl]
    _ ≤ card (Fin 𝔰.n) • (3 * (∑ s : Γ, β s.1) / S.b ^ 10) :=
      sum_le_card_nsmul _ _ _ fun l _ ↦ sum_leadingMinor_eq_zero_le h_nonneg h_posType h_stab l
    _ ≤ (S.b ^ 4)⁻¹ * ∑ s : Γ, β s.1 := by
      -- `3 n ≤ 3 b ≤ b⁶`
      have h_three : 3 ≤ S.b ^ 5 := le_trans (by linarith) (le_self_pow₀ S.one_le_b (by norm_num))
      grw [Fintype.card_fin, nsmul_eq_mul, S.succ_le_b, h_three]
      exact le_of_eq (by field)

/-- If `M ≤ (1 + 4 x) C + x M` with `0 ≤ x ≤ 1/10` and `C ≥ 0`, then `M ≤ (1 + 9 x) C`. -/
lemma le_one_add_nine_mul_of_le_add {x C M : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 10) (hC : 0 ≤ C)
    (h : M ≤ (1 + 4 * x) * C + x * M) : M ≤ (1 + 9 * x) * C := by
  -- `(1 - x) (1 + 9 x) - (1 + 4 x) = x (4 - 9 x)`
  have h_gain : 0 ≤ x * (4 - 9 * x) * C := mul_nonneg (mul_nonneg hx₀ (by linarith)) hC
  have h_mul : (1 - x) * M ≤ (1 - x) * ((1 + 9 * x) * C) := by linarith
  exact le_of_mul_le_mul_left h_mul (by linarith)

/-- Let the filling `S` over the CM field `E` be admissible (`IsAdmissible`) and assume Weil data on
`E`, which include a primitive `5040`-th root of unity. If `s ↦ ‖P_s‖²` has positive type, that is,
`‖P_(x⁻¹ y)‖² = ⟪u x, u y⟫` for vectors `u x` of an inner product space, and `‖P_1‖² ≤ 2 D_X`, then
`∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main`. -/
theorem sum_secondMoment_le [S.IsAdmissible] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [WeilData E] (u : S.ResidueGL → V)
    (h_posType : ∀ a b : S.ResidueGL,
      ⟪u a, u b⟫_ℂ = (secondMoment (S.amplitudeSum .full Set.univ) {a⁻¹ * b} :
      ℝ))
    (h_one : secondMoment (S.amplitudeSum .full Set.univ) {1} ≤ 2 * S.sourceDim) :
    ∑ s : S.ResidueGL, secondMoment (S.amplitudeSum .full Set.univ) {s} ≤
      (1 + 9 / S.b ^ 4) * S.mainSecondMoment := by
  classical
  -- Choose places and vectors maximizing `stabFactor ^ #places` times the sum over the fixer.
  -- Comparison with the empty set of places shows that it suffices to bound the sum for this
  -- choice.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  let β (s : S.ResidueGL) : ℝ := secondMoment (S.amplitudeSum .full Set.univ) {s}
  have h_nonneg (s : S.ResidueGL) : 0 ≤ β s := secondMoment_nonneg
  set stabFactor : ℝ := S.b ^ (6 * 𝔰.k)
  let mass (places : Finset (S.chosenPlaces 0))
      (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w) : ℝ :=
    ∑ s : S.ResidueGL with s ∈ S.fixer places vectors, β s
  have : Nonempty (∀ w : S.chosenPlaces 0, S.FrameVector w) := ⟨fun _ ↦ (true, ⟨1, one_ne_zero⟩)⟩
  obtain ⟨places, vectors, h_max⟩ : ∃ places vectors, ∀ places' vectors',
      stabFactor ^ #places' * mass places' vectors' ≤
        stabFactor ^ #places * mass places vectors := by
    simpa only [Prod.exists, Prod.forall, Function.uncurry_apply_pair] using Finite.exists_max
      (Function.uncurry fun places vectors ↦ stabFactor ^ #places * mass places vectors)
  suffices h_mass : mass places vectors ≤
      (1 + 9 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment) by
    calc _ = stabFactor ^ #(∅ : Finset (S.chosenPlaces 0)) * mass ∅ vectors := by
          simp [mass, β, mem_fixer]
      _ ≤ stabFactor ^ #places * mass places vectors := h_max ∅ vectors
      _ ≤ stabFactor ^ #places *
          ((1 + 9 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment)) := by gcongr
      _ = (1 + 9 / S.b ^ 4) * S.mainSecondMoment := by
        rw [inv_pow]
        field
  obtain rfl | h_places := eq_or_ne places univ
  · calc _ = secondMoment (S.amplitudeSum .full Set.univ) (S.fixer univ vectors) :=
          (secondMoment_eq_sum_secondMoment_singleton _
            (S.fixer univ vectors : Set S.ResidueGL)).symm
      _ ≤ stabFactor⁻¹ ^ #univ * S.mainSecondMoment := secondMoment_fixer_univ_le vectors fun s ↦
        (le_apply_one_of_inner_eq (β := β) h_posType s).trans h_one
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_right (by positivity))
  -- Take `w ∉ places`. Stabilizers of vectors at `w` are fixers for `insert w places`, so they are
  -- small by maximality.
  obtain ⟨w, hw⟩ : ∃ w : S.chosenPlaces 0, w ∉ places :=
    not_forall.1 (mt eq_univ_iff_forall.2 h_places)
  have mass_eq : mass places vectors = ∑ s : S.fixer places vectors, β s.1 :=
    sum_subtype _ (by simp) β
  have h_stab (d : S.FrameVector w) :
      ∑ s : S.fixer places vectors with s.1 ∈ S.vectorFixer w d, β s.1 ≤
        mass places vectors / stabFactor := by
    have h_le := h_max (insert w places) (Function.update vectors w d)
    rw [card_insert_of_notMem hw, pow_succ, mul_assoc, mul_le_mul_iff_right₀ (by positivity),
      ← le_div_iff₀' (by positivity)] at h_le
    rw [sum_subgroup_filter _ (· ∈ S.vectorFixer w d)]
    simpa only [mass, mem_fixer_insert hw] using h_le
  have h_other : ∑ s : S.fixer places vectors with ¬S.IsOpenElement s.1, β s.1 ≤
      (S.b ^ 4)⁻¹ * mass places vectors := by
    rw [mass_eq] at h_stab ⊢
    exact sum_not_isOpenElement_le h_nonneg h_posType h_stab
  have h_open : ∑ s : S.fixer places vectors with S.IsOpenElement s.1, β s.1 ≤
      (1 + 4 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment) := by
    refine le_trans (le_of_eq ?_) (secondMoment_fixer_isOpenElement_le places vectors)
    rw [sum_subgroup_filter, secondMoment_eq_sum_secondMoment_singleton]
    congr!
  have h_split : mass places vectors ≤
      (1 + 4 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment) + (S.b ^ 4)⁻¹ * mass places
        vectors := by
    grw [← h_open, ← h_other, sum_filter_add_sum_filter_not, mass_eq]
  simp only [div_eq_mul_inv _ (S.b ^ 4)] at h_split ⊢
  exact le_one_add_nine_mul_of_le_add (by positivity) (by grw [← hb]; norm_num) (by positivity)
    h_split

end Filling

end New
