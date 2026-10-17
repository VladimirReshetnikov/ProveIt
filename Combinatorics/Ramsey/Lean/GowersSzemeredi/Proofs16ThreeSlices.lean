import GowersSzemeredi.Proofs16PolyCoverTwo
import GowersSzemeredi.Proofs18LengthSixCounts

/-! The slices of a three-dimensional piece (Notes L.5, D2).

In dimension three the final-coordinate sections `h ↦ φ(h, t)` of a piece are
two-dimensional partial functions with the product property. The cubic lift
needs any `r` of them, stacked, to be covered with controls monotone in `r`.
* `section16_slice_decomposition_three`: above Lemma 15.6's threshold, every
  section has a good part `C t` of all but `θN²` points. Its graph lies in
  `polyTwoPieces γ θ` pieces of the uniform class.
* `section16_three_slice_provider`: the stacked slices of `φ₁ = φ(x₀ + ·, ·)`
  on any domain `D` with `init z + x₀ ∈ C (last z)` for all `z ∈ D` form a
  `Section16SliceProvider`. The proof is the uniform cover at
  `r·polyTwoPieces` pieces (`section16_uniform_cover_two`), translated by
  `-x₀`.
* The controls are the power envelopes `threeSlicePb`, `threeSliceEs` of the
  base `(r+1)(m+1)(K₁+p₁+1)·2/(γθε)`. They are monotone and antitone in `r`
  and dominate the actual controls by `uniTwoCount_le_power` and
  `uniTwoExp_inv_le_power`.
* `card_translated_slice_bad_le_succ` (`Proofs16PolyPieceTwoInputs`): the
  translated points that miss the good parts number at most `θN^(k+1)`, in
  every dimension.

The decomposition and the provider, with `section16_slices_envelope_cover`,
are in `Proofs16ThreeSlicesSide`, outside the final route. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- A final-coordinate section inherits the product property, in every dimension. -/
theorem HasProductProperty.final_section {N k : Nat} [NeZero N] {gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hprod : HasProductProperty B phi gamma) (t : ZMod N) :
    HasProductProperty (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) gamma := by
  have h := hprod.coordinateFace (lastSliceFace k t)
  have hdom : (lastSliceFace k t).domain B = section16FinalCoordinateSection B t := by
    ext x
    simp [CoordinateFace.domain, section16FinalCoordinateSection, lastSliceFace]
  have hfun : (lastSliceFace k t).pullback phi = section16FinalCoordinateRestriction phi t := by
    funext x
    rfl
  rw [hdom, hfun] at h
  exact h

/-! ### The slice decomposition -/

/-! ### The stacked slice provider -/

/-- The base of the slice envelopes. -/
def threeSliceBase (theta gamma : Real) (K1 p1 : Nat) (r : Nat) (eps : Real) : Real :=
  ((r : Real) + 1) * ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
    (2 / (gamma * theta * |eps|))

/-- The count envelope of the stacked slices. -/
def threeSlicePb (theta gamma : Real) (K1 p1 : Nat) : Nat → Real → Real :=
  fun r eps => threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 89)

/-- The exponent envelope of the stacked slices. -/
def threeSliceEs (theta gamma : Real) (K1 p1 : Nat) : Nat → Real → Real :=
  fun r eps => (threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 130))⁻¹

theorem threeSliceBase_facts {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (K1 p1 r : Nat) {eps : Real} (he : 0 < eps)
    (he1 : eps ≤ 1) :
    2 / (gamma * theta) ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      eps⁻¹ ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      ((r * polyTwoPieces gamma theta : Nat) : Real) ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      (K1 : Real) ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      (p1 : Real) ≤ threeSliceBase theta gamma K1 p1 r eps := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  unfold threeSliceBase
  rw [abs_of_pos he]
  have hc2 : 2 ≤ 2 / (gamma * theta * eps) := by
    rw [le_div_iff₀ (by positivity)]
    have : gamma * theta * eps ≤ 1 := mul_le_one₀ hgt1 he.le he1
    linarith
  have hv : 2 / (gamma * theta) ≤ 2 / (gamma * theta * eps) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hei : eps⁻¹ ≤ 2 / (gamma * theta * eps) := by
    rw [show 2 / (gamma * theta * eps) = 2 / (gamma * theta) * eps⁻¹ by field_simp]
    have h2 : (1 : Real) ≤ 2 / (gamma * theta) := by rw [le_div_iff₀ hgt]; linarith
    have := inv_pos.mpr he
    nlinarith
  have hr1 : (1 : Real) ≤ (r : Real) + 1 := by linarith [(Nat.cast_nonneg r : (0 : Real) ≤ r)]
  have hm1 : (1 : Real) ≤ (polyTwoPieces gamma theta : Real) + 1 := by
    linarith [(Nat.cast_nonneg (polyTwoPieces gamma theta) : (0 : Real) ≤ _)]
  have hK1 : (1 : Real) ≤ (K1 : Real) + p1 + 1 := by
    linarith [(Nat.cast_nonneg K1 : (0 : Real) ≤ K1), (Nat.cast_nonneg p1 : (0 : Real) ≤ p1)]
  have hc0 : (0 : Real) ≤ 2 / (gamma * theta * eps) := by positivity
  set c := 2 / (gamma * theta * eps)
  set a := (r : Real) + 1
  set b := (polyTwoPieces gamma theta : Real) + 1
  set d := (K1 : Real) + p1 + 1
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le hr1 hm1
  have habd : 1 ≤ a * b * d := one_le_mul_of_one_le_of_one_le hab hK1
  have hbase : c ≤ a * b * d * c := le_mul_of_one_le_left hc0 habd
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc2
  refine ⟨hv.trans hbase, hei.trans hbase, ?_, ?_, ?_⟩
  · push_cast
    have h1 : (r : Real) * (polyTwoPieces gamma theta : Real) ≤ a * b := by
      have := Nat.cast_nonneg (α := Real) r
      have := Nat.cast_nonneg (α := Real) (polyTwoPieces gamma theta)
      nlinarith
    calc (r : Real) * (polyTwoPieces gamma theta : Real) ≤ a * b := h1
      _ ≤ a * b * d := le_mul_of_one_le_right (by linarith) hK1
      _ ≤ a * b * d * c := le_mul_of_one_le_right (by linarith) hc1
  · have h1 : (K1 : Real) ≤ d := by linarith [(Nat.cast_nonneg p1 : (0 : Real) ≤ p1)]
    calc (K1 : Real) ≤ d := h1
      _ ≤ a * b * d := le_mul_of_one_le_left (by linarith) hab
      _ ≤ a * b * d * c := le_mul_of_one_le_right (by linarith) hc1
  · have h1 : (p1 : Real) ≤ d := by linarith [(Nat.cast_nonneg K1 : (0 : Real) ≤ K1)]
    calc (p1 : Real) ≤ d := h1
      _ ≤ a * b * d := le_mul_of_one_le_left (by linarith) hab
      _ ≤ a * b * d * c := le_mul_of_one_le_right (by linarith) hc1

theorem threeSliceBase_two_le {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (K1 p1 r : Nat) {eps : Real} (he : 0 < eps)
    (he1 : eps ≤ 1) : 2 ≤ threeSliceBase theta gamma K1 p1 r eps := by
  obtain ⟨hv, -, -, -, -⟩ := threeSliceBase_facts ht ht1 hg hg1 K1 p1 r he he1
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  exact hv2.trans hv

theorem threeSliceBase_mono (theta gamma : Real) (ht : 0 < theta) (hg : 0 < gamma)
    (K1 p1 : Nat) (eps : Real) : Monotone fun r => threeSliceBase theta gamma K1 p1 r eps := by
  intro r r' hrr
  dsimp only
  unfold threeSliceBase
  have hr : (r : Real) ≤ r' := by exact_mod_cast hrr
  have h0 : (0 : Real) ≤ ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
      (2 / (gamma * theta * |eps|)) := by positivity
  have e1 : ((r : Real) + 1) * ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
      (2 / (gamma * theta * |eps|)) = ((r : Real) + 1) * (((polyTwoPieces gamma theta : Real) + 1) *
      ((K1 : Real) + p1 + 1) * (2 / (gamma * theta * |eps|))) := by ring
  have e2 : ((r' : Real) + 1) * ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
      (2 / (gamma * theta * |eps|)) = ((r' : Real) + 1) * (((polyTwoPieces gamma theta : Real) + 1) *
      ((K1 : Real) + p1 + 1) * (2 / (gamma * theta * |eps|))) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) h0

/-- The envelopes have the ranges and monotonicity the lift needs. -/
theorem threeSlice_ranges {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (K1 p1 : Nat) :
    Section16SliceProviderRanges (threeSlicePb theta gamma K1 p1) (threeSliceEs theta gamma K1 p1) ∧
      (∀ eps, Monotone fun r => threeSlicePb theta gamma K1 p1 r eps) ∧
      (∀ eps, 0 < eps → Antitone fun r => threeSliceEs theta gamma K1 p1 r eps) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r eps _ he he1
    have h2 := threeSliceBase_two_le ht ht1 hg hg1 K1 p1 r he he1
    have hpos : 0 < threeSliceBase theta gamma K1 p1 r eps := lt_of_lt_of_le (by norm_num) h2
    refine ⟨one_le_pow₀ (le_trans (by norm_num) h2), inv_pos.mpr (pow_pos hpos _), ?_⟩
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_trans (by norm_num) h2))
  · intro eps r r' hrr
    show threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 89) ≤
      threeSliceBase theta gamma K1 p1 r' eps ^ ((2 : Nat) ^ 89)
    exact pow_le_pow_left₀ (by unfold threeSliceBase; positivity)
      (threeSliceBase_mono theta gamma ht hg K1 p1 eps hrr) _
  · intro eps he r r' hrr
    show (threeSliceBase theta gamma K1 p1 r' eps ^ ((2 : Nat) ^ 130))⁻¹ ≤
      (threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 130))⁻¹
    have hpos : 0 < threeSliceBase theta gamma K1 p1 r eps := by
      unfold threeSliceBase
      have : 0 < |eps| := abs_pos.mpr he.ne'
      positivity
    exact inv_anti₀ (pow_pos hpos _)
      (pow_le_pow_left₀ hpos.le (threeSliceBase_mono theta gamma ht hg K1 p1 eps hrr) _)

end LeanProofs.GowersSzemeredi
