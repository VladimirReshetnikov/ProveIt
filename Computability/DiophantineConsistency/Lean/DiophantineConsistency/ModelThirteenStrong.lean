import DiophantineConsistency.ModelThirteenForms
/-! # iPRA endpoints for the corrected-strong and mixed thirteen-variable carrier forms

Three thirteen-variable forms on the coordinates and ports of `ThirteenCarrier`:

* 13/73/126 (`ThirteenCorrectedStrong.value`): the strong factor of the 71 form
  plus `(i c)² (P - 1)`. Its positive zeros are exactly the 71 zeros, with the
  identity witness map, because `P ≠ -1` on every positive assignment.
* 13/74/122 (`ThirteenLVCarrier.value`): the squared carrier `V²` of the
  ordinate replaced by the mixed product `L V`. The link to 73 is
  **existence-level**: only the coordinate `m` changes, by `± G (V² - L V)`, and
  positivity of the shifted `m` is proved on each entire zero set.
* 13/72/124 (`ThirteenLVCarrier.value72`): the 74 form without the first-norm
  correction; on positive inputs it has exactly the 74 zeros.

The integer arguments use positivity, discreteness, the units `±1`, the
consecutive-product and mod-4 negative-unit exclusions and the auxiliary-norm
estimates; they are replayed over any discretely ordered ring with the carrier
`Facts` (`ModelCarrierSpheres`), so in every model of `𝗜𝚺₁` the 73 and 72 forms
have the zeros of already bridged forms, the 74 form has a zero iff the 73 form
does, and the bridges transfer.

The generic restoration definitions (`b`, `parent`, `data`, `G`, `signedY`)
are those copied into `ModelThirteenRestoration`; `ThirteenCarrierSoundness`
is deliberately not imported (Mathlib Pell's `Matrix` clashes with Foundation). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenStrong
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts
open ModelThirteenCarrier
open ModelCarrierSpheres (Facts modelFacts negative_unit_exclusions scales_pos unit_eq_one)
open ModelThirteenRestoration (b parent data G signedY signedY_shape parent_pos1 scale_ge_two
  auxiliary_estimates)

/-! ### Ring definitions (as in `ThirteenCorrectedStrong` and `ThirteenLVCarrier`) -/

section Defs
variable {R : Type*} [CommRing R]

/-- The old strong coefficient plus the first norm residual. -/
def correctedStrong (d : Carrier65.Core R) : R :=
  d.f ^ 2 - (d.i ^ 2 * d.c ^ 2) * (d.delta * d.c ^ 2 + (d.P - 1))

theorem correctedStrong_eq (d : Carrier65.Core R) :
    correctedStrong d = Carrier65.strong d - (d.i * d.c) ^ 2 * (d.P - 1) := by
  unfold correctedStrong Carrier65.strong
  ring

theorem strong_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    Carrier65.strong (data p v) =
      (ThirteenCarrier.core p v).f ^ 2 -
        (ThirteenCarrier.core p v).delta * (ThirteenCarrier.core p v).t ^ 2 := by
  change (data p v).f ^ 2 - (data p v).delta * ((b p v * v 4) * (data p v).c ^ 2) ^ 2 =
    (data p v).f ^ 2 - (data p v).delta * (b p v * v 4 * (data p v).c ^ 2) ^ 2
  rfl

/-- The 13/73/126 value (`ThirteenCorrectedStrong.value`). -/
def value73 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let c := ThirteenCarrier.core p v
  c.P * c.Q * (c.delta * (c.f ^ 2 - 1) * c.gap + c.y ^ 2) * correctedStrong (data p v) - 1

/-- Exact polynomial difference; the two polynomials are not identical. -/
theorem correction_identity (p : Fin 4 → R) (v : Fin 13 → R) :
    value73 p v = ThirteenCarrier.value71 p v -
      (ThirteenCarrier.core p v).P * (ThirteenCarrier.core p v).Q *
        ((ThirteenCarrier.core p v).delta * ((ThirteenCarrier.core p v).f ^ 2 - 1) *
          (ThirteenCarrier.core p v).gap + (ThirteenCarrier.core p v).y ^ 2) *
        ((data p v).i * (data p v).c) ^ 2 * ((ThirteenCarrier.core p v).P - 1) := by
  dsimp only [value73]
  rw [correctedStrong_eq, strong_shape]
  dsimp only [ThirteenCarrier.value71]
  change (ThirteenCarrier.core p v).P * (ThirteenCarrier.core p v).Q *
    ((ThirteenCarrier.core p v).delta * ((ThirteenCarrier.core p v).f ^ 2 - 1) *
      (ThirteenCarrier.core p v).gap + (ThirteenCarrier.core p v).y ^ 2) *
    ((ThirteenCarrier.core p v).f ^ 2 - (ThirteenCarrier.core p v).delta *
      (ThirteenCarrier.core p v).t ^ 2 -
      ((data p v).i * (data p v).c) ^ 2 * ((ThirteenCarrier.core p v).P - 1)) - 1 = _
  ring

/-- The mixed factor `L = c T - R`. -/
def mixL (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  (data p v).c * v 5 - (data p v).rank

/-- The mixed ordinate, with `L V` in place of `V²`. -/
def yLV (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  1 + 4 * (b p v * (v 11 - mixL p v * (data p v).V * G p v) - G p v)

/-- The auxiliary factor at an arbitrary ordinate. -/
def normalAux (p : Fin 4 → R) (v : Fin 13 → R) (ordinate : R) : R :=
  (data p v).delta * ((data p v).f ^ 2 - 1) * ((data p v).V ^ 2 - ordinate ^ 2) + ordinate ^ 2

/-- The unit product with the corrected strong factor. -/
def normalValue (p : Fin 4 → R) (v : Fin 13 → R) (ordinate : R) : R :=
  (data p v).P * (data p v).Q * normalAux p v ordinate * correctedStrong (data p v) - 1

/-- The unit product with the plain strong factor. -/
def normalValue72 (p : Fin 4 → R) (v : Fin 13 → R) (ordinate : R) : R :=
  (data p v).P * (data p v).Q * normalAux p v ordinate * Carrier65.strong (data p v) - 1

/-- The 13/74/122 value (`ThirteenLVCarrier.value`). -/
def value74 (p : Fin 4 → R) (v : Fin 13 → R) : R := normalValue p v (yLV p v)

/-- The 13/72/124 value (`ThirteenLVCarrier.value72`). -/
def value72 (p : Fin 4 → R) (v : Fin 13 → R) : R := normalValue72 p v (yLV p v)

theorem old_value (p : Fin 4 → R) (v : Fin 13 → R) :
    value73 p v = normalValue p v (signedY p v) := rfl

/-- Replace the coordinate `m`. -/
def setM (v : Fin 13 → R) (m : R) (j : Fin 13) : R := if j = 11 then m else v j

theorem parent_setM (p : Fin 4 → R) (v : Fin 13 → R) (m z ordinate : R) :
    parent p (setM v m) z ordinate = parent p v z ordinate := by
  funext j
  fin_cases j <;> simp [parent, b, setM]

theorem data_setM (p : Fin 4 → R) (v : Fin 13 → R) (m : R) :
    data p (setM v m) = data p v := by
  unfold data
  rw [parent_setM]

theorem b_setM (p : Fin 4 → R) (v : Fin 13 → R) (m : R) :
    b p (setM v m) = b p v := by simp [b, setM]

theorem G_setM (p : Fin 4 → R) (v : Fin 13 → R) (m : R) :
    G p (setM v m) = G p v := by simp [G, setM, data_setM]

theorem mixL_setM (p : Fin 4 → R) (v : Fin 13 → R) (m : R) :
    mixL p (setM v m) = mixL p v := by simp [mixL, setM, data_setM]

def correction (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  G p v * ((data p v).V ^ 2 - mixL p v * (data p v).V)

/-- From a 74 zero to a 73 zero. -/
def toOld (p : Fin 4 → R) (v : Fin 13 → R) : Fin 13 → R :=
  setM v (v 11 + correction p v)

/-- From a 73 zero to a 74 zero. -/
def toNew (p : Fin 4 → R) (v : Fin 13 → R) : Fin 13 → R :=
  setM v (v 11 - correction p v)

theorem signedY_toOld (p : Fin 4 → R) (v : Fin 13 → R) :
    signedY p (toOld p v) = yLV p v := by
  rw [signedY_shape]
  simp only [toOld, b_setM, data_setM, G_setM]
  simp only [setM, if_pos]
  unfold yLV correction
  ring

theorem yLV_toNew (p : Fin 4 → R) (v : Fin 13 → R) :
    yLV p (toNew p v) = signedY p v := by
  unfold yLV
  simp only [toNew, b_setM, data_setM, G_setM, mixL_setM]
  simp only [setM, if_pos]
  rw [signedY_shape]
  unfold correction
  ring

theorem old_toOld (p : Fin 4 → R) (v : Fin 13 → R) :
    value73 p (toOld p v) = value74 p v := by
  rw [old_value, signedY_toOld]
  simp only [normalValue, normalAux, value74, toOld, data_setM]

theorem new_toNew (p : Fin 4 → R) (v : Fin 13 → R) :
    value74 p (toNew p v) = value73 p v := by
  rw [value74, yLV_toNew, old_value]
  simp only [normalValue, normalAux, toNew, data_setM]

/-- With the strong norm, the auxiliary coefficient is the squared scale. -/
theorem coeff_of_strong (p : Fin 4 → R) (v : Fin 13 → R)
    (hs : Carrier65.strong (data p v) = 1) :
    (data p v).delta * ((data p v).f ^ 2 - 1) = (data p v).S ^ 2 := by
  have hs' : (data p v).f ^ 2 - (data p v).delta * ((data p v).i * (data p v).c ^ 2) ^ 2 = 1 :=
    hs
  change (data p v).delta * ((data p v).f ^ 2 - 1) =
    ((data p v).i * (data p v).delta * (data p v).c ^ 2) ^ 2
  linear_combination (data p v).delta * hs'

end Defs

/-! ### The integer arguments in a discretely ordered ring -/

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The first-norm exclusion on every positive assignment, without a zero premise. -/
theorem data_first_ne_neg_one (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : (data p v).P ≠ -1 :=
  (negative_unit_exclusions F p (parent p v 1 1) hb (parent_pos1 F p v hb hv)).1

theorem first_ne_neg_one (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : (ThirteenCarrier.core p v).P ≠ -1 :=
  -- CHECK: defeq between the two cores' `P` (the integer file uses the same `change`)
  data_first_ne_neg_one F p v hb hv

theorem first_eq_one_of_product (F : Facts R) {P Q U Z : R} (hP : P ≠ -1)
    (hz : P * Q * U * Z - 1 = 0) : P = 1 :=
  unit_eq_one F.discrete (show P * (Q * U * Z) = 1 by linear_combination hz) hP

/-- `ThirteenCorrectedStrong.positive_zero_iff`: identity on all thirteen coordinates. -/
theorem zero73_iff71 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value73 p v = 0 ↔ ThirteenCarrier.value71 p v = 0 := by
  have hnP := first_ne_neg_one F p v hb hv
  constructor
  · intro hz
    have hP := first_eq_one_of_product F hnP hz
    simpa only [correction_identity, hP, sub_self, mul_zero, sub_zero] using hz
  · intro hz
    have hP := first_eq_one_of_product F hnP hz
    simpa only [correction_identity, hP, sub_self, mul_zero, sub_zero] using hz

/-- `ThirteenLVCarrier.norms_of_zero`: either carrier gives the same normalized norms. -/
theorem norms_of_normal_zero (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) (ordinate : R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : normalValue p v ordinate = 0) :
    Carrier65.strong (data p v) = 1 ∧
      (data p v).S ^ 2 * (data p v).V ^ 2 - ((data p v).S ^ 2 - 1) * ordinate ^ 2 = 1 := by
  have hp := parent_pos1 F p v hb hv
  obtain ⟨hnP, hnQ, hnS⟩ := negative_unit_exclusions F p (parent p v 1 1) hb hp
  have hz0 : (data p v).P * (data p v).Q * normalAux p v ordinate *
      correctedStrong (data p v) - 1 = 0 := hz
  have hP : (data p v).P = 1 := first_eq_one_of_product F hnP hz0
  have hz' : (data p v).Q * normalAux p v ordinate * Carrier65.strong (data p v) = 1 := by
    rw [correctedStrong_eq, hP] at hz0
    linear_combination hz0
  have hs : Carrier65.strong (data p v) = 1 :=
    unit_eq_one F.discrete (show Carrier65.strong (data p v) *
      ((data p v).Q * normalAux p v ordinate) = 1 by linear_combination hz') hnS
  have hQ : (data p v).Q = 1 :=
    unit_eq_one F.discrete (show (data p v).Q * normalAux p v ordinate = 1 by
      linear_combination hz' - (data p v).Q * normalAux p v ordinate * hs) hnQ
  have hU : normalAux p v ordinate = 1 := by
    linear_combination hz' - normalAux p v ordinate * Carrier65.strong (data p v) * hQ -
      normalAux p v ordinate * hs
  refine ⟨hs, ?_⟩
  have hc := coeff_of_strong p v hs
  have hU' : (data p v).delta * ((data p v).f ^ 2 - 1) * ((data p v).V ^ 2 - ordinate ^ 2) +
      ordinate ^ 2 = 1 := hU
  rw [hc] at hU'
  linear_combination hU'

theorem seed_estimates (F : Facts R) {c delta i f S : R} (hc : 2 ≤ c) (hd : 0 < delta)
    (hi : 0 < i) (hs : f ^ 2 - delta * (i * c ^ 2) ^ 2 = 1)
    (hS : S = i * delta * c ^ 2) : c + 1 ≤ f ^ 2 ∧ c ^ 2 < S ^ 2 := by
  have hi1 : 1 ≤ i := F.discrete _ hi
  have hd1 : 1 ≤ delta := F.discrete _ hd
  have hc0 : 0 ≤ c := by linarith only [hc]
  have hcc : c < c ^ 2 := by nlinarith only [hc]
  have hu : c ^ 2 ≤ i * c ^ 2 := by
    have := mul_le_mul_of_nonneg_right hi1 (sq_nonneg c)
    linarith only [this]
  have hu' : c ≤ i * c ^ 2 := by linarith only [hu, hcc]
  have hic : 0 ≤ i * c ^ 2 := le_trans hc0 hu'
  have hu2 : c ^ 2 ≤ (i * c ^ 2) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu') (add_nonneg hic hc0)]
  have hd2 : (i * c ^ 2) ^ 2 ≤ delta * (i * c ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hd1 (sq_nonneg (i * c ^ 2))
    linarith only [this]
  have hds : i * c ^ 2 ≤ S := by
    have := mul_le_mul_of_nonneg_right hd1 hic
    rw [hS]
    linarith only [this]
  have hcS : c < S := by linarith only [hcc, hu, hds]
  refine ⟨by linarith only [hs, hd2, hu2, hcc], ?_⟩
  nlinarith only [mul_pos (sub_pos.mpr hcS) (show (0 : R) < S + c by linarith only [hcS, hc])]

theorem mixed_bounds (F : Facts R) {c f S L V ordinate : R} (hc : 2 ≤ c)
    (hf : c + 1 ≤ f ^ 2) (hSc : c ^ 2 < S ^ 2) (hV : V = f ^ 2 * L - c)
    (hn : S ^ 2 * V ^ 2 - (S ^ 2 - 1) * ordinate ^ 2 = 1) :
    L ≠ 0 ∧ |V| ≤ L * V ∧ L * V ≤ V ^ 2 := by
  have hc2 : 4 ≤ c ^ 2 := by nlinarith only [hc]
  have hL : L ≠ 0 := by
    intro hL0
    have he : V = -c := by rw [hV, hL0]; ring
    rw [he] at hn
    have hprod : (S ^ 2 - 1) * (ordinate ^ 2 - c ^ 2) = c ^ 2 - 1 := by
      linear_combination -hn
    have hS1 : 0 ≤ S ^ 2 - 1 := by linarith only [hSc, hc2]
    have hgap : 0 < ordinate ^ 2 - c ^ 2 := by
      by_contra hh
      push_neg at hh
      have hh' := mul_nonpos_of_nonneg_of_nonpos hS1 hh
      linarith only [hh', hprod, hc2]
    have hlarge := mul_le_mul_of_nonneg_left (F.discrete _ hgap) hS1
    rw [mul_one] at hlarge
    linarith only [hlarge, hprod, hSc]
  refine ⟨hL, ?_⟩
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · have hL1 : L ≤ -1 := by
      have := F.discrete (-L) (by linarith only [hneg])
      linarith only [this]
    have hf1 : 0 ≤ f ^ 2 - 1 := by linarith only [hf, hc]
    have hm := mul_nonpos_of_nonneg_of_nonpos hf1 hneg.le
    have hVL : V ≤ L := by linarith only [hV, hm, hc]
    have hV0 : V ≤ 0 := by linarith only [hVL, hneg]
    rw [abs_of_nonpos hV0]
    constructor
    · nlinarith only [mul_nonneg (show (0 : R) ≤ -L - 1 by linarith only [hL1])
        (neg_nonneg.mpr hV0)]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr hVL) (neg_nonneg.mpr hV0)]
  · have hL1 : 1 ≤ L := F.discrete _ hpos
    have hm := mul_nonneg (show (0 : R) ≤ f ^ 2 - c - 1 by linarith only [hf]) hpos.le
    have hmc := mul_nonneg (show (0 : R) ≤ c by linarith only [hc])
      (show (0 : R) ≤ L - 1 by linarith only [hL1])
    have hVL : L ≤ V := by linarith only [hV, hm, hmc]
    have hV0 : 0 ≤ V := by linarith only [hVL, hL1]
    rw [abs_of_nonneg hV0]
    constructor
    · nlinarith only [mul_nonneg (show (0 : R) ≤ L - 1 by linarith only [hL1]) hV0]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr hVL) hV0]

theorem carrier_nonneg (F : Facts R) {base m transport A V ordinate : R}
    (hb : 0 < base) (hm : 0 < m) (hA : |V| ≤ A)
    (hy : ordinate = 1 + 4 * (base * (m - A * transport) - transport))
    (hsmall : |ordinate| < 2 * |V|) : 0 ≤ transport := by
  by_contra hG
  push_neg at hG
  have hG1 : 1 ≤ -transport := F.discrete _ (by linarith only [hG])
  have hA0 : 0 ≤ A := le_trans (abs_nonneg V) hA
  have hbaseA := mul_le_mul_of_nonneg_right (F.discrete _ hb) hA0
  have hbm : 1 ≤ base * m := F.discrete _ (mul_pos hb hm)
  have hprod := mul_nonneg (show (0 : R) ≤ 1 + base * A by linarith only [hbaseA, hA0])
    (show (0 : R) ≤ -transport - 1 by linarith only [hG1])
  linarith only [hy, hprod, hbaseA, hbm, le_abs_self ordinate, hsmall, hA, hA0]

theorem subtractive_positive (F : Facts R) {base m transport A V ordinate : R}
    (hb : 0 < base) (hm : 0 < m) (hG : 0 ≤ transport) (hA : |V| ≤ A)
    (hy : ordinate = 1 + 4 * (base * (m - V ^ 2 * transport) - transport))
    (hsmall : |ordinate| < 2 * |V|) : 0 < m - transport * (V ^ 2 - A) := by
  rcases hG.eq_or_lt with hG0 | hGpos
  · rw [← hG0, zero_mul, sub_zero]
    exact hm
  have hG1 : 1 ≤ transport := F.discrete _ hGpos
  have hA0 : 0 ≤ A := le_trans (abs_nonneg V) hA
  have hAG := mul_le_mul_of_nonneg_left hG1 hA0
  have hprod := mul_le_mul_of_nonneg_left
    (show |V| ≤ transport * A by linarith only [hA, hAG]) hb.le
  have hbaseV := mul_le_mul_of_nonneg_right (F.discrete _ hb) (abs_nonneg V)
  have hlo := neg_abs_le ordinate
  have he : 4 * base * (m - transport * (V ^ 2 - A)) =
      4 * base * A * transport + 4 * transport + ordinate - 1 := by
    rw [hy]
    ring
  have hpos : 0 < 4 * base * (m - transport * (V ^ 2 - A)) := by
    rw [he]
    linarith only [hprod, hbaseV, hlo, hsmall, hG1, abs_nonneg V]
  exact (mul_pos_iff_of_pos_left (by linarith only [hb] : (0 : R) < 4 * base)).mp hpos

theorem bounds_of_normal_zero (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) (ordinate : R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : normalValue p v ordinate = 0) :
    mixL p v ≠ 0 ∧ |(data p v).V| ≤ mixL p v * (data p v).V ∧
      mixL p v * (data p v).V ≤ (data p v).V ^ 2 ∧
      |ordinate| < 2 * |(data p v).V| := by
  obtain ⟨hs, hn⟩ := norms_of_normal_zero F p v ordinate hb hv hz
  have hp := parent_pos1 F p v hb hv
  have hd : 0 < (data p v).delta :=
    ModelCarrierScaled.delta_pos F.discrete p (parent p v 1 1) hb hp
  have hi : 0 < (data p v).i := mul_pos (mul_pos hb (hv 0)) (hv 4)
  obtain ⟨_, _, hY, _, _⟩ := scales_pos F p (parent p v 1 1) hb hp
  have hY1 : 1 ≤ (data p v).Y := F.discrete _ hY
  have h9 : 1 ≤ v 9 := F.discrete _ (hv 9)
  have h10 : 1 ≤ v 10 := F.discrete _ (hv 10)
  have hk : 2 ≤ (data p v).k := by
    change 2 ≤ v 9 + v 10
    linarith only [h9, h10]
  have hc : 2 ≤ (data p v).c := by
    change 2 ≤ (data p v).k * (data p v).Y + v 9
    nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hY1), hk, hY1, h9]
  have he := seed_estimates F hc hd hi hs
    (rfl : (data p v).S = (data p v).i * (data p v).delta * (data p v).c ^ 2)
  have hm := mixed_bounds F hc he.1 he.2
    (rfl : (data p v).V = (data p v).f ^ 2 * mixL p v - (data p v).c) hn
  exact ⟨hm.1, hm.2.1, hm.2.2,
    (auxiliary_estimates F (scale_ge_two F p v hb hv) hn).2⟩

theorem setM_pos (v : Fin 13 → R) (m : R) (hv : ∀ j, 0 < v j) (hm : 0 < m) :
    ∀ j, 0 < setM v m j := by
  intro j
  by_cases hj : j = 11
  · show 0 < (if j = 11 then m else v j)
    rw [if_pos hj]
    exact hm
  · show 0 < (if j = 11 then m else v j)
    rw [if_neg hj]
    exact hv j

/-- Every positive 74 zero maps to a positive 73 zero. -/
theorem positive_toOld (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : value74 p v = 0) :
    (∀ j, 0 < toOld p v j) ∧ value73 p (toOld p v) = 0 := by
  have h := bounds_of_normal_zero F p v (yLV p v) hb hv hz
  have hG := carrier_nonneg F (transport := G p v) (ordinate := yLV p v)
    (mul_pos hb (hv 0)) (hv 11) h.2.1 rfl h.2.2.2
  have hcor : 0 ≤ correction p v := mul_nonneg hG (sub_nonneg.mpr h.2.2.1)
  exact ⟨setM_pos v _ hv (add_pos_of_pos_of_nonneg (hv 11) hcor),
    by rw [old_toOld]; exact hz⟩

/-- Every positive 73 zero maps to a positive 74 zero. The subtractive map is
not claimed positive on arbitrary positive inputs. -/
theorem positive_toNew (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : value73 p v = 0) :
    (∀ j, 0 < toNew p v j) ∧ value74 p (toNew p v) = 0 := by
  have hn : normalValue p v (signedY p v) = 0 := by rwa [← old_value]
  have h := bounds_of_normal_zero F p v (signedY p v) hb hv hn
  have hG := carrier_nonneg F (mul_pos hb (hv 0)) (hv 11)
    (le_trans h.2.1 h.2.2.1) (signedY_shape p v) h.2.2.2
  have hm := subtractive_positive F (mul_pos hb (hv 0)) (hv 11) hG h.2.1
    (signedY_shape p v) h.2.2.2
  exact ⟨setM_pos v _ hv hm, by rw [new_toNew]; exact hz⟩

/-- `ThirteenLVCarrier.positive_zero_iff72`: on positive inputs the optional
first-norm correction vanishes on either zero set. -/
theorem zero74_iff72 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value74 p v = 0 ↔ value72 p v = 0 := by
  have same (hP : (data p v).P = 1) : value74 p v = value72 p v := by
    show normalValue p v (yLV p v) = normalValue72 p v (yLV p v)
    unfold normalValue normalValue72
    rw [correctedStrong_eq, hP]
    ring
  have hnP := data_first_ne_neg_one F p v hb hv
  constructor <;> intro hz
  · have hz0 : (data p v).P * (data p v).Q * normalAux p v (yLV p v) *
        correctedStrong (data p v) - 1 = 0 := hz
    rw [← same (first_eq_one_of_product F hnP hz0)]
    exact hz
  · have hz0 : (data p v).P * (data p v).Q * normalAux p v (yLV p v) *
        Carrier65.strong (data p v) - 1 = 0 := hz
    rw [same (first_eq_one_of_product F hnP hz0)]
    exact hz

end Generic

/-! ### Literal syntax -/

/-- The thirteen-coordinate front of the mixed carriers, followed by
`final P Q delta f c bi V L G b m T` (with `bi = b i` the parent's `i`). -/
def front13x (p : Fin 4 → ℤ)
    (final : Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) →
      Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) →
      Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13)) :
    Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let s : Expr (Fin 13) := .var 6
  let w : Expr (Fin 13) := .var 7
  let n : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let m : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let L := c * T - rank
  let V := f ^ 2 * L - c
  let G := (Expr.constant (p 1) + w) * C - F
  final (tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) delta f c (b * i) V L G b m T

/-- The 13/73/126 polynomial. -/
def expressionAt73 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13x p fun P Q delta f c bi V _ G bb m _ =>
    let y := 1 + 4 * (bb * (m - V ^ 2 * G) - G)
    P * Q * (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) *
      (f ^ 2 - (bi ^ 2 * c ^ 2) * (delta * c ^ 2 + (P - 1))) - 1

/-- The 13/74/122 polynomial. -/
def expressionAt74 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13x p fun P Q delta f c bi V L G bb m _ =>
    let y := 1 + 4 * (bb * (m - L * V * G) - G)
    P * Q * (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) *
      (f ^ 2 - (bi ^ 2 * c ^ 2) * (delta * c ^ 2 + (P - 1))) - 1

/-- The 13/72/124 polynomial. -/
def expressionAt72 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13x p fun P Q delta f c bi V L G bb m _ =>
    let y := 1 + 4 * (bb * (m - L * V * G) - G)
    P * Q * (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) *
      (f ^ 2 - delta * (bi * c ^ 2) ^ 2) - 1

section Eval
variable {R : Type*} [CommRing R]

-- CHECK: the closing `rfl` unfolds `data`/`parent` (literal `Fin` matches) by defeq.
theorem evalRing_expressionAt73 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt73 p).evalRing v = value73 (fun j => (p j : R)) v := by
  simp only [expressionAt73, front13x, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one]
  rfl

-- CHECK: as above.
theorem evalRing_expressionAt74 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt74 p).evalRing v = value74 (fun j => (p j : R)) v := by
  simp only [expressionAt74, front13x, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one]
  rfl

-- CHECK: as above.
theorem evalRing_expressionAt72 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt72 p).evalRing v = value72 (fun j => (p j : R)) v := by
  simp only [expressionAt72, front13x, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one]
  rfl

end Eval

/-! ### Models of `𝗜𝚺₁` -/

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 73 form has exactly the 71 zeros (identity witness map). -/
theorem sameZero73 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt73 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift
        (ModelThirteenForms.expressionAt71 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt73, ModelThirteenForms.evalRing_expressionAt71]
  exact zero73_iff71 modelFacts ringPorts (fun i => ι (u i + 1)) ModelCarrierCurrent.beta_pos
    (ModelThirteenForms.shifted13_pos u)

/-- The 72 form has exactly the 74 zeros (identity witness map). -/
theorem sameZero72 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift (expressionAt74 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt72, evalRing_expressionAt74]
  exact (zero74_iff72 modelFacts ringPorts (fun i => ι (u i + 1)) ModelCarrierCurrent.beta_pos
    (ModelThirteenForms.shifted13_pos u)).symm

end Model

/-! ### The existence-level 74/73 link -/

section Bridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- In every model, the 74 form has a positive zero iff the 73 form does; the
witness maps `toOld`/`toNew` change only the coordinate `m`. -/
theorem sameNoZero74 : HAExpressionNoZeroEquiv.SameNoZero
    (positiveShift (expressionAt74 CurrentWindowCarry2011.ports))
    (positiveShift (expressionAt73 CurrentWindowCarry2011.ports)) := by
  intro V _ _
  constructor
  · intro h u hz
    have hz' := (internalZero_iff _ _).mp ((internalZero_positiveShift _ u).mp hz)
    rw [evalRing_expressionAt73] at hz'
    obtain ⟨hpos, hval⟩ := positive_toNew modelFacts ringPorts (fun j => ι (u j + 1))
      ModelCarrierCurrent.beta_pos (ModelThirteenForms.shifted13_pos u) hz'
    obtain ⟨w, hw⟩ := shifted_of_positive _ hpos
    apply h w
    rw [internalZero_positiveShift, internalZero_iff, evalRing_expressionAt74]
    have hfun : (fun k => ι (w k + 1)) = toNew ringPorts (fun j => ι (u j + 1)) :=
      funext fun k => (hw k).symm
    rw [hfun]
    exact hval
  · intro h u hz
    have hz' := (internalZero_iff _ _).mp ((internalZero_positiveShift _ u).mp hz)
    rw [evalRing_expressionAt74] at hz'
    obtain ⟨hpos, hval⟩ := positive_toOld modelFacts ringPorts (fun j => ι (u j + 1))
      ModelCarrierCurrent.beta_pos (ModelThirteenForms.shifted13_pos u) hz'
    obtain ⟨w, hw⟩ := shifted_of_positive _ hpos
    apply h w
    rw [internalZero_positiveShift, internalZero_iff, evalRing_expressionAt73]
    have hfun : (fun k => ι (w k + 1)) = toOld ringPorts (fun j => ι (u j + 1)) :=
      funext fun k => (hw k).symm
    rw [hfun]
    exact hval

end Bridge

/-! ### Bridges and iPRA endpoints -/

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem bridge73 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt73 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero73 u) ModelThirteenForms.bridge71

theorem bridge74 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt74 CurrentWindowCarry2011.ports)) :=
  HAExpressionNoZeroEquiv.bridge _ _ sameNoZero74 bridge73

theorem bridge72 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero72 u) bridge74

/-- **Native iPRA: the 13/73/126 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence73 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt73 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge73

theorem standard_equivalence73 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt73 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence73

theorem reference_equivalence73 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt73 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence73

/-- **Native iPRA: the 13/74/122 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence74 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt74 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge74

theorem standard_equivalence74 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt74 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence74

theorem reference_equivalence74 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt74 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence74

/-- **Native iPRA: the 13/72/124 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence72 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge72

theorem standard_equivalence72 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence72

theorem reference_equivalence72 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt72 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence72

end DiophantineConsistency.ModelThirteenStrong
