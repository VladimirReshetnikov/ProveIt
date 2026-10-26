import DiophantineConsistency.ThirteenCorrectedStrong

/-! # Replacing the squared carrier by the mixed product L*V

Here L=c*T-R and V=f²*L-c. Only the positive coordinate m changes in
the witness maps. The two maps are polynomial inverses, but positivity is
proved on each entire zero set, not presumed for arbitrary assignments.
-/

set_option Elab.async false
set_option maxRecDepth 10000
namespace DiophantineConsistency.ThirteenLVCarrier
open ThirteenCarrierSoundness

variable {A B : Type*} [CommRing A] [CommRing B]

def L (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  (data p v).c * v 5 - (data p v).rank

def y (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  1 + 4 * (b p v * (v 11 - L p v * (data p v).V * G p v) - G p v)

def normalValue (p : Fin 4 → A) (v : Fin 13 → A) (ordinate : A) : A :=
  let d := data p v
  d.P * d.Q * (d.delta * (d.f^2 - 1) * (d.V^2 - ordinate^2) + ordinate^2) *
    ThirteenCorrectedStrong.correctedStrong d - 1

def value (p : Fin 4 → A) (v : Fin 13 → A) : A := normalValue p v (y p v)

theorem old_value (p : Fin 4 → A) (v : Fin 13 → A) :
    ThirteenCorrectedStrong.value p v = normalValue p v (signedY p v) := rfl

def setM (v : Fin 13 → A) (m : A) (j : Fin 13) : A := if j = 11 then m else v j

theorem parent_setM (p : Fin 4 → A) (v : Fin 13 → A) (m z ordinate : A) :
    parent p (setM v m) z ordinate = parent p v z ordinate := by
  funext j
  fin_cases j <;> simp [parent, b, setM]

@[simp] theorem data_setM (p : Fin 4 → A) (v : Fin 13 → A) (m : A) :
    data p (setM v m) = data p v := by
  unfold data
  rw [parent_setM]

@[simp] theorem b_setM (p : Fin 4 → A) (v : Fin 13 → A) (m : A) :
    b p (setM v m) = b p v := by simp [b, setM]

@[simp] theorem G_setM (p : Fin 4 → A) (v : Fin 13 → A) (m : A) :
    G p (setM v m) = G p v := by simp [G, setM]

@[simp] theorem L_setM (p : Fin 4 → A) (v : Fin 13 → A) (m : A) :
    L p (setM v m) = L p v := by simp [L, setM]

def correction (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  G p v * ((data p v).V^2 - L p v * (data p v).V)

def toOld (p : Fin 4 → A) (v : Fin 13 → A) : Fin 13 → A :=
  setM v (v 11 + correction p v)

def toNew (p : Fin 4 → A) (v : Fin 13 → A) : Fin 13 → A :=
  setM v (v 11 - correction p v)

theorem signedY_toOld (p : Fin 4 → A) (v : Fin 13 → A) :
    signedY p (toOld p v) = y p v := by
  rw [signedY_shape]
  simp only [toOld, b_setM, data_setM, G_setM]
  simp only [setM, if_pos]
  unfold y correction
  ring

theorem y_toNew (p : Fin 4 → A) (v : Fin 13 → A) :
    y p (toNew p v) = signedY p v := by
  unfold y
  simp only [toNew, b_setM, data_setM, G_setM, L_setM]
  simp only [setM, if_pos]
  rw [signedY_shape]
  unfold correction
  ring

theorem old_toOld (p : Fin 4 → A) (v : Fin 13 → A) :
    ThirteenCorrectedStrong.value p (toOld p v) = value p v := by
  rw [old_value, signedY_toOld]
  simp only [normalValue, value, toOld, data_setM]

theorem new_toNew (p : Fin 4 → A) (v : Fin 13 → A) :
    value p (toNew p v) = ThirteenCorrectedStrong.value p v := by
  rw [value, y_toNew, old_value]
  simp only [normalValue, toNew, data_setM]

theorem maps_inverse (p : Fin 4 → A) (v : Fin 13 → A) :
    toOld p (toNew p v) = v ∧ toNew p (toOld p v) = v := by
  constructor <;> funext j <;> by_cases hj : j = 11 <;>
    simp [toOld, toNew, correction, setM, hj]

/-- Either carrier supplies exactly the same normalized norms, with its own
signed ordinate. No positivity of that ordinate or native calibration is used. -/
theorem norms_of_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (ordinate : ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : normalValue p v ordinate = 0) :
    Carrier65.strong (data p v) = 1 ∧
      (data p v).S^2 * (data p v).V^2 - ((data p v).S^2 - 1) * ordinate^2 = 1 := by
  let d := data p v
  let U := d.delta * (d.f^2 - 1) * (d.V^2 - ordinate^2) + ordinate^2
  have hP : d.P = 1 := ThirteenCorrectedStrong.first_eq_one_of_product
    (ThirteenCorrectedStrong.first_ne_neg_one p v hb hv) hz
  have hz' : d.Q * U * Carrier65.strong d = 1 := by
    have he := ThirteenCorrectedStrong.correctedStrong_eq d
    change d.P * d.Q * U * ThirteenCorrectedStrong.correctedStrong d - 1 = 0 at hz
    rw [he, hP] at hz
    simpa using sub_eq_zero.mp hz
  have hd : d.delta = (d.a + 2)^2 - 1 := Carrier65.delta_shape p (parent p v 1 1)
  have hsne : Carrier65.strong d ≠ -1 := by
    unfold Carrier65.strong
    rw [hd]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hs : Carrier65.strong d = 1 :=
    (Int.isUnit_iff.mp (IsUnit.of_mul_eq_one_right _ hz')).resolve_right hsne
  have hQne : d.Q ≠ -1 := by
    change d.D^2 - d.delta*d.c^2 ≠ -1
    rw [hd]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hQ : d.Q = 1 := by
    have he : U * d.Q = 1 := by rw [hs] at hz'; nlinarith only [hz']
    exact (Int.isUnit_iff.mp (IsUnit.of_mul_eq_one_right _ he)).resolve_right hQne
  have hU : U = 1 := by simpa [hQ, hs] using hz'
  have hc : d.delta * (d.f^2 - 1) = d.S^2 := by
    have hs' : d.f^2 - 1 = d.delta * (d.i*d.c^2)^2 := by
      change d.f^2 - d.delta*(d.i*d.c^2)^2 = 1 at hs
      linarith
    rw [hs']
    change d.delta * (d.delta * (d.i*d.c^2)^2) = (d.i*d.delta*d.c^2)^2
    ring
  refine ⟨hs, ?_⟩
  change d.delta * (d.f^2-1) * (d.V^2-ordinate^2)+ordinate^2=1 at hU
  rw [hc] at hU
  nlinarith only [hU]

theorem seed_estimates {c delta i f S : ℤ} (hc : 2 ≤ c) (hd : 0 < delta)
    (hi : 0 < i) (hs : f^2 - delta*(i*c^2)^2 = 1)
    (hS : S = i*delta*c^2) : c + 1 ≤ f^2 ∧ c^2 < S^2 := by
  have hu : c^2 ≤ i*c^2 := by
    simpa using mul_le_mul_of_nonneg_right (show 1 ≤ i from hi) (sq_nonneg c)
  have hu' : c ≤ i*c^2 := by nlinarith
  have hu2 : c^2 ≤ (i*c^2)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu') (show 0 ≤ i*c^2+c by positivity)]
  have hd2 : (i*c^2)^2 ≤ delta*(i*c^2)^2 := by
    simpa using mul_le_mul_of_nonneg_right (show 1 ≤ delta from hd) (sq_nonneg (i*c^2))
  have hds : i*c^2 ≤ S := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ delta from hd) (show 0 ≤ i*c^2 by positivity)
    nlinarith only [hh, hS]
  have hcS : c < S := by nlinarith
  refine ⟨by nlinarith, ?_⟩
  nlinarith [mul_pos (sub_pos.mpr hcS) (show 0 < S+c by omega)]

theorem mixed_bounds {c f S L V ordinate : ℤ} (hc : 2 ≤ c)
    (hf : c+1 ≤ f^2) (hSc : c^2 < S^2) (hV : V = f^2*L-c)
    (hn : S^2*V^2-(S^2-1)*ordinate^2=1) :
    L ≠ 0 ∧ |V| ≤ L*V ∧ L*V ≤ V^2 := by
  have hL : L ≠ 0 := by
    intro hL
    have he : V = -c := by simp [hL] at hV; exact hV
    rw [he] at hn
    have hprod : (S^2-1)*(ordinate^2-c^2)=c^2-1 := by nlinarith only [hn]
    have hgap : 0 < ordinate^2-c^2 := by
      by_contra hh
      have hh' := mul_nonpos_of_nonneg_of_nonpos
        (by nlinarith : 0 ≤ S^2-1) (by omega : ordinate^2-c^2 ≤ 0)
      nlinarith
    have hlarge := mul_le_mul_of_nonneg_left (show 1 ≤ ordinate^2-c^2 from hgap)
      (by nlinarith : 0 ≤ S^2-1)
    nlinarith
  refine ⟨hL, ?_⟩
  rcases lt_or_gt_of_ne hL with hL | hL
  · have hL1 : L ≤ -1 := by omega
    have hm := mul_nonpos_of_nonneg_of_nonpos (by nlinarith : 0 ≤ f^2-1) hL.le
    have hVL : V ≤ L := by nlinarith
    have hV0 : V ≤ 0 := by omega
    rw [abs_of_nonpos hV0]
    constructor
    · nlinarith [mul_nonneg (by omega : 0 ≤ -L-1) (neg_nonneg.mpr hV0)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hVL) (neg_nonneg.mpr hV0)]
  · have hL1 : 1 ≤ L := hL
    have hm := mul_nonneg (by nlinarith : 0 ≤ f^2-c-1) (by omega : 0 ≤ L)
    have hmc := mul_nonneg (by omega : 0 ≤ c) (by omega : 0 ≤ L-1)
    have hVL : L ≤ V := by nlinarith
    have hV0 : 0 ≤ V := by omega
    rw [abs_of_nonneg hV0]
    constructor
    · nlinarith [mul_nonneg (by omega : 0 ≤ L-1) hV0]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hVL) hV0]

theorem carrier_nonneg {base m transport A V ordinate : ℤ}
    (hb : 0 < base) (hm : 0 < m) (hA : |V| ≤ A)
    (hy : ordinate = 1+4*(base*(m-A*transport)-transport))
    (hsmall : |ordinate| < 2*|V|) : 0 ≤ transport := by
  by_contra hG
  have hG : transport ≤ -1 := by omega
  have hA0 : 0 ≤ A := le_trans (abs_nonneg V) hA
  have hbaseA := mul_le_mul_of_nonneg_right (show 1 ≤ base from hb) hA0
  have hbm : 1 ≤ base*m := mul_pos hb hm
  have hprod := mul_nonneg (show 0 ≤ 1+base*A by positivity)
    (by omega : 0 ≤ -transport-1)
  nlinarith [le_abs_self ordinate]

theorem subtractive_positive {base m transport A V ordinate : ℤ}
    (hb : 0 < base) (hm : 0 < m) (hG : 0 ≤ transport) (hA : |V| ≤ A)
    (hy : ordinate = 1+4*(base*(m-V^2*transport)-transport))
    (hsmall : |ordinate| < 2*|V|) : 0 < m-transport*(V^2-A) := by
  by_cases hG0 : transport=0
  · simpa [hG0] using hm
  have hG1 : 1 ≤ transport := by omega
  have hA0 : 0 ≤ A := le_trans (abs_nonneg V) hA
  have hAG := mul_le_mul_of_nonneg_left hG1 hA0
  have hprod := mul_le_mul_of_nonneg_left (le_trans hA (by simpa [mul_comm] using hAG))
    (show 0 ≤ base from hb.le)
  have hbaseV := mul_le_mul_of_nonneg_right (show 1 ≤ base from hb) (abs_nonneg V)
  have hlo := neg_abs_le ordinate
  have he : 4*base*(m-transport*(V^2-A)) = 4*base*A*transport+4*transport+ordinate-1 := by
    rw [hy]
    ring
  have hpos : 0 < 4*base*(m-transport*(V^2-A)) := by nlinarith
  exact (mul_pos_iff_of_pos_left (show 0 < 4*base by positivity)).mp hpos

theorem bounds_of_normal_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (ordinate : ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : normalValue p v ordinate = 0) :
    L p v ≠ 0 ∧ |(data p v).V| ≤ L p v * (data p v).V ∧
      L p v * (data p v).V ≤ (data p v).V^2 ∧
      |ordinate| < 2 * |(data p v).V| := by
  obtain ⟨hs, hn⟩ := norms_of_zero p v ordinate hb hv hz
  have hp := parent_pos p v hb hv (z := 1) (y := 1) (by norm_num) (by norm_num)
  have hd := Carrier65.delta_pos p (parent p v 1 1) hb hp
  have hi : 0 < (data p v).i := mul_pos (mul_pos hb (hv 0)) (hv 4)
  have hY := (Carrier65.scales_pos p (parent p v 1 1) hb hp).2.1
  have hk : 2 ≤ (data p v).k := by
    change 2 ≤ v 9 + v 10
    have := hv 9
    have := hv 10
    omega
  have hc : 2 ≤ (data p v).c := by
    change 2 ≤ (data p v).k * (data p v).Y + v 9
    change 0 < (data p v).Y at hY
    have := hv 9
    nlinarith
  have he := seed_estimates hc hd hi hs
    (rfl : (data p v).S = (data p v).i*(data p v).delta*(data p v).c^2)
  have hm := mixed_bounds hc he.1 he.2
    (rfl : (data p v).V = (data p v).f^2 * L p v - (data p v).c) hn
  exact ⟨hm.1, hm.2.1, hm.2.2,
    (auxiliary_estimates (scale_ge_two p v hb hv) hn).2⟩

theorem setM_pos (v : Fin 13 → ℤ) (m : ℤ) (hv : ∀ j, 0 < v j) (hm : 0 < m) :
    ∀ j, 0 < setM v m j := by
  intro j
  by_cases hj : j = 11
  · simpa [setM, hj] using hm
  · simpa [setM, hj] using hv j

/-- Every positive new zero, without a canonical-witness restriction. -/
theorem positive_toOld (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : value p v = 0) :
    (∀ j, 0 < toOld p v j) ∧ ThirteenCorrectedStrong.value p (toOld p v) = 0 := by
  have h := bounds_of_normal_zero p v (y p v) hb hv hz
  have hG := carrier_nonneg (mul_pos hb (hv 0)) (hv 11) h.2.1 rfl h.2.2.2
  have hcor : 0 ≤ correction p v := mul_nonneg hG (sub_nonneg.mpr h.2.2.1)
  exact ⟨setM_pos v _ hv (add_pos_of_pos_of_nonneg (hv 11) hcor),
    by rw [old_toOld]; exact hz⟩

/-- The subtractive map is positive on every old zero. It is not claimed
positive on arbitrary positive inputs. -/
theorem positive_toNew (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : ThirteenCorrectedStrong.value p v = 0) :
    (∀ j, 0 < toNew p v j) ∧ value p (toNew p v) = 0 := by
  have hn : normalValue p v (signedY p v) = 0 := by rwa [← old_value]
  have h := bounds_of_normal_zero p v (signedY p v) hb hv hn
  have hG := carrier_nonneg (mul_pos hb (hv 0)) (hv 11)
    (le_trans h.2.1 h.2.2.1) (signedY_shape p v) h.2.2.2
  have hm := subtractive_positive (mul_pos hb (hv 0)) (hv 11) hG h.2.1
    (signedY_shape p v) h.2.2.2
  exact ⟨setM_pos v _ hv hm, by rw [new_toNew]; exact hz⟩

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp [value, normalValue, y, L, G, data, Carrier65.core, parent, b,
    ThirteenCorrectedStrong.correctedStrong, map_add, map_sub, map_mul,
    map_pow, map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem exists_positive_zero_iff (p : Fin 4 → ℤ) (hb : 0 < p 0) :
    CurrentCarrierArithmetic2011.PositiveZero (polynomial p) ↔
      CurrentCarrierArithmetic2011.PositiveZero (ThirteenCorrectedStrong.polynomial p) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    rw [eval_polynomial] at hz
    obtain ⟨hp, hz⟩ := positive_toOld p v hb hv hz
    exact ⟨toOld p v, hp, by rwa [ThirteenCorrectedStrong.eval_polynomial]⟩
  · rintro ⟨v, hv, hz⟩
    rw [ThirteenCorrectedStrong.eval_polynomial] at hz
    obtain ⟨hp, hz⟩ := positive_toNew p v hb hv hz
    exact ⟨toNew p v, hp, by rwa [eval_polynomial]⟩

attribute [local irreducible] CurrentKernel2011.K

noncomputable def currentPolynomial : MvPolynomial (Fin 13) ℤ :=
  polynomial CurrentWindowCarry2011.ports

/-- External Lean consistency transfer at the complete current2011 ports.
This theorem is not an HA derivation or an exact-degree theorem. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  exact (not_congr (exists_positive_zero_iff _ hb)).trans
    ThirteenCorrectedStrong.no_current_positive_zero_iff_conZFC

/-- The mixed carrier without the optional first-norm correction. Its
separate graph uses 72 operations, with exact degree124. -/
def normalValue72 (p : Fin 4 → A) (v : Fin 13 → A) (ordinate : A) : A :=
  let d := data p v
  d.P * d.Q * (d.delta * (d.f^2 - 1) * (d.V^2 - ordinate^2) + ordinate^2) *
    Carrier65.strong d - 1

def value72 (p : Fin 4 → A) (v : Fin 13 → A) : A := normalValue72 p v (y p v)

theorem old_value72 (p : Fin 4 → A) (v : Fin 13 → A) :
    ThirteenCarrier.value71 p v = normalValue72 p v (signedY p v) := rfl

theorem old72_toOld (p : Fin 4 → A) (v : Fin 13 → A) :
    ThirteenCarrier.value71 p (toOld p v) = value72 p v := by
  rw [old_value72, signedY_toOld]
  simp only [normalValue72, value72, toOld, data_setM]

theorem new72_toNew (p : Fin 4 → A) (v : Fin 13 → A) :
    value72 p (toNew p v) = ThirteenCarrier.value71 p v := by
  rw [value72, y_toNew, old_value72]
  simp only [normalValue72, toNew, data_setM]

/-- The optional correction still vanishes on every positive zero of either
mixed polynomial; P=1 is obtained separately from the relevant unit product. -/
theorem positive_zero_iff72 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value p v = 0 ↔ value72 p v = 0 := by
  have same (hP : (data p v).P = 1) : value p v = value72 p v := by
    dsimp only [value, normalValue, value72, normalValue72]
    rw [ThirteenCorrectedStrong.correctedStrong_eq, hP]
    ring
  constructor <;> intro hz
  · have hP := ThirteenCorrectedStrong.first_eq_one_of_product
      (ThirteenCorrectedStrong.first_ne_neg_one p v hb hv) hz
    rwa [← same hP]
  · have hP := ThirteenCorrectedStrong.first_eq_one_of_product
      (ThirteenCorrectedStrong.first_ne_neg_one p v hb hv) hz
    rwa [same hP]

theorem positive72_toOld (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : value72 p v = 0) :
    (∀ j, 0 < toOld p v j) ∧ ThirteenCarrier.value71 p (toOld p v) = 0 := by
  have h := positive_toOld p v hb hv ((positive_zero_iff72 p v hb hv).mpr hz)
  exact ⟨h.1, by rwa [old72_toOld]⟩

theorem positive72_toNew (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : ThirteenCarrier.value71 p v = 0) :
    (∀ j, 0 < toNew p v j) ∧ value72 p (toNew p v) = 0 := by
  have h := positive_toNew p v hb hv
    ((ThirteenCorrectedStrong.positive_zero_iff p v hb hv).mpr hz)
  exact ⟨h.1, by rwa [new72_toNew]⟩

theorem value72_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value72 p v) = value72 (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp [value72, normalValue72, y, L, G, data, Carrier65.core, parent, b,
    Carrier65.strong, map_add, map_sub, map_mul, map_pow, map_ofNat]

noncomputable def polynomial72 (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value72 (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial72 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial72 p) = value72 p v := by
  simpa only [polynomial72, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value72_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem exists_positive72_zero_iff (p : Fin 4 → ℤ) (hb : 0 < p 0) :
    CurrentCarrierArithmetic2011.PositiveZero (polynomial72 p) ↔
      CurrentCarrierArithmetic2011.PositiveZero (ThirteenCarrier.polynomial71 p) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    rw [eval_polynomial72] at hz
    obtain ⟨hp, hz⟩ := positive72_toOld p v hb hv hz
    exact ⟨toOld p v, hp, by rwa [ThirteenCarrier.eval_polynomial71]⟩
  · rintro ⟨v, hv, hz⟩
    rw [ThirteenCarrier.eval_polynomial71] at hz
    obtain ⟨hp, hz⟩ := positive72_toNew p v hb hv hz
    exact ⟨toNew p v, hp, by rwa [eval_polynomial72]⟩

noncomputable def currentPolynomial72 : MvPolynomial (Fin 13) ℤ :=
  polynomial72 CurrentWindowCarry2011.ports

theorem no_current_positive72_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial72) ↔
      DiophantineConsistency.ConZFC := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  exact (not_congr (exists_positive72_zero_iff _ hb)).trans
    CurrentPositiveZero2011.no_thirteen_positive_zero_iff_conZFC.2.2

end DiophantineConsistency.ThirteenLVCarrier
