import DiophantineConsistency.ModelRatio
import DiophantineConsistency.ModelProductPell
import DiophantineConsistency.ModelNineConds
import Mathlib.RingTheory.Coprime.Basic

/-! # The ratio stage of Jones's nine unknowns, in every model of `𝗜𝚺₁`

Internal counterparts of `Jones1982.Nine.ratio_sound` and `ratio_complete`.
The free quantities live in the ring of differences (`ofModel`, a
`NinePolynomial.RingVars (DiffRing V)` of model naturals); the conditions
`ModelNineConds.Conds` on them are equivalent to the central binomial
divisibility `N² ∣ C(2R, R)` together with `b` a power of two, up to the
margin `8g < G` (sound) and `32g < G` (complete).

The model-natural quantities `Q.U … Q.I` mirror `Jones1982.Nine.NatQ`; the
cast lemmas identify each field of `ofModel` with the image of its natural
quantity, with the truncated-subtraction side conditions made explicit.
The two directions then follow Jones: the product-Pell square gives
`C = ψ_A(2R+1)` (`ModelProductPell.lemma_2_27`), the base-two congruence
modulo `J = 4A - 5` is `ModelExponentialCongruence.pow_congruence`, and the
ratio method is `ModelRatio.lemma_2_25` / `exists_B25core`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelNineRatio
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ModelArithmetic NinePolynomial ArithmeticPellRecurrence
  ArithmeticBinomPascal
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The free quantities of model naturals, in the ring of differences. -/
def ofModel (R N b g G h s w φ i j : V) : RingVars (DiffRing V) :=
  ⟨ι R, ι N, ι b, ι g, ι G, ι h, ι s, ι w, ι φ, ι i, ι j⟩

/-! ### Generic transfer facts -/

theorem ι_sub_of_le {a c : V} (h : c ≤ a) : ι (a - c) = ι a - ι c := by
  have e : ι (a - c) + ι c = ι a := by rw [← map_add, tsub_add_cancel_of_le h]
  linear_combination e

theorem isSquare_ι (x : V) : IsSquare (ι x) ↔ ∃ r : V, x = r * r := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨t, ht⟩ := nonneg_iff.mp (abs_nonneg r)
    refine ⟨t, ι_injective ?_⟩
    rw [hr, map_mul, ← ht, abs_mul_abs_self]
  · rintro ⟨r, rfl⟩
    exact ⟨ι r, map_mul ι r r⟩

/-- A multiple of `J` strictly between `-J` and `J` vanishes. -/
theorem eq_zero_of_dvd_of_abs_lt {J x : DiffRing V} (hJ : 0 < J) (hd : J ∣ x)
    (h1 : x < J) (h2 : -J < x) : x = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rcases lt_trichotomy k 0 with hk | hk | hk
  · exfalso
    have hk1 : (1 : DiffRing V) ≤ -k := model_discrete (-k) (by linarith)
    have h3 : J * 1 ≤ J * (-k) := mul_le_mul_of_nonneg_left hk1 hJ.le
    linarith
  · rw [hk, mul_zero]
  · exfalso
    have hk1 : (1 : DiffRing V) ≤ k := model_discrete k hk
    have h3 : J * 1 ≤ J * k := mul_le_mul_of_nonneg_left hk1 hJ.le
    linarith

/-- Equal remainders iff the difference is divisible, read in `DiffRing V`. -/
theorem dvd_sub_iff_mod_eq {F H C : V} (hF : 0 < F) :
    ι F ∣ ι H - ι C ↔ H % F = C % F := by
  have eH := div_add_mod H F
  have eC := div_add_mod C F
  have hH : ι H = ι F * ι (H / F) + ι (H % F) := by rw [← map_mul, ← map_add, eH]
  have hC : ι C = ι F * ι (C / F) + ι (C % F) := by rw [← map_mul, ← map_add, eC]
  constructor
  · intro hd
    have hr : ι F ∣ ι (H % F) - ι (C % F) := by
      have e : ι (H % F) - ι (C % F) =
          (ι H - ι C) - ι F * (ι (H / F) - ι (C / F)) := by rw [hH, hC]; ring
      rw [e]; exact dvd_sub hd (dvd_mul_right _ _)
    have hlt1 : ι (H % F) < ι F := ι_lt_ι.mpr (mod_lt H hF)
    have hlt2 : ι (C % F) < ι F := ι_lt_ι.mpr (mod_lt C hF)
    have h0 := eq_zero_of_dvd_of_abs_lt (ι_lt_ι.mpr hF |>.trans_eq' (map_zero ι).symm |> fun h => by
        simpa using h) hr
      (by linarith [ι_nonneg (C % F)]) (by linarith [ι_nonneg (H % F)])
    exact ι_injective (sub_eq_zero.mp h0)
  · intro he
    refine ⟨ι (H / F) - ι (C / F), ?_⟩
    rw [hH, hC, he]; ring

/-! ### The natural quantities (`Jones1982.Nine.NatQ`) -/

namespace Q
variable (R N b h s w φ i j : V)
def U : V := N * N * w
def Y : V := N * N * s
def M : V := R * Y N s
def P : V := 2 * M R N s * M R N s * U N w
def K : V := R + 1 + h * (P R N s w - 1)
def A : V := M R N s * (U N w + 1)
def B' : V := 2 * R + 1
def W : V := b * w
def C : V := B' R + W b w + φ
def J : V := 4 * A R N s w - 5
def D : V := (A R N s w * A R N s w - 1) * C R b w φ * C R b w φ + 1
def E : V := i * J R N s w * D R N b s w φ * C R b w φ * C R b w φ
def F : V := (A R N s w * A R N s w - 1) * E R N b s w φ i * E R N b s w φ i + 1
def Gp : V := A R N s w + F R N b s w φ i * (C R b w φ * D R N b s w φ + 1 - A R N s w)
def H : V := B' R + j * C R b w φ
def I : V := (Gp R N b s w φ i * Gp R N b s w φ i - 1) * H R b w φ j * H R b w φ j + 1
end Q

section Casts
variable (R N b g G h s w φ i j : V)

local notation "𝒱" => ofModel R N b g G h s w φ i j

theorem cU : (𝒱).U = ι (Q.U N w) := by
  simp only [RingVars.U, ofModel, Q.U, map_mul]; ring
theorem cY : (𝒱).Y = ι (Q.Y N s) := by
  simp only [RingVars.Y, ofModel, Q.Y, map_mul]; ring
theorem cM : (𝒱).M = ι (Q.M R N s) := by
  simp only [RingVars.M, RingVars.Y, ofModel, Q.M, Q.Y, map_mul]; ring
theorem cP : (𝒱).P = ι (Q.P R N s w) := by
  simp only [RingVars.P, RingVars.M, RingVars.Y, RingVars.U, ofModel, Q.P, Q.M, Q.Y, Q.U,
    map_mul, map_ofNat]; ring
theorem cA : (𝒱).A = ι (Q.A R N s w) := by
  simp only [RingVars.A, RingVars.M, RingVars.Y, RingVars.U, ofModel, Q.A, Q.M, Q.Y, Q.U,
    map_mul, map_add, map_one]; ring
theorem cB' : (𝒱).B' = ι (Q.B' R) := by
  simp only [RingVars.B', ofModel, Q.B', map_mul, map_add, map_one, map_ofNat]
theorem cW : (𝒱).W = ι (Q.W b w) := by
  simp only [RingVars.W, ofModel, Q.W, map_mul]
theorem cC : (𝒱).C = ι (Q.C R b w φ) := by
  show (𝒱).B' + (𝒱).W + (𝒱).φ = _
  rw [cB', cW]
  simp only [Q.C, map_add, ofModel]

variable {R N b g G h s w φ i j}

theorem cK (hP1 : 1 ≤ Q.P R N s w) : (𝒱).K = ι (Q.K R N h s w) := by
  show (𝒱).R + 1 + (𝒱).h * ((𝒱).P - 1) = _
  rw [cP]
  simp only [Q.K, map_add, map_mul, map_one, ι_sub_of_le hP1, ofModel]

theorem cJ (hA5 : 5 ≤ 4 * Q.A R N s w) : (𝒱).J = ι (Q.J R N s w) := by
  show 4 * (𝒱).A - 5 = _
  rw [cA]
  simp only [Q.J, ι_sub_of_le hA5, map_mul, map_ofNat]

theorem cD (hA1 : 1 ≤ Q.A R N s w * Q.A R N s w) : (𝒱).D = ι (Q.D R N b s w φ) := by
  show ((𝒱).A ^ 2 - 1) * (𝒱).C ^ 2 + 1 = _
  rw [cA, cC]
  simp only [Q.D, map_add, map_mul, map_one, ι_sub_of_le hA1]
  ring

theorem cE (hA5 : 5 ≤ 4 * Q.A R N s w) (hA1 : 1 ≤ Q.A R N s w * Q.A R N s w) :
    (𝒱).E = ι (Q.E R N b s w φ i) := by
  show (𝒱).i * (𝒱).J * (𝒱).D * (𝒱).C ^ 2 = _
  rw [cJ hA5, cD hA1, cC]
  simp only [Q.E, map_mul, ofModel]
  ring

theorem cF (hA5 : 5 ≤ 4 * Q.A R N s w) (hA1 : 1 ≤ Q.A R N s w * Q.A R N s w) :
    (𝒱).F = ι (Q.F R N b s w φ i) := by
  show ((𝒱).A ^ 2 - 1) * (𝒱).E ^ 2 + 1 = _
  rw [cA, cE hA5 hA1]
  simp only [Q.F, map_add, map_mul, map_one, ι_sub_of_le hA1]
  ring

theorem cGp (hA5 : 5 ≤ 4 * Q.A R N s w) (hA1 : 1 ≤ Q.A R N s w * Q.A R N s w)
    (hCD : Q.A R N s w ≤ Q.C R b w φ * Q.D R N b s w φ + 1) :
    (𝒱).Gp = ι (Q.Gp R N b s w φ i) := by
  show (𝒱).A + (𝒱).F * ((𝒱).C * (𝒱).D + 1 - (𝒱).A) = _
  rw [cA, cF hA5 hA1, cC, cD hA1]
  simp only [Q.Gp, map_add, map_mul, map_one, ι_sub_of_le hCD]

theorem cH : (𝒱).H = ι (Q.H R b w φ j) := by
  show (𝒱).B' + (𝒱).j * (𝒱).C = _
  rw [cB', cC]
  simp only [Q.H, map_add, map_mul, ofModel]

theorem cI (hA5 : 5 ≤ 4 * Q.A R N s w) (hA1 : 1 ≤ Q.A R N s w * Q.A R N s w)
    (hCD : Q.A R N s w ≤ Q.C R b w φ * Q.D R N b s w φ + 1)
    (hG1 : 1 ≤ Q.Gp R N b s w φ i * Q.Gp R N b s w φ i) :
    (𝒱).I = ι (Q.I R N b s w φ i j) := by
  show ((𝒱).Gp ^ 2 - 1) * (𝒱).H ^ 2 + 1 = _
  rw [cGp hA5 hA1 hCD, cH]
  simp only [Q.I, map_add, map_mul, map_one, ι_sub_of_le hG1]
  ring

theorem cQ : (𝒱).Q = 3 * ι (Q.W b w) * ι (Q.C R b w φ) - 2 * (ι (Q.W b w) ^ 2 - 1) := by
  show 3 * (𝒱).W * (𝒱).C - 2 * ((𝒱).W ^ 2 - 1) = _
  rw [cW, cC]

end Casts

/-! ### Sizes -/

theorem sizes {R N s w : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hs : 0 < s) (hw : 0 < w) :
    1 ≤ Q.P R N s w ∧ 2 ≤ Q.A R N s w := by
  have hNN : 64 ≤ N * N := calc
    (64 : V) = 8 * 8 := by norm_num
    _ ≤ N * N := mul_le_mul hN hN (by simp) (by simp)
  have hU : 64 ≤ Q.U N w :=
    le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hw))
  have hY : 64 ≤ Q.Y N s :=
    le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs))
  obtain ⟨-, -, hA2, hP2⟩ := ModelRatio.basic_sizes R (Q.Y N s) (Q.U N w) (Q.M R N s)
    (Q.A R N s w) (Q.P R N s w) hR hY hU rfl rfl rfl
  exact ⟨le_trans one_le_two hP2, hA2⟩

theorem one_le_sq_of_two_le {x : V} (hx : 2 ≤ x) : 1 ≤ x * x :=
  le_trans (le_trans one_le_two hx) (le_mul_of_one_le_left (by simp) (le_trans one_le_two hx))

theorem five_le_four_mul {x : V} (hx : 2 ≤ x) : 5 ≤ 4 * x :=
  le_trans (by norm_num : (5 : V) ≤ 4 * 2) (mul_le_mul_of_nonneg_left hx (by simp))

theorem A_le_CD {R N b s w φ : V} (hA2 : 2 ≤ Q.A R N s w) (hC : 1 ≤ Q.C R b w φ) :
    Q.A R N s w ≤ Q.C R b w φ * Q.D R N b s w φ + 1 := by
  have hA1 := one_le_sq_of_two_le hA2
  have hD : Q.A R N s w * Q.A R N s w ≤ Q.D R N b s w φ := by
    apply ι_le_ι.mp
    have hDi : ι (Q.D R N b s w φ) = (ι (Q.A R N s w) * ι (Q.A R N s w) - 1) *
        ι (Q.C R b w φ) * ι (Q.C R b w φ) + 1 := by
      simp only [Q.D, map_add, map_mul, map_one, ι_sub_of_le hA1]
    rw [hDi, map_mul]
    have hc : (1 : DiffRing V) ≤ ι (Q.C R b w φ) := by
      simpa only [map_one] using ι_le_ι.mpr hC
    have ha : (1 : DiffRing V) ≤ ι (Q.A R N s w) * ι (Q.A R N s w) := by
      simpa only [map_one, map_mul] using ι_le_ι.mpr hA1
    nlinarith [mul_le_mul hc hc zero_le_one (by linarith : (0 : DiffRing V) ≤ ι (Q.C R b w φ))]
  have hAD : Q.A R N s w ≤ Q.D R N b s w φ :=
    le_trans (le_mul_of_one_le_left (by simp) (le_trans one_le_two hA2)) hD
  calc Q.A R N s w ≤ Q.D R N b s w φ := hAD
    _ ≤ Q.C R b w φ * Q.D R N b s w φ := le_mul_of_one_le_left (by simp) hC
    _ ≤ Q.C R b w φ * Q.D R N b s w φ + 1 := le_add_of_nonneg_right (by simp)

theorem odd_B' (R : V) : Q.B' R % 2 = 1 := by
  have e : Q.B' R = 1 + R * 2 := by simp only [Q.B']; ring
  rw [e, mod_add_mul 1 R (by norm_num : (0 : V) < 2), mod_eq_self_of_lt (by norm_num : (1 : V) < 2)]

/-- The coprimality certificate `F - J·(…) = 1` of `Jones1982.Nine.isCoprime_F_J`. -/
theorem isCoprime_F_J (v : RingVars (DiffRing V)) : IsCoprime v.F v.J := by
  refine ⟨1, -((v.A ^ 2 - 1) * v.i ^ 2 * v.J * v.D ^ 2 * v.C ^ 4), ?_⟩
  simp only [RingVars.F, RingVars.E]
  ring

/-! ### The two directions -/

set_option maxHeartbeats 1000000 in
/-- **Sufficiency** (`Jones1982.Nine.ratio_sound`), in every model. -/
theorem ratio_sound {R N b g G h s w φ i j : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R)
    (hb : 0 < b) (hbN : b ≤ N) (hG : 0 < G) (hh : 0 < h) (hs : 0 < s) (hw : 0 < w)
    (hi : 0 < i) (hj : 0 < j) (hc : ModelNineConds.Conds (ofModel R N b g G h s w φ i j)) :
    N * N ∣ binom (2 * R) R ∧ (∃ k, b = Exp.exp k) ∧ 8 * g < G := by
  obtain ⟨hP1, hA2⟩ := sizes hR hN hs hw
  have hA1 := one_le_sq_of_two_le hA2
  have hA5 := five_le_four_mul hA2
  have hW0 : 0 < Q.W b w := mul_pos hb hw
  have hB1 : 1 < Q.B' R := by
    have : (1 : V) < 2 * 8 + 1 := by norm_num
    exact lt_of_lt_of_le this (by simp only [Q.B']; exact add_le_add (mul_le_mul_of_nonneg_left hR (by simp)) le_rfl)
  have hBC : Q.B' R ≤ Q.C R b w φ := by
    simp only [Q.C]; exact le_trans (le_add_of_nonneg_right (by simp)) (le_add_of_nonneg_right (by simp))
  have hC1 : 1 ≤ Q.C R b w φ := le_trans hB1.le hBC
  have hCD := A_le_CD (b := b) (φ := φ) hA2 hC1
  have hGp1 : 1 ≤ Q.Gp R N b s w φ i * Q.Gp R N b s w φ i := by
    have : 1 ≤ Q.Gp R N b s w φ i :=
      le_trans (le_trans one_le_two hA2) (le_add_of_nonneg_right (by simp))
    exact le_trans this (le_mul_of_one_le_left (by simp) this)
  have hF1 : 1 ≤ Q.F R N b s w φ i := le_add_of_nonneg_left (by simp)
  obtain ⟨sq1, sq2, hdvd, hpos⟩ := hc
  -- the casts
  rw [cP, cK hP1] at sq1
  rw [cD hA1, cF hA5 hA1, cI hA5 hA1 hCD hGp1] at sq2
  rw [cJ hA5, cF hA5 hA1, cQ, cH, cC] at hdvd
  rw [cK hP1, cY, cC] at hpos
  simp only [ofModel] at hpos
  have hGz : (0 : DiffRing V) < ι G := by simpa only [map_zero] using ι_lt_ι.mpr hG
  have hK1 : (1 : DiffRing V) ≤ ι (Q.K R N h s w) := by
    have : 1 ≤ Q.K R N h s w := le_trans (by norm_num : (1 : V) ≤ 8 + 1)
      (le_add_of_le_of_nonneg (add_le_add hR le_rfl) (by simp))
    simpa only [map_one] using ι_le_ι.mpr this
  have hKz : (0 : DiffRing V) < ι (Q.K R N h s w) ^ 2 := by positivity
  have hg0 : (0 : DiffRing V) ≤ ι g := ι_nonneg g
  -- (B3) and the ceiling
  have hB3 : 4 * (ι (Q.C R b w φ) - ι (Q.K R N h s w) * ι (Q.Y N s)) ^ 2 < ι (Q.K R N h s w) ^ 2 := by
    have h1 : 0 ≤ 8 * ι g * ι (Q.K R N h s w) ^ 2 := by positivity
    have h2 : 4 * (ι (Q.C R b w φ) - ι (Q.K R N h s w) * ι (Q.Y N s)) ^ 2 * ι G < ι (Q.K R N h s w) ^ 2 * ι G := by linarith
    exact lt_of_mul_lt_mul_right h2 hGz.le
  have hgG : 8 * g < G := by
    have h1 : 0 ≤ 4 * (ι (Q.C R b w φ) - ι (Q.K R N h s w) * ι (Q.Y N s)) ^ 2 * ι G := by positivity
    have h2 : 8 * ι g * ι (Q.K R N h s w) ^ 2 < ι G * ι (Q.K R N h s w) ^ 2 := by linarith
    have h3 : ι (8 * g) < ι G := by
      rw [map_mul, map_ofNat]; exact lt_of_mul_lt_mul_right h2 hKz.le
    exact ι_lt_ι.mp h3
  -- the two divisibilities
  have hcop : IsCoprime (ι (Q.F R N b s w φ i)) (ι (Q.J R N s w)) := by
    have := isCoprime_F_J (ofModel R N b g G h s w φ i j)
    rwa [cF hA5 hA1, cJ hA5] at this
  have hFHC : ι (Q.F R N b s w φ i) ∣ ι (Q.H R b w φ j) - ι (Q.C R b w φ) := by
    have h2 : ι (Q.F R N b s w φ i) ∣ (3 * ι (Q.W b w) * ι (Q.C R b w φ) - 2 * (ι (Q.W b w) ^ 2 - 1)) * ι (Q.F R N b s w φ i) + ι (Q.J R N s w) * (ι (Q.H R b w φ j) - ι (Q.C R b w φ)) :=
      (Dvd.intro_left _ rfl).trans hdvd
    have h1 : ι (Q.F R N b s w φ i) ∣ ι (Q.J R N s w) * (ι (Q.H R b w φ j) - ι (Q.C R b w φ)) := (dvd_add_right (Dvd.intro_left _ rfl)).1 h2
    exact hcop.dvd_of_dvd_mul_left h1
  have hJQ : ι (Q.J R N s w) ∣ (3 * ι (Q.W b w) * ι (Q.C R b w φ) - 2 * (ι (Q.W b w) ^ 2 - 1)) := by
    have h2 : ι (Q.J R N s w) ∣ (3 * ι (Q.W b w) * ι (Q.C R b w φ) - 2 * (ι (Q.W b w) ^ 2 - 1)) * ι (Q.F R N b s w φ i) + ι (Q.J R N s w) * (ι (Q.H R b w φ j) - ι (Q.C R b w φ)) := (Dvd.intro _ rfl).trans hdvd
    have h1 : ι (Q.J R N s w) ∣ (3 * ι (Q.W b w) * ι (Q.C R b w φ) - 2 * (ι (Q.W b w) ^ 2 - 1)) * ι (Q.F R N b s w φ i) := (dvd_add_left (Dvd.intro _ rfl)).1 h2
    exact hcop.symm.dvd_of_dvd_mul_right h1
  -- Lemma 2.27: the product-Pell square identifies `C`
  have hJ0 : 0 < Q.J R N s w := by
    simp only [Q.J]
    exact lt_tsub_of_add_lt_left (lt_of_lt_of_le (by norm_num : (5 : V) + 0 < 8)
      (le_trans (by norm_num : (8 : V) ≤ 4 * 2) (mul_le_mul_of_nonneg_left hA2 (by simp))))
  have hcong : Q.H R b w φ j % Q.F R N b s w φ i = Q.C R b w φ % Q.F R N b s w φ i :=
    (dvd_sub_iff_mod_eq (lt_of_lt_of_le (by norm_num) hF1)).mp hFHC
  have hpp : ModelProductPell.ProductPellConds (Q.A R N s w - 2 + 2) (Q.B' R) (Q.C R b w φ)
      (Q.J R N s w) i j (Q.D R N b s w φ) (Q.E R N b s w φ i) (Q.F R N b s w φ i)
      (Q.Gp R N b s w φ i) (Q.H R b w φ j) (Q.I R N b s w φ i j) := by
    rw [tsub_add_cancel_of_le hA2]
    refine ⟨(isSquare_ι _).mp ?_, hcong, ?_, rfl, ?_, ?_, rfl, ?_⟩
    · have e : ι (Q.D R N b s w φ * Q.F R N b s w φ i * Q.I R N b s w φ i j) =
          ι (Q.D R N b s w φ) * ι (Q.F R N b s w φ i) * ι (Q.I R N b s w φ i j) := by rw [map_mul, map_mul]
      rw [e]; exact sq2
    · apply ι_injective
      simp only [Q.D, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
    · apply ι_injective
      simp only [Q.F, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
    · apply ι_injective
      simp only [Q.Gp, map_add, map_mul, map_one, ι_sub_of_le hCD]; ring
    · apply ι_injective
      simp only [Q.I, map_add, map_mul, map_one, ι_sub_of_le hGp1]; ring
  have hψ : Q.C R b w φ = ycoord (Q.B' R) (Q.A R N s w - 2) :=
    (ModelProductPell.lemma_2_27 (Q.A R N s w - 2) (Q.B' R) (Q.C R b w φ) (Q.J R N s w)
      hB1 hBC (Or.inr (odd_B' R)) hJ0).mpr ⟨i, j, _, _, _, _, _, _, hi, hj, hpp⟩
  -- Lemma 2.25
  have hcore : ModelRatio.B25core R N b h s w (Q.W b w + φ) (Q.A R N s w) (Q.B' R)
      (Q.C R b w φ) (Q.K R N h s w) (Q.M R N s) (Q.P R N s w) (Q.U N w) 2 (Q.W b w)
      (Q.Y N s) := by
    refine ⟨rfl, ?_, hB3, rfl, rfl, rfl, rfl, by simp only [Q.C]; ring, rfl, rfl, rfl, rfl, hψ⟩
    have hPP : 1 ≤ Q.P R N s w * Q.P R N s w :=
      le_trans hP1 (le_mul_of_one_le_left (by simp) hP1)
    have e : ι ((Q.P R N s w * Q.P R N s w - 1) * Q.K R N h s w * Q.K R N h s w + 1) =
        (ι (Q.P R N s w) ^ 2 - 1) * ι (Q.K R N h s w) ^ 2 + 1 := by
      simp only [map_add, map_mul, map_one, ι_sub_of_le hPP]
      ring
    have hsq : IsSquare (ι ((Q.P R N s w * Q.P R N s w - 1) * Q.K R N h s w * Q.K R N h s w + 1)) := by
      rw [e]; exact sq1
    obtain ⟨r, hr⟩ := (isSquare_ι _).mp hsq
    exact ⟨r, hr.symm⟩
  have hB13 : (2 * ι (Q.A R N s w) * ι (2 : V) - ι (2 : V) * ι (2 : V) - 1 : DiffRing V) ∣
      ι (2 : V) * (ι (Q.W b w) ^ 2 - 1) - (ι (2 : V) ^ 2 - 1) * ι (Q.W b w) * ι (Q.C R b w φ) := by
    have hJd : ι (Q.J R N s w) = 4 * ι (Q.A R N s w) - 5 := by
      simp only [Q.J, ι_sub_of_le hA5, map_mul, map_ofNat]
    have e1 : (2 * ι (Q.A R N s w) * ι (2 : V) - ι (2 : V) * ι (2 : V) - 1 : DiffRing V) = ι (Q.J R N s w) := by
      rw [hJd, map_ofNat]; ring
    have e2 : ι (2 : V) * (ι (Q.W b w) ^ 2 - 1) - (ι (2 : V) ^ 2 - 1) * ι (Q.W b w) * ι (Q.C R b w φ) = -(3 * ι (Q.W b w) * ι (Q.C R b w φ) - 2 * (ι (Q.W b w) ^ 2 - 1)) := by
      rw [map_ofNat]; ring
    rw [e1, e2]; exact (dvd_neg).mpr hJQ
  obtain ⟨hdvd', hpow⟩ := (ModelRatio.lemma_2_25 R N b hR hN hbR hb hbN).mpr
    ⟨h, s, w, Q.W b w + φ, _, _, _, _, _, _, _, _, _, _, hh, hs, hw,
      lt_of_lt_of_le hW0 (le_add_of_nonneg_right (by simp)), hcore, hB13⟩
  exact ⟨hdvd', hpow, hgG⟩

set_option maxHeartbeats 1000000 in
/-- **Necessity** (`Jones1982.Nine.ratio_complete`), in every model. -/
theorem ratio_complete {R N b g G : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R)
    (hb : 0 < b) (hbN : b ≤ N) (hgG : 32 * g < G)
    (hdvd : N * N ∣ binom (2 * R) R) (hpow : ∃ k, b = Exp.exp k) :
    ∃ h s w φ i j : V, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < i ∧ 0 < j ∧
      ModelNineConds.Conds (ofModel R N b g G h s w φ i j) := by
  obtain ⟨h, s, w, φ₀, A, B', C, K, M, P, U, V', W, Y, hh, hs, hw, -, hcore, hW, hBWC, hB3s⟩ :=
    ModelRatio.exists_B25core R N b hR hN hbR hb hbN hdvd hpow
  obtain ⟨B1, B2, -, B4, B5, B6, B7, -, B9, B10, B11, -, B14⟩ := hcore
  subst B1 B4 B5 B6 B7 B9 B10 B11
  -- now every quantity is the corresponding `Q` quantity
  obtain ⟨hP1, hA2⟩ := sizes hR hN hs hw
  have hA1 := one_le_sq_of_two_le hA2
  have hA5 := five_le_four_mul hA2
  set φ := C - Q.B' R - Q.W b w with hφ
  have hBW : Q.B' R + Q.W b w ≤ C := hBWC.le
  have eC : Q.C R b w φ = C := by
    simp only [Q.C, hφ]
    rw [tsub_tsub]; exact add_tsub_cancel_of_le hBW
  have hB1 : 1 < Q.B' R := by
    have : (1 : V) < 2 * 8 + 1 := by norm_num
    exact lt_of_lt_of_le this (by simp only [Q.B']; exact add_le_add (mul_le_mul_of_nonneg_left hR (by simp)) le_rfl)
  have hBC : Q.B' R ≤ C := le_trans (le_add_of_nonneg_right (by simp)) hBW
  have hJ0 : 0 < Q.J R N s w := by
    simp only [Q.J]
    exact lt_tsub_of_add_lt_left (lt_of_lt_of_le (by norm_num : (5 : V) + 0 < 8)
      (le_trans (by norm_num : (8 : V) ≤ 4 * 2) (mul_le_mul_of_nonneg_left hA2 (by simp))))
  have hψ : C = ycoord (Q.B' R) (Q.A R N s w - 2) := B14
  obtain ⟨i, j, D, E, F, Gp, H, I, hi, hj, hpp⟩ :=
    (ModelProductPell.lemma_2_27 (Q.A R N s w - 2) (Q.B' R) C (Q.J R N s w)
      hB1 hBC (Or.inr (odd_B' R)) hJ0).mp hψ
  rw [tsub_add_cancel_of_le hA2] at hpp
  obtain ⟨⟨r, hsq⟩, hcong, A2, A3, A4, A5, A6, A7⟩ := hpp
  refine ⟨h, s, w, φ, i, j, hh, hs, hw, hi, hj, ?_⟩
  -- identify the product-Pell witnesses with the `Q` quantities
  have eD : Q.D R N b s w φ = D := by
    apply ι_injective
    have h2 := congrArg ι A2
    simp only [map_add, map_mul, map_one] at h2
    simp only [Q.D, map_add, map_mul, map_one, ι_sub_of_le hA1, eC]
    linear_combination -h2
  have eE : Q.E R N b s w φ i = E := by simp only [Q.E, eD, eC, A3]
  have eF : Q.F R N b s w φ i = F := by
    apply ι_injective
    have h2 := congrArg ι A4
    simp only [map_add, map_mul, map_one] at h2
    simp only [Q.F, map_add, map_mul, map_one, ι_sub_of_le hA1, eE]
    linear_combination -h2
  have hC1 : 1 ≤ Q.C R b w φ := by rw [eC]; exact le_trans hB1.le hBC
  have hCD := A_le_CD (b := b) (φ := φ) hA2 hC1
  have eG : Q.Gp R N b s w φ i = Gp := by
    apply ι_injective
    have h2 := congrArg ι A5
    simp only [map_add, map_mul, map_one] at h2
    have hCD' : Q.A R N s w ≤ C * D + 1 := by rw [← eC, ← eD]; exact hCD
    simp only [Q.Gp, eF, eC, eD, map_add, map_mul, map_one, ι_sub_of_le hCD']
    linear_combination -h2
  have eH : Q.H R b w φ j = H := by simp only [Q.H, eC, A6]
  have hGp1 : 1 ≤ Q.Gp R N b s w φ i * Q.Gp R N b s w φ i := by
    have : 1 ≤ Q.Gp R N b s w φ i :=
      le_trans (le_trans one_le_two hA2) (le_add_of_nonneg_right (by simp))
    exact le_trans this (le_mul_of_one_le_left (by simp) this)
  have eI : Q.I R N b s w φ i j = I := by
    apply ι_injective
    have h2 := congrArg ι A7
    simp only [map_add, map_mul, map_one] at h2
    have hG1' : 1 ≤ Gp * Gp := by rw [← eG]; exact hGp1
    simp only [Q.I, eG, eH, map_add, map_mul, map_one, ι_sub_of_le hG1']
    linear_combination -h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the first Pell square
    rw [cP, cK hP1]
    obtain ⟨z, hz⟩ := B2
    have hPP : 1 ≤ Q.P R N s w * Q.P R N s w :=
      le_trans hP1 (le_mul_of_one_le_left (by simp) hP1)
    have e : (ι (Q.P R N s w) ^ 2 - 1) * ι (Q.K R N h s w) ^ 2 + 1 =
        ι ((Q.P R N s w * Q.P R N s w - 1) * Q.K R N h s w * Q.K R N h s w + 1) := by
      simp only [map_add, map_mul, map_one, ι_sub_of_le hPP]; ring
    rw [e]
    exact (isSquare_ι _).mpr ⟨z, hz.symm⟩
  · -- the product-Pell square
    rw [cD hA1, cF hA5 hA1, cI hA5 hA1 hCD hGp1, eD, eF, eI, ← map_mul, ← map_mul]
    exact (isSquare_ι _).mpr ⟨r, hsq⟩
  · -- the divisibility
    rw [cJ hA5, cF hA5 hA1, cQ, cH, cC, eF, eH, eC]
    have hJQ : ι (Q.J R N s w) ∣ 3 * ι (Q.W b w) * ι C - 2 * (ι (Q.W b w) ^ 2 - 1) := by
      have hpc := ModelExponentialCongruence.pow_congruence (Q.A R N s w - 2) (Q.B' R)
      have hJd : (4 * ι (Q.A R N s w - 2) + 3 : DiffRing V) = ι (Q.J R N s w) := by
        simp only [Q.J, ι_sub_of_le hA5, ι_sub_of_le hA2, map_mul, map_ofNat]; ring
      have hWe : Q.W b w = Exp.exp (Q.B' R) := hW
      rw [hJd, ← hψ, ← hWe] at hpc
      exact hpc
    have hFHC : ι F ∣ ι H - ι C := by
      have hF0 : 0 < F := by rw [← eF]; exact lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_left (by simp))
      exact (dvd_sub_iff_mod_eq hF0).mpr hcong
    exact dvd_add (mul_dvd_mul hJQ (dvd_refl _)) (mul_dvd_mul_left _ hFHC)
  · -- the margin
    rw [cK hP1, cY, cC, eC]
    simp only [ofModel]
    have hK1 : (1 : DiffRing V) ≤ ι (Q.K R N h s w) := by
      have : 1 ≤ Q.K R N h s w := le_trans (by norm_num : (1 : V) ≤ 8 + 1)
        (le_add_of_le_of_nonneg (add_le_add hR le_rfl) (by simp))
      simpa only [map_one] using ι_le_ι.mpr this
    have hKz : (0 : DiffRing V) < ι (Q.K R N h s w) ^ 2 :=
      pow_pos (lt_of_lt_of_le zero_lt_one hK1) 2
    have hG0 : 0 < G := lt_of_le_of_lt (by simp) hgG
    have hGz : (0 : DiffRing V) < ι G := by simpa only [map_zero] using ι_lt_ι.mpr hG0
    have hg32 : 32 * ι g < ι G := by
      have h := ι_lt_ι.mpr hgG
      rw [map_mul, map_ofNat] at h
      exact h
    have h1 : 4096 * (4 * (ι C - ι (Q.K R N h s w) * ι (Q.Y N s)) ^ 2 * ι G) ≤
        2500 * (ι (Q.K R N h s w) ^ 2 * ι G) := by
      have hB3q : (4096 : DiffRing V) * (ι C - ι (Q.K R N h s w) * ι (Q.Y N s)) ^ 2 ≤
          625 * ι (Q.K R N h s w) ^ 2 := hB3s
      have := mul_le_mul_of_nonneg_right hB3q hGz.le
      linarith
    have h2 : 32 * ι g * ι (Q.K R N h s w) ^ 2 < ι G * ι (Q.K R N h s w) ^ 2 :=
      mul_lt_mul_of_pos_right hg32 hKz
    have h3 : 0 < ι (Q.K R N h s w) ^ 2 * ι G := mul_pos hKz hGz
    linarith

end DiophantineConsistency.ModelNineRatio
