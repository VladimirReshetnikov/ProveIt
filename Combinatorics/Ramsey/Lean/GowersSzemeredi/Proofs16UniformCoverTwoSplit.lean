import GowersSzemeredi.Proofs16UniformCoverTwoFejer
import GowersSzemeredi.Proofs16SplitStepBounds

/-! **The dimension-two class with a small family exponent** (Notes L.16j).

`splitUniformClass_two_fejer` obtains the dimension-two split class from the
power class through `toSplit`, which sets the family exponent equal to the
parameter degree: `a₂ = D₂ = 2^46`. The split recursion squares the family
exponent, so `a₂` fixes the class constant. But the dimension-two controls are
polynomials of fixed degree in the number `M = n·m` of pieces. The base
controls `famTwoQr`, `famTwoPb` are linear in `M`, so in the two bases
`ν = n + 1` and `W = splitW V θ γ ρ`:
* `uniTwoFejerCount_le_split`: the count is at most `ν^11·W^(2^41)`;
* `uniTwoFejerExp_inv_le_split`: the inverse width exponent is at most
  `ν^29·W^(2^46)`;
* `splitUniformClass_two_small`: **dimension two is a split class at
  `a₂ = 32`, `D₂ = 2^48`**.

With `a₂ ≤ 2^8` the split invariant runs at class constant `4` instead of
`14` (Notes L.16j). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- `(cubicBaseExponent q s)⁻¹ = 2^27·s⁻³·q⁴`, in two bases. -/
theorem cubicBaseExponent_inv_le_tb {q : Nat} {s ν W : Real} {a b c : Nat} (hW : 2 ≤ W)
    (hq : 0 < q) (hqw : (q : Real) ≤ ν ^ a * W ^ b) (hs : 0 < s) (hsw : s⁻¹ ≤ W ^ c) :
    (cubicBaseExponent q s)⁻¹ ≤ ν ^ (a * 4) * W ^ (27 + c * 3 + b * 4) := by
  have hW0 : 0 ≤ W := le_trans (by norm_num) hW
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hval : (cubicBaseExponent q s)⁻¹ = (2 : Real) ^ 27 * s⁻¹ ^ 3 * (q : Real) ^ 4 := by
    unfold cubicBaseExponent
    rw [show (-(27 : Real)) = -((27 : Nat) : Real) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    field_simp
  rw [hval]
  have h27 : (2 : Real) ^ 27 ≤ W ^ 27 := pow_le_pow_left₀ (by norm_num) hW 27
  have h3 : s⁻¹ ^ 3 ≤ W ^ (c * 3) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (inv_pos.mpr hs).le hsw 3
  have h4 := tb_pow hq0.le hqw 4
  calc (2 : Real) ^ 27 * s⁻¹ ^ 3 * (q : Real) ^ 4
      ≤ W ^ 27 * W ^ (c * 3) * (ν ^ (a * 4) * W ^ (b * 4)) :=
        mul_le_mul (mul_le_mul h27 h3 (pow_nonneg (inv_pos.mpr hs).le _) (pow_nonneg hW0 _)) h4
          (pow_nonneg hq0.le _) (mul_nonneg (pow_nonneg hW0 _) (pow_nonneg hW0 _))
    _ = ν ^ (a * 4) * W ^ (27 + c * 3 + b * 4) := by rw [pow_add, pow_add]; ring

/-- The scaled loss `(ρ/c)⁻¹ ≤ W^(j+1)` for `c ≤ 2^j`. -/
theorem inv_scale_le_W {W rho c : Real} {j : Nat} (hW : 2 ≤ W) (hr : 0 < rho) (hrW : rho⁻¹ ≤ W)
    (hc0 : 0 < c) (hc : c ≤ 2 ^ j) : (rho / c)⁻¹ ≤ W ^ (j + 1) :=
  inv_scale_le hW hr hrW hc0 hc

/-- The family size `M = n·m` and the dimension-two counts in two bases. -/
theorem two_split_basics {V : Real} (hV : 1 ≤ V) {theta gamma rho : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    ((n * polyTwoFejerPieces gamma theta : Nat) : Real) ≤
        ((n : Real) + 1) ^ 1 * splitW V theta gamma rho ^ ((2 : Nat) ^ 24) ∧
      (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma : Real) ≤
        ((n : Real) + 1) ^ 0 * splitW V theta gamma rho ^ ((2 : Nat) ^ 38) ∧
      (polyPieceSpecCountW (fejerThetaOne theta gamma 1) : Real) ≤
        ((n : Real) + 1) ^ 0 * splitW V theta gamma rho ^ ((2 : Nat) ^ 38) := by
  obtain ⟨hW2, hvW, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hu0 : (0 : Real) ≤ 2 / (gamma * theta) := le_trans (by norm_num) hu2
  have hm := (polyTwoFejerPieces_le_power hg hg1 ht ht1).trans (pow_le_pow_left₀ hu0 hvW _)
  have hqf := (polyPieceFaceCountW_fejer_le_power hg hg1 ht ht1).trans (pow_le_pow_left₀ hu0 hvW _)
  have hqs := (polyPieceSpecCountW_fejer_le_power hg hg1 ht ht1).trans (pow_le_pow_left₀ hu0 hvW _)
  refine ⟨?_, by rw [pow_zero, one_mul]; exact hqf, by rw [pow_zero, one_mul]; exact hqs⟩
  rw [Nat.cast_mul, pow_one]
  have hn : (n : Real) ≤ (n : Real) + 1 := by linarith
  exact mul_le_mul hn hm (Nat.cast_nonneg _) (by positivity)

/-- `M·q + 1` in two bases. -/
theorem affine_le_tb {ν W : Real} {M q : Nat} {a b c : Nat} (hν : 1 ≤ ν) (hW : 2 ≤ W)
    (hM : (M : Real) ≤ ν ^ a * W ^ b) (hq : (q : Real) ≤ ν ^ 0 * W ^ c) :
    ((M * q + 1 : Nat) : Real) ≤ ν ^ a * W ^ (b + c + 1) := by
  have h := tb_mul hν (by linarith) (Nat.cast_nonneg _) hM hq
  rw [Nat.add_zero] at h
  push_cast
  exact tb_add_one hν hW h

/-- The dimension-two remainder count from separate family and face bounds. -/
theorem famTwoQr_le_two_bases {ν W : Real} {M q a b c : Nat} (hν : 1 ≤ ν) (hW : 2 ≤ W)
    (hM : (M : Real) ≤ ν ^ a * W ^ b) (hq : (q : Real) ≤ ν ^ 0 * W ^ c) (t : Real) :
    famTwoQr M q t ≤ ν ^ a * W ^ (4 + (b + c + 1)) := by
  unfold famTwoQr
  apply max_le <;> rw [Nat.cast_mul] <;>
    exact tb_const_mul hW (by norm_num) (Nat.cast_nonneg _) (affine_le_tb hν hW hM hq)

/-- The dimension-two family count is polynomial in its family and face bounds. -/
theorem famTwoCount_le_two_bases {ν W rho : Real} {M q a b c : Nat} (hν : 1 ≤ ν) (hW : 2 ≤ W)
    (hr : 0 < rho) (hrW : rho⁻¹ ≤ W) (hM : (M : Real) ≤ ν ^ a * W ^ b)
    (hq : (q : Real) ≤ ν ^ 0 * W ^ c) :
    max (famPieceGraphBound (famTwoQr M q) (famTwoPb M q) M rho)
      ((3 ^ (1 + 1) * M : Nat) : Real) ≤ ν ^ (11 * a) * W ^ (11 * b + 6 * c + 54) := by
  have hW1 : 1 ≤ W := by linarith only [hW]
  have hQr := famTwoQr_le_two_bases hν hW hM hq (rho / 8)
  have hS : (famPieceSamples (famTwoQr M q) M rho : Real) ≤
      ν ^ (2 * a) * W ^ (2 * b + c + 12) := by
    exact (famPieceSamples_le_two_bases hν hW hr hrW hQr hM).trans_eq (by congr 2 <;> ring)
  set S := famPieceSamples (famTwoQr M q) M rho
  have hSq := tb_mul hν hW1 (Nat.cast_nonneg _) hS hq
  have hprod := tb_mul hν hW1 (by positivity) hM hSq
  have hplus : ((M * (S * q) + 1 : Nat) : Real) ≤ ν ^ (3 * a) * W ^ (3 * b + 2 * c + 13) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_one]
    exact (tb_add_one hν hW hprod).trans_eq (by congr 2 <;> ring)
  have hPb : famTwoPb M q S (rho / 4) ≤ ν ^ (3 * a) * W ^ (3 * b + 2 * c + 15) := by
    unfold famTwoPb
    rw [Nat.cast_mul]
    exact (tb_const_mul (c := (3 : Real)) (j := 2) hW (by norm_num)
      (Nat.cast_nonneg _) hplus).trans_eq (by congr 2 <;> ring)
  have hP0 : 0 ≤ famTwoPb M q S (rho / 4) := by unfold famTwoPb; exact Nat.cast_nonneg _
  have hG := famPieceGraphBound_le_mul_sq (tb_one_le hν hW1) (tb_one_le hν hW1) hM hS hP0 hPb
  refine max_le (hG.trans_eq (by ring)) ?_
  have h9 : ((3 ^ (1 + 1) * M : Nat) : Real) ≤ ν ^ a * W ^ (4 + b) := by
    rw [Nat.cast_mul]
    exact tb_const_mul hW (by norm_num) (Nat.cast_nonneg _) hM
  exact h9.trans (tb_mono hν hW1 (by omega) (by omega))

/-- **The dimension-two count, in two bases**: `≤ ν^11·W^(2^41)`. -/
theorem uniTwoFejerCount_le_split {V : Real} (hV : 1 ≤ V) {gamma theta rho : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    uniTwoFejerCount theta gamma (n * polyTwoFejerPieces gamma theta) rho ≤
      ((n : Real) + 1) ^ 11 * splitW V theta gamma rho ^ ((2 : Nat) ^ 41) := by
  obtain ⟨hW2, -, hrW, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hqf, -⟩ := two_split_basics hV hg hg1 ht ht1 hr hr1 n
  have hν : (1 : Real) ≤ (n : Real) + 1 := by have := Nat.cast_nonneg (α := Real) n; linarith
  have h := famTwoCount_le_two_bases hν hW2 hr hrW hM hqf
  unfold uniTwoFejerCount
  exact h.trans (tb_mono hν (by linarith only [hW2]) (by norm_num) (by norm_num))

/-- The samples of the dimension-two family, in two bases. -/
theorem twoSamples_le_split {ν W rho : Real} {M q : Nat} (hν : 1 ≤ ν) (hW : 2 ≤ W) (hr : 0 < rho)
    (hrW : rho⁻¹ ≤ W) (hM : (M : Real) ≤ ν ^ 1 * W ^ ((2 : Nat) ^ 24))
    (hq : (q : Real) ≤ ν ^ 0 * W ^ ((2 : Nat) ^ 38)) :
    (famPieceSamples (famTwoQr M q) M rho : Real) ≤
      ν ^ (1 + 1) * W ^ (5 + (4 + ((2 : Nat) ^ 24 + (2 : Nat) ^ 38 + 1) + (2 : Nat) ^ 24 + 1) + 1) := by
  have hQr := famTwoQr_le_two_bases hν hW hM hq (rho / 8)
  convert famPieceSamples_le_two_bases hν hW hr hrW hQr hM using 1 <;> ring

/-- **The dimension-two width exponent, in two bases**: its inverse is at most
`ν^29·W^(2^46)`. -/
theorem uniTwoFejerExp_inv_le_split {V : Real} (hV : 1 ≤ V) {K1 p1 : Nat} (hK1 : 0 < K1)
    (hp1 : 0 < p1) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) {gamma theta rho : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho)
    (hr1 : rho ≤ 1) (n : Nat) :
    (uniTwoFejerExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) theta gamma
      (n * polyTwoFejerPieces gamma theta) rho)⁻¹ ≤
      ((n : Real) + 1) ^ 29 * splitW V theta gamma rho ^ ((2 : Nat) ^ 46) := by
  obtain ⟨hW2, hvW, hrW, hVW⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hqf, hqs⟩ := two_split_basics hV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hζ0, hζ1, hζi⟩ := tightZeta_fejer_one_bounds hg hg1 ht ht1
  unfold uniTwoFejerExp
  dsimp only
  set ζ := tightZeta (fejerThetaOne theta gamma 1 / 4)
  set M := n * polyTwoFejerPieces gamma theta with hMdef
  set qs := polyPieceSpecCountW (fejerThetaOne theta gamma 1)
  set qf := polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma
  set W := splitW V theta gamma rho with hWdef
  set ν : Real := (n : Real) + 1 with hνdef
  clear_value ζ M qs qf W
  have hν : 1 ≤ ν := by
    rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith only [this]
  have hν0 : 0 ≤ ν := by linarith only [hν]
  have hW1 : 1 ≤ W := by linarith only [hW2]
  have hW0 : 0 ≤ W := by linarith only [hW2]
  have hu0 : (0 : Real) ≤ 2 / (gamma * theta) := le_trans (by norm_num) hu2
  have hζW : ζ⁻¹ ≤ Real.exp (W ^ ((2 : Nat) ^ 40)) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hu0 hvW _))
  -- `linarith` would evaluate a power with exponent `2 ^ 40` (see `hΛ0`)
  clear hζi
  have hr8 : (rho / 8)⁻¹ ≤ W ^ (3 + 1) := inv_scale_le_W hW2 hr hrW (by norm_num) (by norm_num)
  have hr4 : (rho / 4)⁻¹ ≤ W ^ (2 + 1) := inv_scale_le_W hW2 hr hrW (by norm_num) (by norm_num)
  set B := (2 : Nat) ^ 24 + (2 : Nat) ^ 38 + 1 with hBdef
  have hMqs : ((M * qs + 1 : Nat) : Real) ≤ ν ^ 1 * W ^ B := affine_le_tb hν hW2 hM hqs
  have hMqf : ((M * qf + 1 : Nat) : Real) ≤ ν ^ 1 * W ^ B := affine_le_tb hν hW2 hM hqf
  have hn1 : ((3 * (M * qs + 1) + 1 : Nat) : Real) ≤ ν ^ 1 * W ^ (2 + B + 1) := by
    have h := tb_const_mul (c := (3 : Real)) (j := 2) hW2 (by norm_num)
      (Nat.cast_nonneg _) hMqs
    rw [Nat.cast_succ, Nat.cast_mul]
    push_cast at h ⊢
    exact tb_add_one hν hW2 h
  have hfloor : ⌊famTwoQb M qs (rho / 8)⌋₊ = 3 * (M * qs + 1) := by
    unfold famTwoQb; exact Nat.floor_natCast _
  -- the divisor
  have hpW : (p1 : Real) ≤ ν ^ 0 * W ^ 1 := by rw [pow_zero, one_mul, pow_one]; exact hpV.trans hVW
  have hBq : familyWidthDivisor 1 p1 (3 * (M * qs + 1)) ≤ ν ^ 8 * W ^ (3 + (1 + (2 + B + 1) * 8)) := by
    have hval : familyWidthDivisor 1 p1 (3 * (M * qs + 1)) =
        8 * ((p1 : Real) * ((3 * (M * qs + 1) + 1 : Nat) : Real) ^ 8) := by
      unfold familyWidthDivisor; push_cast; ring
    rw [hval]
    have h8 := tb_pow (Nat.cast_nonneg _) hn1 8
    have h := tb_mul hν hW1 (by positivity) hpW h8
    rw [show (0 + 1 * 8) = 8 by norm_num] at h
    exact tb_const_mul hW2 (by norm_num) (by positivity) h
  have hBq0 : 0 < familyWidthDivisor 1 p1 (3 * (M * qs + 1)) := familyWidthDivisor_pos hp1 _
  -- the two base exponents
  have hEb0 : 0 < famTwoEb M qs (rho / 8) := cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)
  have hEb : (famTwoEb M qs (rho / 8))⁻¹ ≤ ν ^ (1 * 4) * W ^ (27 + (3 + 1) * 3 + B * 4) := by
    unfold famTwoEb
    exact cubicBaseExponent_inv_le_tb hW2 (Nat.succ_pos _) hMqs (by positivity) hr8
  have hEr0 : 0 < famTwoEr M qf (rho / 8) := by
    unfold famTwoEr
    exact div_pos (cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)) (by norm_num)
  have hEr : (famTwoEr M qf (rho / 8))⁻¹ ≤ ν ^ (1 * 4) * W ^ (4 + (27 + (3 + 1) * 3 + B * 4)) := by
    unfold famTwoEr
    rw [inv_div, div_eq_mul_inv]
    have h := cubicBaseExponent_inv_le_tb hW2 (Nat.succ_pos _) hMqf (by positivity) hr8
    exact tb_const_mul hW2 (by norm_num)
      (inv_pos.mpr (cubicBaseExponent_pos (Nat.succ_pos _) (by positivity))).le h
  -- the line exponent
  set L := pieceLineExponent (familyWidthDivisor 1 p1) (famTwoQb M qs) (famTwoEb M qs)
    (famTwoEr M qf) rho with hLdef
  have hLval : L = famTwoEr M qf (rho / 8) * famTwoEb M qs (rho / 8) /
      familyWidthDivisor 1 p1 (3 * (M * qs + 1)) := by
    rw [hLdef]; unfold pieceLineExponent; rw [hfloor]
  have hL0 : 0 < L := by rw [hLval]; positivity
  set LB := 3 + (1 + (2 + B + 1) * 8) + (4 + (27 + (3 + 1) * 3 + B * 4) + (27 + (3 + 1) * 3 + B * 4))
    with hLBdef
  have hLi : L⁻¹ ≤ ν ^ 16 * W ^ LB := by
    rw [hLval, inv_div, div_eq_mul_inv, mul_inv]
    have h := tb_mul hν hW1 (mul_nonneg (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le) hBq
      (tb_mul hν hW1 (inv_pos.mpr hEb0).le hEr hEb)
    exact h.trans (le_of_eq (by rw [hLBdef]))
  -- the slice exponent
  have hSamp := twoSamples_le_split hν hW2 hr hrW hM hqf
  set Sp := famPieceSamples (famTwoQr M qf) M rho
  set SB := 5 + (4 + ((2 : Nat) ^ 24 + (2 : Nat) ^ 38 + 1) + (2 : Nat) ^ 24 + 1) + 1 with hSBdef
  have hSq : ((Sp : Real) * qf) ≤ ν ^ 2 * W ^ (SB + (2 : Nat) ^ 38) := by
    have h := tb_mul hν hW1 (Nat.cast_nonneg _) hSamp hqf
    simpa using h
  have hqS : ((M * (Sp * qf) + 1 : Nat) : Real) ≤ ν ^ 3 * W ^ ((2 : Nat) ^ 24 + (SB + (2 : Nat) ^ 38) + 1) := by
    have h1 := tb_mul hν hW1 (by positivity) hM hSq
    push_cast
    have := tb_add_one hν hW2 h1
    simpa using this
  set S := famPieceSliceExponent (famTwoQr M qf) (famTwoEs M qf) M rho with hSdef
  have hSval : S = cubicBaseExponent (M * (Sp * qf) + 1) (rho / 4) := by rw [hSdef]; rfl
  have hS0 : 0 < S := by rw [hSval]; exact cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)
  have hS1 : S ≤ 1 := by
    rw [hSval]
    exact cubicBaseExponent_le_one (Nat.succ_pos _) (by positivity) (by linarith only [hr1])
  set SS := 27 + (2 + 1) * 3 + ((2 : Nat) ^ 24 + (SB + (2 : Nat) ^ 38) + 1) * 4 with hSSdef
  have hSi : S⁻¹ ≤ ν ^ 12 * W ^ SS := by
    rw [hSval]
    have h := cubicBaseExponent_inv_le_tb hW2 (Nat.succ_pos _) hqS (by positivity) hr4
    exact h
  -- the bound `R`
  set RB := 2 + (LB + SS) with hRBdef
  set R := ν ^ 28 * W ^ RB with hRdef
  have hR1 : 1 ≤ R := tb_one_le hν hW1
  have hLR : L⁻¹ ≤ R := hLi.trans (tb_mono hν hW1 (by norm_num) (by rw [hRBdef]; omega))
  have hLSR : (L * S / 4)⁻¹ ≤ R := by
    have hval : (L * S / 4)⁻¹ = 4 * (L⁻¹ * S⁻¹) := by field_simp
    rw [hval]
    have h := tb_mul hν hW1 (inv_pos.mpr hS0).le hLi hSi
    exact (tb_const_mul (j := 2) hW2 (by norm_num) (by positivity) h).trans
      (le_of_eq (by rw [hRdef, hRBdef]))
  -- the scale `z = ζ / A`
  set z := pieceWidthScale (familyWidthPrefactor K1) (famTwoQb M qs) ζ rho with hzdef
  have hKW : (K1 : Real) ≤ ν ^ 0 * W ^ 1 := by rw [pow_zero, one_mul, pow_one]; exact hKV.trans hVW
  set AB := 2 + (1 + (2 + B + 1)) with hABdef
  have hA : familyWidthPrefactor K1 (3 * (M * qs + 1)) ≤ ν ^ 1 * W ^ AB := by
    unfold familyWidthPrefactor
    rw [Nat.cast_mul]
    have h := tb_mul hν hW1 (Nat.cast_nonneg _) hKW hn1
    rw [Nat.zero_add] at h
    exact tb_const_mul hW2 (by norm_num) (by positivity) h
  have hA1 : 1 ≤ familyWidthPrefactor K1 (3 * (M * qs + 1)) := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K1 * (3 * (M * qs + 1) + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hzval : z = ζ / familyWidthPrefactor K1 (3 * (M * qs + 1)) := by
    rw [hzdef]; unfold pieceWidthScale; rw [hfloor]
  have hz0 : 0 < z := by rw [hzval]; exact div_pos hζ0 (lt_of_lt_of_le zero_lt_one hA1)
  have hz1 : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hζ1.trans hA1
  set A := familyWidthPrefactor K1 (3 * (M * qs + 1)) with hAdef
  set Λ := A + W ^ ((2 : Nat) ^ 40) with hΛdef
  -- no `linarith` may see `W ^ 2 ^ 40`: its parser evaluates powers, and Lean's `Nat.pow`
  -- panics on exponents above `2 ^ 24`
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛdef]; exact add_nonneg (le_trans zero_le_one hA1) (pow_nonneg hW0 _)
  have hzi : z⁻¹ ≤ Real.exp Λ := by
    rw [hzval, inv_div, div_eq_mul_inv, hΛdef, Real.exp_add]
    have hAe : A ≤ Real.exp A := by have := Real.add_one_le_exp A; linarith only [this]
    exact mul_le_mul hAe hζW (inv_pos.mpr hζ0).le (Real.exp_pos _).le
  have hcap := capped_rounded_inv_le_real hL0 hS0 hS1 hz0 hz1 hΛ0 hzi hR1 hLR hLSR
  -- the final bound
  set X := AB + (2 : Nat) ^ 40 + 3 with hXdef
  have h6 : (6 : Real) ≤ ν ^ 1 * W ^ X := by
    have h1 : (6 : Real) ≤ W ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hW2 3; norm_num at this
      linarith only [this]
    exact h1.trans ((tb_mono (a := 0) (b := 3) hν hW1 (by norm_num) (by rw [hXdef]; omega)).trans'
      (by rw [pow_zero, one_mul]))
  have hAX : A ≤ ν ^ 1 * W ^ X := hA.trans (tb_mono hν hW1 le_rfl (by rw [hXdef]; omega))
  have hWX : W ^ ((2 : Nat) ^ 40) ≤ ν ^ 1 * W ^ X := by
    have h := tb_mono (a := 0) (b := (2 : Nat) ^ 40) (a' := 1) (b' := X) hν hW1 (by norm_num)
      (by rw [hXdef] <;> omega)
    rwa [pow_zero, one_mul] at h
  have h6Λ : 6 + Λ ≤ ν ^ 1 * W ^ (X + 2) := by
    rw [hΛdef]
    have h3 : (3 : Real) ≤ W ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hW2 2; norm_num at this
      linarith only [this]
    have hpos : 0 ≤ ν ^ 1 * W ^ X := by positivity
    calc 6 + (A + W ^ ((2 : Nat) ^ 40)) ≤ ν ^ 1 * W ^ X + (ν ^ 1 * W ^ X + ν ^ 1 * W ^ X) :=
          add_le_add h6 (add_le_add hAX hWX)
      _ = 3 * (ν ^ 1 * W ^ X) := by ring
      _ ≤ W ^ 2 * (ν ^ 1 * W ^ X) := mul_le_mul_of_nonneg_right h3 hpos
      _ = ν ^ 1 * W ^ (X + 2) := by rw [pow_add]; ring
  have hfin : 2 * ((6 + Λ) * R) ≤ ν ^ 29 * W ^ (1 + (X + 2 + RB)) := by
    have h := tb_mul hν hW1 (by positivity) h6Λ (le_refl R)
    rw [hRdef] at h ⊢
    have h2 : (2 : Real) ≤ W ^ 1 := by rw [pow_one]; exact hW2
    calc 2 * ((6 + Λ) * (ν ^ 28 * W ^ RB)) ≤ W ^ 1 * (ν ^ (1 + 28) * W ^ (X + 2 + RB)) :=
          mul_le_mul h2 h (by positivity) (by positivity)
      _ = ν ^ 29 * W ^ (1 + (X + 2 + RB)) := by rw [pow_add W 1]; ring
  refine hcap.trans (hfin.trans (tb_mono hν hW1 le_rfl ?_))
  rw [hXdef, hRBdef, hLBdef, hSSdef, hSBdef, hABdef, hBdef]
  norm_num

/-- **Dimension two is a split class at `a₂ = 32`, `D₂ = 2^48`.** -/
theorem splitUniformClass_two_small {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) :
    Nonempty (SplitUniformClass 2 V 32 ((2 : Nat) ^ 48)) := by
  classical
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (polyTwoFejerPieces gamma theta) → PolyPieceTwoFejer N theta gamma,
        Gamma ⊆ polyPieceTwoFejerGraphs P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => PolyPieceTwoData.empty _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    have hthr : polyTwoFejerThreshold theta gamma ≤ N := by
      refine (polyTwoFejerThreshold_le_power hg hg1 ht ht1).trans (le_trans ?_ hN)
      refine (pow_le_pow_left₀ (by linarith only [hu2])
        (le_mul_of_one_le_left (by linarith only [hu2]) hV) _).trans ?_
      exact pow_le_pow_right₀ hVu (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    obtain ⟨J, hJ, P, hP⟩ := section16_poly_piece_decomposition_two_fejer ht ht1 hg hg1 hthr Gamma
      hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have hcov := section16_uniform_cover_two_fejer (familyWidthPrefactor_pos hK1)
      (familyWidthDivisor_pos hp1) hlemma6 ht ht1 hg hg1 Gamma (fun _ => Finset.univ) P
      (fun i => by rw [restrictRelation_univ]; exact hP i)
    have hsub : Finset.univ.biUnion Gamma ⊆
        Finset.univ.biUnion fun i => restrictRelation (Gamma i) Finset.univ := by
      simp only [restrictRelation_univ]; exact le_rfl
    have hν : (1 : Real) ≤ (n : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) n; linarith only [this]
    refine (hcov.subset hsub).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      exact (uniTwoFejerCount_le_split hV hg hg1 ht ht1 hr hr1 n).trans
        (tb_mono hν (by linarith only [hW2]) (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have : (0 : Real) < splitW V theta gamma rho := by linarith only [hW2]
      positivity
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have h := (uniTwoFejerExp_inv_le_split hV (by omega : 0 < K1) hp1 hKV hpV hg hg1 ht ht1 hr hr1
        n).trans (tb_mono hν (by linarith only [hW2]) (by norm_num : 29 ≤ 32)
          (Nat.pow_le_pow_right (by norm_num) (by norm_num) : (2 : Nat) ^ 46 ≤ (2 : Nat) ^ 48))
      have h0 := uniTwoFejerExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
        (familyWidthDivisor_pos (k := 1) hp1)
        (theta := theta) (gamma := gamma) (n * polyTwoFejerPieces gamma theta) hr
      have := inv_anti₀ (inv_pos.mpr h0) h
      rwa [inv_inv] at this

end LeanProofs.GowersSzemeredi
