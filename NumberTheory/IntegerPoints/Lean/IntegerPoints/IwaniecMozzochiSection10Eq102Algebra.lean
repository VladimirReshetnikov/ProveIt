import IntegerPoints.IwaniecMozzochiEq84Conclusion
import IntegerPoints.IwaniecMozzochiSection9Algebra
import IntegerPoints.IwaniecMozzochiSection10Scales

/-!
# Algebra behind Iwaniec--Mozzochi (10.2)

This file isolates the exact, non-asymptotic algebra used between the
Section 9 modular transformation and equation (10.2).  In particular it
records the following points which are easy to obscure in the paper's
notation.

* The Section 9 displacement is
  `eta = 2 * v * beta * c`.  The Farey geometry gives `0 <= v < 1`, hence
  `|eta| <= 2 * beta * c`, exactly (9.5) with constant two.  It does **not**
  by itself put `eta` in the normalized half-open interval
  `(-1/2, 1/2]`; that extra restriction is therefore not used below.
* Coprimality changes `ell == a*h (mod c)` into
  `h == inv(a)*ell (mod c)`, including the modulus-one edge case.
* The integer part `b` and fractional part `kappa` of `c*x/m` give the
  phase factor printed in (10.2), with no discarded integral phase.
* The principal complex powers in the two Fresnel normalizations really
  agree.  The proof keeps the branch check explicit.

The remaining passage to (10.2) is analytic: the Section 9 remainder must
be proved for the unreduced displacement above and summed over `h`, and
Poisson summation must be justified for the smooth congruence-class
amplitude.  Those obligations are stated separately in the downstream
reduction module.
-/

open scoped BigOperators
open Real

namespace LeanProofs.IntegerPoints

open IMReductionEq75

noncomputable section

/-- The displacement used when (9.6) is applied to the Section 8 parameter
`alpha = -a*h/c - 2*v*beta`. -/
def section10Eta (x : ℝ) (a c h : ℕ) : ℝ :=
  2 * fareyFrac x a c * betaIM x a c h * c

/-- Equation (10.1), before any manipulation of real or complex powers. -/
theorem section10_betaIM_eq_gammaIM_mul (x : ℝ) (a c h : ℕ) :
    betaIM x a c h = gammaIM x a c * h := by
  rfl

/-- The scale `gamma` is positive throughout the declared main/Farey range. -/
theorem section10_gammaIM_pos
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    0 < gammaIM x a c := by
  rcases hmain with ⟨hx, hxM, _hMx, _hH, _hHupper, _hHlower,
    _hHlowerTwo, _hMlower⟩
  rcases hfarey with ⟨hc, _hcH, _hac, haLower, _haUpper⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hMPos : 0 < M := (Real.rpow_pos_of_pos hxPos theta0).trans hxM
  have hcPos : (0 : ℝ) < c := by
    exact_mod_cast (zero_lt_one.trans_le hc)
  have haModelPos : 0 < (c : ℝ) * x / (2 * M) ^ 2 := by positivity
  have haPos : (0 : ℝ) < a := haModelPos.trans_le haLower
  unfold gammaIM
  positivity

/-- With the unreduced displacement `section10Eta`, the Section 8 linear
coefficient has exactly the rational form required in (9.2). -/
theorem section10_alphaIM_eq_unreducedEta
    {x : ℝ} {a c h : ℕ} (hc : (c : ℝ) ≠ 0) :
    alphaIM x a c h =
      -((((a : ℝ) * h) + section10Eta x a c h) / c) := by
  unfold alphaIM section10Eta
  field_simp [hc]
  <;> ring

/-- The exact content of the paper's condition (9.5) in the Section 10
specialization.  Notice that no half-unit normalization is asserted. -/
theorem section10_eta_nonneg_and_abs_le
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    0 ≤ section10Eta x a c h ∧
      |section10Eta x a c h| ≤ 2 * betaIM x a c h * c := by
  rcases fareyPoint_geometry hmain hfarey with
    ⟨_hm, hvNonneg, hvLt, _hsum, _hcoefficient, _hmLower, _hmUpper⟩
  have hbetaPos := betaIM_pos_of_mem_intRange hmain hfarey hh
  have hcNonneg : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hetaNonneg : 0 ≤ section10Eta x a c h := by
    unfold section10Eta
    positivity
  refine ⟨hetaNonneg, ?_⟩
  rw [abs_of_nonneg hetaNonneg]
  unfold section10Eta
  calc
    2 * fareyFrac x a c * betaIM x a c h * (c : ℝ) ≤
        2 * 1 * betaIM x a c h * (c : ℝ) := by
      gcongr
    _ = 2 * betaIM x a c h * (c : ℝ) := by ring

/-- If a separate argument does make `beta*c <= 1/4`, then the unreduced
displacement lies in the normalized interval used by the current catalogue
statement of (9.6)/(9.7).  This deliberately exposes the missing premise. -/
theorem section10_eta_mem_normalized_of_beta_mul_c_le
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hsmall : betaIM x a c h * c ≤ 1 / 4) :
    -1 / 2 < section10Eta x a c h ∧
      section10Eta x a c h ≤ 1 / 2 := by
  have heta := section10_eta_nonneg_and_abs_le hmain hfarey hh
  constructor
  · linarith
  · have habs := heta.2
    rw [abs_of_nonneg heta.1] at habs
    linarith

private theorem section10_rpow_lower_identity {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) =
      x ^ (-(3 : ℝ) / 11) := by
  calc
    x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) =
        x ^ ((1 : ℝ) / 22 + -(7 : ℝ) / 22) :=
      (Real.rpow_add hx _ _).symm
    _ = x ^ (-(3 : ℝ) / 11) := by norm_num

/-- The selected shift is at least the Fourier-shell scale throughout the
main range.  This supplies the missing comparison `c <= N` when (8.2) is
converted into the three scale inequalities of (9.4). -/
theorem section10_H_le_shiftLength
    {x H M : ℝ} (hmain : InMainRange x H M) :
    H ≤ shiftLength x M := by
  rcases hmain with ⟨hx, _hxM, _hMx, hH, hHupper, _hHlower,
    _hHlowerTwo, _hMlower⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hNlower :
      x ^ ((1 : ℝ) / 22) * H ≤ shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    calc
      x ^ ((1 : ℝ) / 22) * H ≤
          x ^ ((1 : ℝ) / 22) * (M * x ^ (-(7 : ℝ) / 22)) :=
        mul_le_mul_of_nonneg_left hHupper'
          (Real.rpow_nonneg hxPos.le _)
      _ = M *
          (x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22)) := by ring
      _ = M * x ^ (-(3 : ℝ) / 11) := by
        rw [section10_rpow_lower_identity hxPos]
  have hxpow : 1 ≤ x ^ ((1 : ℝ) / 22) :=
    Real.one_le_rpow hx (by norm_num)
  calc
    H = 1 * H := by ring
    _ ≤ x ^ ((1 : ℝ) / 22) * H :=
      mul_le_mul_of_nonneg_right hxpow hHPos.le
    _ ≤ shiftLength x M := hNlower

/-- Rescaling a Section 10 weight gives the support window required in the
generic Section 9 statement with `c0 = 1/8`.  The actual support
`[4*N,8*N]` is stronger at the lower endpoint. -/
theorem section10_rescaledWeight_support
    {sigma : ℝ → ℝ} {N t : ℝ}
    (hsigma : IsSmoothWeight sigma 4 8) (hN : 0 < N)
    (ht : sigma (t / N) ≠ 0) :
    (1 / 8 : ℝ) * N ≤ t ∧ t ≤ N / (1 / 8 : ℝ) := by
  have hsupp := hsigma.2.2 (t / N) ht
  have hlower : 4 * N ≤ t := (le_div_iff₀ hN).1 hsupp.1
  have hupper : t ≤ 8 * N := (div_le_iff₀ hN).1 hsupp.2
  constructor
  · nlinarith [hN]
  · convert hupper using 1 <;> ring

/-- The rescaled weight also has the `C^3` regularity required by Section 9.
No normalization of its first three derivatives is claimed: the specialized
interface instead lets its constant depend on the fixed weight `sigma`. -/
theorem section10_rescaledWeight_contDiff_three
    {sigma : ℝ → ℝ} {N : ℝ}
    (hsigma : IsSmoothWeight sigma 4 8) :
    ContDiff ℝ 3 (fun t : ℝ => sigma (t / N)) := by
  exact (hsigma.1.comp (contDiff_id.div_const N)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)

/-- Apart from the normalized half-unit restriction on `eta`, every scale
condition in the public (9.6)/(9.7) interface follows from (8.2).  In
particular one may use the same positive lower constant for `beta*N^2` and
`beta*c*N`, an upper constant for `beta*N`, and the exact displacement
constant two. -/
theorem section10_eq96_scale_data :
    ∀ mu1 : ℝ, 0 < mu1 →
      ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
        ∀ (x H M : ℝ) (a c h : ℕ),
          InMainRange x H M → InFareySet x H M a c →
          mu1 * Gscale x H M < c → h ∈ intRange H (4 * H) →
          c1 ≤ betaIM x a c h * shiftLength x M ^ 2 ∧
          betaIM x a c h * shiftLength x M ≤ c2 ∧
          c3 ≤ betaIM x a c h * c * shiftLength x M ∧
          |section10Eta x a c h| ≤ 2 * betaIM x a c h * c := by
  intro mu1 hmu1
  rcases iwaniecMozzochi_eq82_holds mu1 hmu1 with
    ⟨cUpper, cLower, hcUpper, hcLower, h82⟩
  refine ⟨cLower, cUpper, cLower, hcLower, hcUpper, hcLower, ?_⟩
  intro x H M a c h hmain hfarey hshort hh
  have h82' := h82 x H M a c h hmain hfarey hshort hh
  have hbeta : 0 < betaIM x a c h :=
    betaIM_pos_of_mem_intRange hmain hfarey hh
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hcN : (c : ℝ) ≤ shiftLength x M :=
    hfarey.2.1.trans (section10_H_le_shiftLength hmain)
  have hbetaN : 0 ≤ betaIM x a c h * shiftLength x M :=
    mul_nonneg hbeta.le hN.le
  have hNtwo :
      betaIM x a c h * (c : ℝ) * shiftLength x M ≤
        betaIM x a c h * shiftLength x M ^ 2 := by
    calc
      betaIM x a c h * (c : ℝ) * shiftLength x M =
          (betaIM x a c h * shiftLength x M) * (c : ℝ) := by ring
      _ ≤ (betaIM x a c h * shiftLength x M) * shiftLength x M :=
        mul_le_mul_of_nonneg_left hcN hbetaN
      _ = betaIM x a c h * shiftLength x M ^ 2 := by ring
  exact ⟨h82'.2.trans hNtwo, h82'.1, h82'.2,
    (section10_eta_nonneg_and_abs_le hmain hfarey hh).2⟩

/-- The fractional part `kappa` has its exact closed/open range, with no
main-range assumptions. -/
theorem section10_kappaIM_mem (x : ℝ) (a c : ℕ) :
    0 ≤ kappaIM x a c ∧ kappaIM x a c < 1 := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- In the Farey range, the natural floor used for `b` and the integer floor
used by `Int.fract` are the same real number.  Thus `b + kappa = c*x/m`
even at an integral endpoint. -/
theorem section10_bIM_add_kappaIM
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    (bIM x a c : ℝ) + kappaIM x a c =
      (c : ℝ) * x / fareyPoint x a c := by
  have hxPos : 0 < x := zero_lt_one.trans_le hmain.1
  have hcPos : (0 : ℝ) < c := by
    exact_mod_cast (zero_lt_one.trans_le hfarey.1)
  have hmPosNat := (fareyPoint_geometry hmain hfarey).1
  have hmPos : (0 : ℝ) < fareyPoint x a c := by exact_mod_cast hmPosNat
  let t : ℝ := (c : ℝ) * x / fareyPoint x a c
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hcast : ((⌊t⌋₊ : ℕ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.natCast_floor_eq_floor ht
  change ((⌊t⌋₊ : ℕ) : ℝ) + Int.fract t = t
  rw [hcast]
  exact Int.floor_add_fract t

/-- The first equality in the paper's display immediately after the
definition of `b` and `kappa`. -/
theorem section10_e_x_over_fareyPoint
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    e (x * (h : ℝ) / fareyPoint x a c) =
      e ((h : ℝ) * ((bIM x a c : ℝ) + kappaIM x a c) / c) := by
  rw [section10_bIM_add_kappaIM hmain hfarey]
  have hc : (c : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (zero_lt_one.trans_le hfarey.1))
  have hm : (fareyPoint x a c : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (fareyPoint_geometry hmain hfarey).1)
  congr 1
  field_simp [hc, hm]
  <;> ring

/-- The standard representative `modInv` is an inverse modulo `c`.  This
formulation includes `c = 1`, where the representative is zero. -/
theorem section10_modInv_modEq {a c : ℕ} (hac : Nat.Coprime a c) :
    a * modInv a c ≡ 1 [MOD c] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa [modInv, Nat.cast_mul] using ZMod.mul_val_inv hac

/-- Multiplication by the inverse residue identifies the two congruence
classes used before and after (10.1).  The statement is over integers because
the dual variable `ell` may be negative. -/
theorem section10_residueClass_iff
    {a c h : ℕ} (hac : Nat.Coprime a c) (ell : ℤ) :
    ell ≡ (a : ℤ) * (h : ℤ) [ZMOD (c : ℤ)] ↔
      (h : ℤ) ≡ (modInv a c : ℤ) * ell [ZMOD (c : ℤ)] := by
  have haInv : (a : ZMod c) * (modInv a c : ZMod c) = 1 := by
    simpa [modInv, Nat.cast_mul] using ZMod.mul_val_inv hac
  have hInvA : (modInv a c : ZMod c) * (a : ZMod c) = 1 := by
    simpa [mul_comm] using haInv
  constructor
  · intro hell
    have hellZ : (ell : ZMod c) = (a : ZMod c) * (h : ZMod c) := by
      have hz := (ZMod.intCast_eq_intCast_iff ell
        ((a : ℤ) * (h : ℤ)) c).mpr hell
      simpa only [Int.cast_mul, Int.cast_natCast] using hz
    apply (ZMod.intCast_eq_intCast_iff (h : ℤ)
      ((modInv a c : ℤ) * ell) c).mp
    simpa only [Int.cast_mul, Int.cast_natCast] using calc
      (h : ZMod c) = 1 * (h : ZMod c) := by simp
      _ = ((modInv a c : ZMod c) * (a : ZMod c)) * (h : ZMod c) := by
        rw [hInvA]
      _ = (modInv a c : ZMod c) * ((a : ZMod c) * (h : ZMod c)) := by
        ring
      _ = (modInv a c : ZMod c) * (ell : ZMod c) := by rw [← hellZ]
  · intro hh
    have hhZ : (h : ZMod c) = (modInv a c : ZMod c) * (ell : ZMod c) := by
      have hz := (ZMod.intCast_eq_intCast_iff (h : ℤ)
        ((modInv a c : ℤ) * ell) c).mpr hh
      simpa only [Int.cast_mul, Int.cast_natCast] using hz
    apply (ZMod.intCast_eq_intCast_iff ell
      ((a : ℤ) * (h : ℤ)) c).mp
    simpa only [Int.cast_mul, Int.cast_natCast] using calc
      (ell : ZMod c) = 1 * (ell : ZMod c) := by simp
      _ = ((a : ZMod c) * (modInv a c : ZMod c)) * (ell : ZMod c) := by
        rw [haInv]
      _ = (a : ZMod c) * ((modInv a c : ZMod c) * (ell : ZMod c)) := by
        ring
      _ = (a : ZMod c) * (h : ZMod c) := by rw [← hhZ]

/-- Congruent indices give the same `b`-phase.  This is the precise
periodicity step hidden in the second equality after the definition of
`b,kappa`. -/
theorem section10_e_integerPart_of_residue
    {c b r h : ℕ} {ell : ℤ} (hc : 0 < c)
    (hh : (h : ℤ) ≡ (r : ℤ) * ell [ZMOD (c : ℤ)]) :
    e ((h : ℝ) * b / c) = e ((r : ℝ) * b * (ell : ℝ) / c) := by
  rcases (Int.modEq_iff_dvd.mp hh) with ⟨q, hq⟩
  have hqReal := congrArg (fun z : ℤ => (z : ℝ)) hq
  push_cast at hqReal
  have hcReal : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hphase :
      (h : ℝ) * b / c =
        (r : ℝ) * b * (ell : ℝ) / c - ((b : ℤ) * q : ℤ) := by
    field_simp [hcReal]
    push_cast
    linear_combination -(b : ℝ) * hqReal
  rw [hphase, KL.e_sub_int]

/-- The complete pre-Poisson phase conversion in the display preceding
(10.2). -/
theorem section10_primal_phase
    {x H M : ℝ} {a c h : ℕ} {ell : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hell : ell ≡ (a : ℤ) * (h : ℤ) [ZMOD (c : ℤ)]) :
    e (-fareyFrac x a c * (ell : ℝ) / c) *
        e (x * (h : ℝ) / fareyPoint x a c) =
      e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
          (ell : ℝ) / c) *
        e (kappaIM x a c * (h : ℝ) / c) := by
  have hcNat : 0 < c := zero_lt_one.trans_le hfarey.1
  have hhResidue := (section10_residueClass_iff hfarey.2.2.1 ell).mp hell
  rw [section10_e_x_over_fareyPoint hmain hfarey]
  have hsplit :
      (h : ℝ) * ((bIM x a c : ℝ) + kappaIM x a c) / c =
        (h : ℝ) * bIM x a c / c + kappaIM x a c * (h : ℝ) / c := by
    ring
  rw [hsplit, KL.e_add,
    section10_e_integerPart_of_residue hcNat hhResidue]
  calc
    e (-fareyFrac x a c * (ell : ℝ) / c) *
          (e ((modInv a c : ℝ) * bIM x a c * (ell : ℝ) / c) *
            e (kappaIM x a c * (h : ℝ) / c)) =
        (e (-fareyFrac x a c * (ell : ℝ) / c) *
          e ((modInv a c : ℝ) * bIM x a c * (ell : ℝ) / c)) *
            e (kappaIM x a c * (h : ℝ) / c) := by ring
    _ = e (-fareyFrac x a c * (ell : ℝ) / c +
          (modInv a c : ℝ) * bIM x a c * (ell : ℝ) / c) *
            e (kappaIM x a c * (h : ℝ) / c) := by rw [← KL.e_add]
    _ = e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
          (ell : ℝ) / c) *
            e (kappaIM x a c * (h : ℝ) / c) := by
      congr 2
      ring

/-- Evaluation of the Section 9 amplitude at its stationary point after
substituting `beta = gamma*h`. -/
theorem section10_sigma_stationaryArgument
    {sigma : ℝ → ℝ} {gamma N : ℝ} {c h : ℕ} {ell : ℤ}
    (hgamma : gamma ≠ 0) (hN : N ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0) :
    (fun t : ℝ => sigma (t / N))
        ((ell : ℝ) / (2 * (gamma * h) * c)) =
      sigma ((ell : ℝ) / (2 * gamma * c * h * N)) := by
  congr 1
  field_simp [hgamma, hN, Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr hh]
  <;> ring

/-- The stationary phase in (9.6) becomes the two phases displayed just
before (10.2). -/
theorem section10_stationaryPhase
    {gamma : ℝ} {c h : ℕ} {v : ℝ} {ell : ℤ}
    (hgamma : gamma ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0) :
    (-(ell : ℝ) ^ 2 - 2 * (2 * v * (gamma * h) * c) * ell) /
        (4 * (gamma * h) * c ^ 2) =
      -(ell : ℝ) ^ 2 / (4 * gamma * c ^ 2 * h) -
        v * ell / c := by
  field_simp [hgamma, Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr hh]
  <;> ring

/-- The principal branch in the prefactor of (10.2) has the same explicit
Fresnel value as the Section 9 square root. -/
theorem section10_dualFresnelConstant_eq
    {gamma : ℝ} (hgamma : 0 < gamma) :
    (-2 * Complex.I * (gamma : ℂ)) ^ (-(1 : ℂ) / 2) =
      e (1 / 8) / ((Real.sqrt (2 * gamma) : ℝ) : ℂ) := by
  let z : ℂ := -2 * Complex.I * (gamma : ℂ)
  have hzArg : z.arg ≠ π := by
    intro hz
    have him := (Complex.arg_eq_pi_iff.mp hz).2
    dsimp [z] at him
    norm_num at him
    linarith
  have hzInv : z⁻¹ = Complex.I / (2 * gamma) := by
    dsimp [z]
    have hgammaC : (gamma : ℂ) ≠ 0 := by exact_mod_cast hgamma.ne'
    field_simp [hgammaC, Complex.I_ne_zero, Complex.I_mul_I]
    rw [Complex.I_sq]
  change z ^ (-(1 : ℂ) / 2) = _
  calc
    z ^ (-(1 : ℂ) / 2) = (z ^ ((1 : ℂ) / 2))⁻¹ := by
      rw [show -(1 : ℂ) / 2 = -((1 : ℂ) / 2) by ring,
        Complex.cpow_neg]
    _ = z⁻¹ ^ ((1 : ℂ) / 2) :=
      (Complex.inv_cpow z ((1 : ℂ) / 2) hzArg).symm
    _ = (Complex.I / (2 * gamma)) ^ ((1 : ℂ) / 2) := by rw [hzInv]
    _ = e (1 / 8) / ((Real.sqrt (2 * gamma) : ℝ) : ℂ) :=
      section9_fresnelConstant_eq hgamma

private theorem section10_rpow_neg_three_halves
    {t : ℝ} (ht : 0 < t) :
    t ^ (-(3 : ℝ) / 2) = (t * Real.sqrt t)⁻¹ := by
  calc
    t ^ (-(3 : ℝ) / 2) = t ^ (-(1 + 1 / 2 : ℝ)) := by
      congr 1
      ring
    _ = (t ^ (1 + 1 / 2 : ℝ))⁻¹ := Real.rpow_neg ht.le _
    _ = (t ^ (1 : ℝ) * t ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_add ht]
    _ = (t * Real.sqrt t)⁻¹ := by
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Exact prefactor conversion from the `h`-th theta transform to the common
factor in (10.2).  This is where the power `h^(-3/2)` is created. -/
theorem section10_fresnelPrefactor
    {gamma h : ℝ} (hgamma : 0 < gamma) (hh : 0 < h) :
    (1 / (((π * h : ℝ)) : ℂ)) *
        (Complex.I / (2 * (gamma * h))) ^ ((1 : ℂ) / 2) =
      ((-2 * Complex.I * (gamma : ℂ)) ^ (-(1 : ℂ) / 2) /
          (π : ℂ)) *
        ((h ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  rw [section9_fresnelConstant_eq (mul_pos hgamma hh),
    section10_dualFresnelConstant_eq hgamma]
  have hsqrt :
      Real.sqrt (2 * (gamma * h)) =
        Real.sqrt (2 * gamma) * Real.sqrt h := by
    rw [show 2 * (gamma * h) = (2 * gamma) * h by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * gamma)]
  rw [hsqrt, section10_rpow_neg_three_halves hh]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hgammaSqrt : ((Real.sqrt (2 * gamma) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by positivity : 0 < 2 * gamma)
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hhSqrt : ((Real.sqrt h : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 hh
  push_cast
  field_simp [hpi, hgammaSqrt, hhC, hhSqrt]
  <;> ring

/-- The two exterior characters combine to the character printed in (10.2). -/
theorem section10_dualPhase
    (r b v c : ℝ) (k ell : ℤ) :
    e ((r * b - v) * (ell : ℝ) / c) *
        e (r * (k : ℝ) * (ell : ℝ) / c) =
      e ((r * ((k : ℝ) + b) - v) * (ell : ℝ) / c) := by
  rw [← KL.e_add]
  congr 1
  ring

/-- The oscillation `e(kappa*h/c)` shifts the Poisson frequency from `k`
to `k-kappa`, with the sign convention used by `fourierI`. -/
theorem section10_fourierKernel
    (gamma c kappa xi : ℝ) (k ell : ℤ) :
    e (-(ell : ℝ) ^ 2 / (4 * gamma * c ^ 2 * xi) +
          kappa * xi / c) *
        e (-xi * (k : ℝ) / c) =
      e (-(ell : ℝ) ^ 2 / (4 * gamma * c ^ 2 * xi) -
          xi * ((k : ℝ) - kappa) / c) := by
  rw [← KL.e_add]
  congr 1
  ring

end

end LeanProofs.IntegerPoints
