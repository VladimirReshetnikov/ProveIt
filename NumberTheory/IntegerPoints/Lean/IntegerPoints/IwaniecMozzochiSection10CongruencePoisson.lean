import IntegerPoints.IwaniecMozzochiSection10Eq102Reduction
import IntegerPoints.Lemma9Tools
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Congruence-class Poisson summation for Iwaniec--Mozzochi Section 10

This file discharges the exact one-dimensional Poisson interface left by
`IwaniecMozzochiSection10Eq102Reduction`.  The apparent singularities at
`xi = 0` are harmless because the dyadic factor `chi (xi / H)` is supported
inside `(H, 4 H)`.  To expose that fact to Mathlib's Schwartz-space Poisson
theorem, we replace every singular occurrence of `xi` by an everywhere
positive smooth radius which agrees with `xi` wherever `chi (xi / H)` is
nonzero.  The resulting global function is smooth, compactly supported, and
pointwise equal to the original amplitude.

Applying Poisson summation to `t |-> g(r + c t)`, where
`r = modInv a c * ell`, gives the character `e(k r / c)` with Mathlib's
Fourier convention.  The proof below also performs explicitly the two exact
reindexings hidden in the paper notation:

* the full integer lattice is reindexed as one residue class modulo `c`;
* the nonpositive part of that residue class vanishes, leaving the original
  finitely supported sum over natural `h`.

There is no additional summability or regularity premise and no new trust
boundary in this module.
-/

open scoped BigOperators FourierTransform SchwartzMap ContDiff
open Real Set Filter MeasureTheory

namespace LeanProofs.IntegerPoints

noncomputable section

/-! ## A globally smooth representative of the compactly supported amplitude -/

/-- The Mathlib Fourier kernel at an integral frequency, in the project-local
`e(t) = exp(2 pi i t)` notation. -/
private theorem real_fourier_kernel_eq_e (k : ℤ) (t : ℝ) :
    Complex.exp ((-2 * π * t * (k : ℝ) : ℝ) * Complex.I) =
      e (-((k : ℝ) * t)) := by
  unfold e
  congr 1
  push_cast
  ring

/-- Smoothness of the project-local additive character, with the real-to-
complex coercion made explicit for `ContDiff` elaboration. -/
private theorem section10_e_contDiff_comp {f : ℝ -> ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => e (f x)) := by
  unfold e
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hf))

/-- `L9.hfun` is smooth to every order, not merely to the finite order needed
by its original exponent-pair application. -/
private theorem hfun_contDiff_top : ContDiff ℝ ∞ L9.hfun := by
  unfold L9.hfun
  fun_prop

/-- An everywhere positive smooth replacement for `xi`, equal to `xi` on
the effective dyadic support. -/
private noncomputable def section10SmoothRadius (H xi : ℝ) : ℝ :=
  H * L9.hfun (xi / H)

private theorem section10SmoothRadius_pos {H : ℝ} (hH : 0 < H) (xi : ℝ) :
    0 < section10SmoothRadius H xi := by
  unfold section10SmoothRadius
  exact mul_pos hH (L9.hfun_pos _)

private theorem section10SmoothRadius_contDiff {H : ℝ} (hH : 0 < H) :
    ContDiff ℝ ∞ (section10SmoothRadius H) := by
  have hquot : ContDiff ℝ ∞ (fun xi : ℝ => xi / H) :=
    contDiff_id.div contDiff_const (fun _ => hH.ne')
  unfold section10SmoothRadius
  exact contDiff_const.mul (hfun_contDiff_top.comp hquot)

private theorem section10SmoothRadius_eq_of_chi_ne
    {chi : ℝ -> ℝ} {H xi : ℝ} (hchi : IsDyadicPartition chi)
    (hH : 0 < H) (hchiNe : chi (xi / H) ≠ 0) :
    section10SmoothRadius H xi = xi := by
  have harg : 1 < xi / H := by
    apply lt_of_not_ge
    intro hle
    exact hchiNe (hchi.2.2.2.2 _ hle)
  unfold section10SmoothRadius
  rw [L9.hfun_eq (by linarith : (1 / 2 : ℝ) ≤ xi / H)]
  field_simp [hH.ne']

/-- The globally smooth Section 10 amplitude before taking its Fourier
transform.  It agrees everywhere with the literal paper amplitude, since the
only altered factor is multiplied by `chi (xi / H)`. -/
private noncomputable def section10PoissonAmplitude
    (chi sigma : ℝ -> ℝ) (gamma c H N kappa : ℝ) (ell : ℤ) (xi : ℝ) : ℂ :=
  ((section10SmoothRadius H xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
      sigma ((ell : ℝ) /
        (2 * gamma * c * N * section10SmoothRadius H xi)) : ℝ) : ℂ) *
    e (-((ell : ℝ) ^ 2) /
          (4 * gamma * c ^ 2 * section10SmoothRadius H xi) +
        kappa * section10SmoothRadius H xi / c)

/-- On and off the support, the smooth representative is exactly the literal
amplitude occurring in `section10PrimalHSummand`. -/
private theorem section10PoissonAmplitude_eq_raw
    {chi sigma : ℝ -> ℝ} {gamma c H N kappa xi : ℝ} {ell : ℤ}
    (hchi : IsDyadicPartition chi) (hH : 0 < H) :
    section10PoissonAmplitude chi sigma gamma c H N kappa ell xi =
      ((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
          sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
        e (-((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) +
          kappa * xi / c) := by
  by_cases hchiZero : chi (xi / H) = 0
  · simp [section10PoissonAmplitude, hchiZero]
  · rw [section10PoissonAmplitude,
      section10SmoothRadius_eq_of_chi_ne hchi hH hchiZero]

private theorem section10PoissonAmplitude_contDiff
    {chi sigma : ℝ -> ℝ} {gamma c H N kappa : ℝ} {ell : ℤ}
    (hchi : IsDyadicPartition chi) (hsigma : IsSmoothWeight sigma 4 8)
    (hgamma : 0 < gamma) (hc : 0 < c) (hH : 0 < H) (hN : 0 < N) :
    ContDiff ℝ ∞
      (section10PoissonAmplitude chi sigma gamma c H N kappa ell) := by
  have hchiSmooth : ContDiff ℝ ∞ chi := by
    simpa only using hchi.1
  have hsigmaSmooth : ContDiff ℝ ∞ sigma := by
    simpa only using hsigma.1
  have hrhoSmooth : ContDiff ℝ ∞ (section10SmoothRadius H) :=
    section10SmoothRadius_contDiff hH
  have hrhoNe : forall xi : ℝ, section10SmoothRadius H xi ≠ 0 :=
    fun xi => (section10SmoothRadius_pos hH xi).ne'
  have hxiOverH : ContDiff ℝ ∞ (fun xi : ℝ => xi / H) :=
    contDiff_id.div contDiff_const (fun _ => hH.ne')
  have hchiComp : ContDiff ℝ ∞ (fun xi : ℝ => chi (xi / H)) :=
    hchiSmooth.comp hxiOverH
  have hrhoPow : ContDiff ℝ ∞ (fun xi : ℝ =>
      section10SmoothRadius H xi ^ (-(3 : ℝ) / 2)) :=
    hrhoSmooth.rpow_const_of_ne hrhoNe
  have hdenom : ContDiff ℝ ∞ (fun xi : ℝ =>
      2 * gamma * c * N * section10SmoothRadius H xi) := by
    fun_prop
  have hdenomNe : forall xi : ℝ,
      2 * gamma * c * N * section10SmoothRadius H xi ≠ 0 := by
    intro xi
    exact (mul_pos
      (mul_pos (mul_pos (mul_pos (by norm_num) hgamma) hc) hN)
      (section10SmoothRadius_pos hH xi)).ne'
  have hsigmaArg : ContDiff ℝ ∞ (fun xi : ℝ =>
      (ell : ℝ) /
        (2 * gamma * c * N * section10SmoothRadius H xi)) :=
    contDiff_const.div hdenom hdenomNe
  have hsigmaComp : ContDiff ℝ ∞ (fun xi : ℝ =>
      sigma ((ell : ℝ) /
        (2 * gamma * c * N * section10SmoothRadius H xi))) :=
    hsigmaSmooth.comp hsigmaArg
  have hreal : ContDiff ℝ ∞ (fun xi : ℝ =>
      section10SmoothRadius H xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
        sigma ((ell : ℝ) /
          (2 * gamma * c * N * section10SmoothRadius H xi))) :=
    (hrhoPow.mul hchiComp).mul hsigmaComp
  have hphaseDenom : ContDiff ℝ ∞ (fun xi : ℝ =>
      4 * gamma * c ^ 2 * section10SmoothRadius H xi) :=
    contDiff_const.mul hrhoSmooth
  have hphaseDenomNe : forall xi : ℝ,
      4 * gamma * c ^ 2 * section10SmoothRadius H xi ≠ 0 := by
    intro xi
    exact (mul_pos
      (mul_pos (mul_pos (by norm_num) hgamma) (sq_pos_of_pos hc))
      (section10SmoothRadius_pos hH xi)).ne'
  have hphaseFirst : ContDiff ℝ ∞ (fun xi : ℝ =>
      -((ell : ℝ) ^ 2) /
        (4 * gamma * c ^ 2 * section10SmoothRadius H xi)) :=
    contDiff_const.div hphaseDenom hphaseDenomNe
  have hphaseSecond : ContDiff ℝ ∞ (fun xi : ℝ =>
      kappa * section10SmoothRadius H xi / c) :=
    (contDiff_const.mul hrhoSmooth).div contDiff_const (fun _ => hc.ne')
  have hphase : ContDiff ℝ ∞ (fun xi : ℝ =>
      -((ell : ℝ) ^ 2) /
          (4 * gamma * c ^ 2 * section10SmoothRadius H xi) +
        kappa * section10SmoothRadius H xi / c) := by
    exact hphaseFirst.add hphaseSecond
  have hephase : ContDiff ℝ ∞ (fun xi : ℝ =>
      e (-((ell : ℝ) ^ 2) /
          (4 * gamma * c ^ 2 * section10SmoothRadius H xi) +
        kappa * section10SmoothRadius H xi / c)) := by
    exact section10_e_contDiff_comp hphase
  unfold section10PoissonAmplitude
  exact (Complex.ofRealCLM.contDiff.comp hreal).mul hephase

/-- The support is contained in the original dyadic shell. -/
private theorem section10PoissonAmplitude_support
    {chi sigma : ℝ -> ℝ} {gamma c H N kappa : ℝ} {ell : ℤ}
    (hchi : IsDyadicPartition chi) (hH : 0 < H) :
    Function.support
        (section10PoissonAmplitude chi sigma gamma c H N kappa ell) ⊆
      Icc H (4 * H) := by
  intro xi hxi
  have hchiNe : chi (xi / H) ≠ 0 := by
    intro hz
    apply hxi
    simp [section10PoissonAmplitude, hz]
  have hlowerArg : 1 < xi / H := by
    apply lt_of_not_ge
    intro hle
    exact hchiNe (hchi.2.2.2.2 _ hle)
  have hupperArg : xi / H < 4 := by
    apply lt_of_not_ge
    intro hge
    exact hchiNe (hchi.2.1 _ hge)
  constructor
  · simpa only [one_mul] using ((lt_div_iff₀ hH).1 hlowerArg).le
  · exact ((div_lt_iff₀ hH).1 hupperArg).le

private theorem section10PoissonAmplitude_hasCompactSupport
    {chi sigma : ℝ -> ℝ} {gamma c H N kappa : ℝ} {ell : ℤ}
    (hchi : IsDyadicPartition chi) (hH : 0 < H) :
    HasCompactSupport
      (section10PoissonAmplitude chi sigma gamma c H N kappa ell) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (section10PoissonAmplitude_support hchi hH)

/-! ## Residue-class and natural-number reindexing -/

/-- `n |-> r + c n` parametrizes a nonzero residue class without
repetition. -/
private def residueClassEquivAdd (r c : ℤ) (hc : c ≠ 0) :
    ℤ ≃ {z : ℤ // z ≡ r [ZMOD c]} where
  toFun n := ⟨r + c * n, by
    rw [Int.modEq_iff_dvd]
    use -n
    ring⟩
  invFun z := (z.1 - r) / c
  left_inv n := by
    dsimp
    rw [show r + c * n - r = c * n by ring,
      Int.mul_ediv_cancel_left n hc]
  right_inv z := by
    apply Subtype.ext
    rcases Int.modEq_iff_add_fac.mp z.2.symm with ⟨t, ht⟩
    dsimp
    rw [ht, show r + c * t - r = c * t by ring,
      Int.mul_ediv_cancel_left t hc]

private theorem tsum_residueClass_add (g : ℤ -> ℂ) (r c : ℤ) (hc : c ≠ 0) :
    (∑' n : ℤ, g (r + c * n)) =
      ∑' z : ℤ, if z ≡ r [ZMOD c] then g z else 0 := by
  calc
    (∑' n : ℤ, g (r + c * n)) =
        ∑' z : {z : ℤ // z ≡ r [ZMOD c]}, g z.1 := by
      simpa [residueClassEquivAdd] using
        (residueClassEquivAdd r c hc).tsum_eq (fun z => g z.1)
    _ = ∑' z : ℤ, Set.indicator {z : ℤ | z ≡ r [ZMOD c]} g z :=
      tsum_subtype {z : ℤ | z ≡ r [ZMOD c]} g
    _ = ∑' z : ℤ, if z ≡ r [ZMOD c] then g z else 0 := by
      apply tsum_congr
      intro z
      by_cases hz : z ≡ r [ZMOD c] <;> simp [Set.indicator, hz]

/-- The natural-number primal fiber is the complete affine lattice sum. -/
private theorem section10_primalFiber_eq_lattice
    {chi sigma : ℝ -> ℝ} {gamma H N kappa : ℝ} {a c : Nat}
    (hchi : IsDyadicPartition chi) (hH : 0 < H) (hc : 0 < c)
    (ell : ℤ) :
    section10PrimalFiber chi sigma gamma a c H N kappa ell =
      ∑' n : ℤ,
        section10PoissonAmplitude chi sigma gamma c H N kappa ell
          ((c : ℝ) * (n : ℝ) +
            (((modInv a c : ℤ) * ell : ℤ) : ℝ)) := by
  let r : ℤ := (modInv a c : ℤ) * ell
  let q : ℤ -> ℂ := fun z =>
    if z ≡ r [ZMOD (c : ℤ)] then
      section10PoissonAmplitude chi sigma gamma c H N kappa ell (z : ℝ)
    else 0

  have hqFinite : (Function.support q).Finite := by
    apply (Set.finite_Icc (⌈H⌉ : ℤ) (⌊4 * H⌋ : ℤ)).subset
    intro z hz
    have hamp :
        section10PoissonAmplitude chi sigma gamma c H N kappa ell (z : ℝ) ≠ 0 := by
      intro hampZero
      apply hz
      simp [q, hampZero]
    have hzShell := section10PoissonAmplitude_support
      (sigma := sigma) (gamma := gamma) (c := (c : ℝ)) (N := N)
      (kappa := kappa) (ell := ell) hchi hH hamp
    exact ⟨Int.ceil_le.mpr hzShell.1, Int.le_floor.mpr hzShell.2⟩

  have hqNatFinite :
      (Function.support (fun h : Nat => q (h : ℤ))).Finite := by
    have hpre := hqFinite.preimage Nat.cast_injective.injOn
    exact hpre.subset (fun h hh => hh)

  have hterm (h : Nat) :
      section10PrimalHSummand chi sigma gamma a c H N kappa ell h =
        q (h : ℤ) := by
    by_cases hresidue :
        (h : ℤ) ≡ (modInv a c : ℤ) * ell [ZMOD (c : ℤ)]
    · rw [section10PrimalHSummand, if_pos hresidue]
      simp only [q, r, if_pos hresidue]
      exact (section10PoissonAmplitude_eq_raw hchi hH).symm
    · simp [section10PrimalHSummand, q, r, hresidue]

  have hprimal :
      section10PrimalFiber chi sigma gamma a c H N kappa ell =
        ∑' h : Nat, q (h : ℤ) := by
    unfold section10PrimalFiber
    calc
      (∑ᶠ h : Nat,
          section10PrimalHSummand chi sigma gamma a c H N kappa ell h) =
          ∑ᶠ h : Nat, q (h : ℤ) := finsum_congr hterm
      _ = ∑' h : Nat, q (h : ℤ) :=
        (tsum_eq_finsum hqNatFinite).symm

  have hnegative (n : Nat) : q (-((n : ℤ) + 1)) = 0 := by
    let z : ℤ := -((n : ℤ) + 1)
    change q z = 0
    have hzInt : z ≤ 0 := by
      dsimp only [z]
      omega
    have hnonpos : (z : ℝ) ≤ 0 := by
      exact_mod_cast hzInt
    have harg : (z : ℝ) / H ≤ 1 := by
      have := div_nonpos_of_nonpos_of_nonneg hnonpos hH.le
      linarith
    have hchiZero := hchi.2.2.2.2 _ harg
    change (if z ≡ r [ZMOD (c : ℤ)] then
      section10PoissonAmplitude chi sigma gamma c H N kappa ell (z : ℝ)
      else 0) = 0
    by_cases hresidue : z ≡ r [ZMOD (c : ℤ)]
    · rw [if_pos hresidue]
      simp only [section10PoissonAmplitude, hchiZero, mul_zero,
        zero_mul, Complex.ofReal_zero]
    · rw [if_neg hresidue]

  have hqSummable : Summable q := summable_of_hasFiniteSupport hqFinite
  have hsplit :
      (∑' h : Nat, q (h : ℤ)) = ∑' z : ℤ, q z := by
    simpa only [hnegative, add_zero] using
      (tsum_nat_add_neg_add_one hqSummable)

  have hlattice :
      (∑' n : ℤ,
          section10PoissonAmplitude chi sigma gamma c H N kappa ell
            ((c : ℝ) * (n : ℝ) + (r : ℝ))) =
        ∑' z : ℤ, q z := by
    calc
      (∑' n : ℤ,
          section10PoissonAmplitude chi sigma gamma c H N kappa ell
            ((c : ℝ) * (n : ℝ) + (r : ℝ))) =
          ∑' n : ℤ,
            section10PoissonAmplitude chi sigma gamma c H N kappa ell
              ((r : ℝ) + (c : ℝ) * (n : ℝ)) := by
        apply tsum_congr
        intro n
        congr 1
        ring
      _ = ∑' z : ℤ, q z := by
        simpa [q, r, Int.cast_add, Int.cast_mul] using
          tsum_residueClass_add
            (fun z : ℤ =>
              section10PoissonAmplitude chi sigma gamma c H N kappa ell (z : ℝ))
            r (c : ℤ) (Int.ofNat_ne_zero.mpr hc.ne')

  rw [hprimal, hsplit, ← hlattice]

/-! ## Fourier transform of the affine lattice amplitude -/

private theorem section10_affineAmplitude_contDiff
    {chi sigma : ℝ -> ℝ} {gamma c H N kappa : ℝ} {ell r : ℤ}
    (hchi : IsDyadicPartition chi) (hsigma : IsSmoothWeight sigma 4 8)
    (hgamma : 0 < gamma) (hc : 0 < c) (hH : 0 < H) (hN : 0 < N) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      section10PoissonAmplitude chi sigma gamma c H N kappa ell
        (c * t + (r : ℝ))) := by
  exact (section10PoissonAmplitude_contDiff hchi hsigma hgamma hc hH hN).comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)

private theorem section10_affineAmplitude_hasCompactSupport
    {chi sigma : ℝ -> ℝ} {gamma c H N kappa : ℝ} {ell r : ℤ}
    (hchi : IsDyadicPartition chi) (hc : 0 < c) (hH : 0 < H) :
    HasCompactSupport (fun t : ℝ =>
      section10PoissonAmplitude chi sigma gamma c H N kappa ell
        (c * t + (r : ℝ))) := by
  have hcompact := section10PoissonAmplitude_hasCompactSupport
    (sigma := sigma) (gamma := gamma) (c := c) (N := N)
    (kappa := kappa) (ell := ell) hchi hH
  have hshift := hcompact.comp_homeomorph (Homeomorph.addRight (r : ℝ))
  have hscale := hshift.comp_smul hc.ne'
  simpa only [smul_eq_mul, Function.comp_apply, Homeomorph.coe_addRight] using hscale

/-- The Fourier transform of `t |-> g(r + c t)` is the expected character,
Jacobian, and project-local integral `fourierI`. -/
private theorem section10_fourier_affine
    {chi sigma : ℝ -> ℝ} {gamma c H N kappa : ℝ} {ell r k : ℤ}
    (hchi : IsDyadicPartition chi) (hc : 0 < c) (hH : 0 < H) :
    𝓕 (fun t : ℝ =>
        section10PoissonAmplitude chi sigma gamma c H N kappa ell
          (c * t + (r : ℝ))) k =
      (1 / (c : ℂ)) *
        (e ((k : ℝ) * (r : ℝ) / c) *
          fourierI chi sigma gamma c H N
            ((k : ℝ) - kappa) (ell : ℝ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [real_fourier_kernel_eq_e, smul_eq_mul]

  let g : ℝ -> ℂ :=
    section10PoissonAmplitude chi sigma gamma c H N kappa ell
  let K : ℝ -> ℂ := fun xi =>
    e (-((k : ℝ) * ((xi - (r : ℝ)) / c))) * g xi
  let raw : ℝ -> ℂ := fun xi =>
    ((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
        sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
      e (-((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) -
        xi * ((k : ℝ) - kappa) / c)

  have hrewrite :
      (fun t : ℝ => e (-((k : ℝ) * t)) * g (c * t + (r : ℝ))) =
        fun t : ℝ => K (c * t + (r : ℝ)) := by
    funext t
    dsimp only [K]
    congr 2
    field_simp [hc.ne']
    ring

  have hKpoint (xi : ℝ) :
      K xi = e ((k : ℝ) * (r : ℝ) / c) * raw xi := by
    dsimp only [K]
    rw [show g xi =
        ((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
            sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
          e (-((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) +
            kappa * xi / c) by
      exact section10PoissonAmplitude_eq_raw hchi hH]
    dsimp only [raw]
    calc
      e (-((k : ℝ) * ((xi - (r : ℝ)) / c))) *
          (((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
              sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
            e (-((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) +
              kappa * xi / c)) =
        ((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
            sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
          e (-((k : ℝ) * ((xi - (r : ℝ)) / c) +
            ((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) -
            kappa * xi / c)) := by
              calc
                _ = ((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
                      sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
                    (e (-((k : ℝ) * ((xi - (r : ℝ)) / c))) *
                      e (-((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) +
                        kappa * xi / c)) := by ring
                _ = _ := by
                  rw [← KL.e_add]
                  congr 2
                  ring
      _ = ((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
            sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
          e ((k : ℝ) * (r : ℝ) / c +
            (-((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) -
              xi * ((k : ℝ) - kappa) / c)) := by
              congr 2
              ring
      _ = e ((k : ℝ) * (r : ℝ) / c) *
          (((xi ^ (-(3 : ℝ) / 2) * chi (xi / H) *
              sigma ((ell : ℝ) / (2 * gamma * c * N * xi)) : ℝ) : ℂ) *
            e (-((ell : ℝ) ^ 2) / (4 * gamma * c ^ 2 * xi) -
              xi * ((k : ℝ) - kappa) / c)) := by
              rw [KL.e_add]
              ring

  have hrawSet :
      (∫ xi : ℝ in Ioi 0, raw xi) = ∫ xi : ℝ, raw xi := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards with xi
    intro hxi
    have hxiNonpos : xi ≤ 0 := le_of_not_gt hxi
    have harg : xi / H ≤ 1 := by
      have := div_nonpos_of_nonpos_of_nonneg hxiNonpos hH.le
      linarith
    have hchiZero := hchi.2.2.2.2 _ harg
    simp [raw, hchiZero]

  have hrawIntegral : (∫ xi : ℝ, raw xi) =
      fourierI chi sigma gamma c H N ((k : ℝ) - kappa) (ell : ℝ) := by
    simpa only [fourierI] using hrawSet.symm

  have hKIntegral : (∫ xi : ℝ, K xi) =
      e ((k : ℝ) * (r : ℝ) / c) *
        fourierI chi sigma gamma c H N
          ((k : ℝ) - kappa) (ell : ℝ) := by
    calc
      (∫ xi : ℝ, K xi) =
          ∫ xi : ℝ, e ((k : ℝ) * (r : ℝ) / c) * raw xi := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hKpoint
      _ = e ((k : ℝ) * (r : ℝ) / c) * (∫ xi : ℝ, raw xi) := by
        rw [MeasureTheory.integral_const_mul]
      _ = _ := by rw [hrawIntegral]

  rw [hrewrite]
  calc
    (∫ t : ℝ, K (c * t + (r : ℝ))) =
        ∫ t : ℝ, (fun y => K (y + (r : ℝ))) (c * t) := rfl
    _ = abs c⁻¹ • (∫ y : ℝ, K (y + (r : ℝ))) :=
      MeasureTheory.Measure.integral_comp_mul_left
        (fun y : ℝ => K (y + (r : ℝ))) c
    _ = abs c⁻¹ • (∫ y : ℝ, K y) := by
      rw [integral_add_right_eq_self]
    _ = (1 / (c : ℂ)) *
        (e ((k : ℝ) * (r : ℝ) / c) *
          fourierI chi sigma gamma c H N
            ((k : ℝ) - kappa) (ell : ℝ)) := by
      rw [hKIntegral, abs_of_pos (inv_pos.mpr hc)]
      simp only [Complex.real_smul, Complex.ofReal_inv, one_div]

/-! ## The unconditional Section 10 endpoint -/

/-- The exact congruence-class Poisson identity required by equation (10.2)
holds uniformly on the full Section 10 domain. -/
theorem iwaniecMozzochi_section10_congruencePoisson_holds :
    iwaniecMozzochi_section10_congruencePoisson := by
  intro chi sigma x H M a c hchi hsigma hmain hfarey ell
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hcNat : 0 < c := zero_lt_one.trans_le hfarey.1
  have hc : (0 : ℝ) < c := by exact_mod_cast hcNat
  have hgamma : 0 < gammaIM x a c := section10_gammaIM_pos hmain hfarey
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  let r : ℤ := (modInv a c : ℤ) * ell
  let F : ℝ -> ℂ := fun t =>
    section10PoissonAmplitude chi sigma (gammaIM x a c) c H
      (shiftLength x M) (kappaIM x a c) ell (c * t + (r : ℝ))
  have hFsmooth : ContDiff ℝ ∞ F := by
    simpa only [F] using section10_affineAmplitude_contDiff
      (ell := ell) (r := r) hchi hsigma hgamma hc hH hN
  have hFcompact : HasCompactSupport F := by
    simpa only [F] using section10_affineAmplitude_hasCompactSupport
      (sigma := sigma) (gamma := gammaIM x a c) (N := shiftLength x M)
      (kappa := kappaIM x a c) (ell := ell) (r := r) hchi hc hH
  let phi : 𝓢(ℝ, ℂ) := hFcompact.toSchwartzMap hFsmooth
  have hphiFun : (phi : ℝ -> ℂ) = F := rfl

  have hpoisson := SchwartzMap.tsum_eq_tsum_fourier phi 0
  have hpoissonSchwartz :
      (∑' n : ℤ, (phi : ℝ -> ℂ) n) =
        ∑' k : ℤ, (𝓕 phi : 𝓢(ℝ, ℂ)) (k : ℝ) := by
    simpa only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero,
      mul_one] using hpoisson
  have hpoissonPhi :
      (∑' n : ℤ, (phi : ℝ -> ℂ) n) =
        ∑' k : ℤ, 𝓕 (phi : ℝ -> ℂ) k := by
    calc
      (∑' n : ℤ, (phi : ℝ -> ℂ) n) =
          ∑' k : ℤ, (𝓕 phi : 𝓢(ℝ, ℂ)) (k : ℝ) :=
        hpoissonSchwartz
      _ = ∑' k : ℤ, 𝓕 (phi : ℝ -> ℂ) k := by
        apply tsum_congr
        intro k
        exact congrFun (SchwartzMap.fourier_coe phi) (k : ℝ)
  have hpoissonZero :
      (∑' n : ℤ, F n) = ∑' k : ℤ, 𝓕 F k := by
    simpa only [hphiFun] using hpoissonPhi

  have hprimal :
      section10PrimalFiber chi sigma (gammaIM x a c) a c H
          (shiftLength x M) (kappaIM x a c) ell = ∑' n : ℤ, F n := by
    simpa only [F, r] using section10_primalFiber_eq_lattice
      (sigma := sigma) (gamma := gammaIM x a c) (N := shiftLength x M)
      (kappa := kappaIM x a c) hchi hH hcNat ell

  calc
    section10PrimalFiber chi sigma (gammaIM x a c) a c H
        (shiftLength x M) (kappaIM x a c) ell =
        ∑' n : ℤ, F n := hprimal
    _ = ∑' k : ℤ, 𝓕 F k := hpoissonZero
    _ = ∑' k : ℤ,
        (1 / (c : ℂ)) *
          (e ((k : ℝ) * (r : ℝ) / c) *
            fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
              ((k : ℝ) - kappaIM x a c) (ell : ℝ)) := by
      apply tsum_congr
      intro k
      simpa only [F, Complex.ofReal_natCast] using
        section10_fourier_affine
          (ell := ell) (r := r) (k := k) hchi hc hH
    _ = (1 / (c : ℂ)) *
        ∑' k : ℤ,
          e ((modInv a c : ℝ) * (k : ℝ) * (ell : ℝ) / c) *
            fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
              (k - kappaIM x a c) ell := by
      rw [tsum_mul_left]
      apply congrArg ((1 / (c : ℂ)) * .)
      apply tsum_congr
      intro k
      congr 2
      dsimp only [r]
      push_cast
      ring

end

end LeanProofs.IntegerPoints
