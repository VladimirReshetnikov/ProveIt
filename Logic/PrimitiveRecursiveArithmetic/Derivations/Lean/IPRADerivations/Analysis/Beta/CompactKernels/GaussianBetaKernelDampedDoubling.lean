import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelRefinement
import IPRADerivations.Analysis.RationalArithmetic.Intervals.RationalIntervalArithmeticPrecision
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals

/-!
# Exact relative error of doubling the original beta kernel

On the original half-support, the quadratic Bernoulli surplus and the
actual finite power perturbation give an error relative to the later
beta kernel itself. This finite estimate retains the literal a²/(2b²N)
factor; the cofinal decay comparison and geometric accumulation are
separate consumers.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelDampedDoubling

open_ipra
open GaussianBetaKernelRefinement (value)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- A true finite relative power estimate. All exponents and the
positive factor H remain numerical inputs, including exponent zero. -/
theorem relative_power_error (P Q G H j : PTm n)
    (hPQ : Γ ⊢[PRAAx] le P Q) (hGap : Γ ⊢[PRAAx] Q ≐ P+G)
    (hHQ : Γ ⊢[PRAAx] le H Q) : Γ ⊢[PRAAx]
    le (H*pw Q j) (H*pw P j+j*G*pw Q j) := by
  have gapBound : Γ ⊢[PRAAx] le (one*Q) (one*P+G) :=
    le_congr (one_mul Q).eqSymm (by ipra_ring) (le_congr (.eqRefl Q) hGap (le_refl Q))
  have term := RationalIntervalArithmeticPrecision.natural_power_perturbation Q P Q G one j
    (le_refl Q) hPQ gapBound
  have raw : Γ ⊢[PRAAx] le (Q*pw Q j) (Q*pw P j+j*G*pw Q j) := by
    apply le_congr (by ipra_ring)
      (by
        have e := (natEq (GaussianRationalHornerPerturbation.weighted_power (Γ := Γ) Q j))
        apply deriveNat
        dsimp only [GaussianRationalPowerDifference.budget]
        ipra_simps
        linear_combination 𝔞 G*e)
      (mul_le_mul_right Q term)
  let powerGap := monus (pw Q j) (pw P j)
  let factorGap := monus Q H
  let errorGap := monus (Q*pw P j+j*G*pw Q j) (Q*pw Q j)
  have powerEq := natEq (eq_add_of_le (pw_le_pw j hPQ))
  have factorEq := natEq (eq_add_of_le hHQ)
  have errorEq := natEq (eq_add_of_le raw)
  apply le_of_eq_add (d := errorGap+factorGap*powerGap)
  apply deriveNat
  dsimp only [powerGap,factorGap,errorGap]
  ipra_simps
  linear_combination errorEq+(𝔞 Q-𝔞 H)*powerEq+𝔞(monus (pw Q j) (pw P j))*factorEq

def smaller (a D : PTm n) : PTm n := monus D a*(num 4*D)
def larger (a D : PTm n) : PTm n := pw (monus (two*D) a) two

/-- The surplus is exactly a², not a magnitude or output premise. -/
theorem quadratic_surplus (a D : PTm n) (h : Γ ⊢[PRAAx] le a D) : Γ ⊢[PRAAx]
    larger a D ≐ smaller a D+a*a := by
  have twice : Γ ⊢[PRAAx] le a (two*D) := le_trans h (le_of_eq_add (d := D) (by ipra_ring))
  have e := natEq (eq_add_of_le h)
  have f := natEq (eq_add_of_le twice)
  have square := natEq ((pw_succ (Γ := Γ) (monus (two*D) a) one).eqTrans
    (congrMul (pw_one _) (.eqRefl _)))
  apply deriveNat
  dsimp only [larger,smaller]
  ipra_simps
  rw [square]
  linear_combination -(𝔞(monus (two*D) a)+2*𝔞 D-𝔞 a)*f+4*𝔞 D*e

theorem larger_lower (a D : PTm n) (h : Γ ⊢[PRAAx] le (two*a) D) : Γ ⊢[PRAAx]
    le (two*D*D) (larger a D) := by
  have aSmall : Γ ⊢[PRAAx] le a D := le_trans (le_of_eq_add (d := a) (by ipra_ring)) h
  have twice : Γ ⊢[PRAAx] le a (two*D) := le_trans aSmall (le_of_eq_add (d := D) (by ipra_ring))
  have e := natEq (eq_add_of_le h)
  have f := natEq (eq_add_of_le twice)
  have square := natEq ((pw_succ (Γ := Γ) (monus (two*D) a) one).eqTrans
    (congrMul (pw_one _) (.eqRefl _)))
  apply le_of_eq_add (d := two*D*monus D (two*a)+a*a)
  apply deriveNat
  dsimp only [larger]
  ipra_simps
  rw [square]
  linear_combination -(𝔞(monus (two*D) a)+2*𝔞 D-𝔞 a)*f+2*𝔞 D*e

/-- Exact cleared relative error for the SAME two original kernels.
Their common denominator is (2D)^(2N); neither kernel is replaced. -/
theorem doubling_relative_cleared (a D N : PTm n) (h : Γ ⊢[PRAAx] le (two*a) D) : Γ ⊢[PRAAx]
    le ((two*D*D)*pw (larger a D) N)
      ((two*D*D)*pw (smaller a D) N+N*a*a*pw (larger a D) N) := by
  have small : Γ ⊢[PRAAx] le a D := le_trans (le_of_eq_add (d := a) (by ipra_ring)) h
  exact le_congr (.eqRefl _) (by ipra_ring)
    (relative_power_error (smaller a D) (larger a D) (a*a) (two*D*D) N
      (GaussianBetaKernelRefinement.doubling_square a D small)
      (quadratic_surplus a D small) (larger_lower a D h))

def commonDenominator (D N : PTm n) : PTm n := pw (two*D) (two*N)
def relativeNumerator (a b N : PTm n) : PTm n := a*a*pw (larger a (b*N)) N
def relativeDenominator (b N : PTm n) : PTm n := two*b*b*N*commonDenominator (b*N) N

theorem first_common (a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (value a b N) (ZT.ofNat (pw (smaller a (b*N)) N)) (commonDenominator (b*N) N) := by
  let D := b*N
  have hd := positive_product (Γ := Γ) b N hb hN
  have scaled := GaussianRationalHorner.scalar_rescale (value a b N) _ _ (pw (num 4*D) N)
    (RationalNonnegativePowers.power_represents (monus D a) D N hd)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ ?_ scaled
  · apply ZT.derive
    have e := natEq (AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) (monus D a) (num 4*D) N)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    dsimp only [smaller,D] at e ⊢
    ipra_simps
    linear_combination -e
  · exact (mul_comm _ _).eqTrans (GaussianBetaKernelRefinement.doubling_denominator D N).eqSymm

theorem second_common (a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (value a b (two*N)) (ZT.ofNat (pw (larger a (b*N)) N)) (commonDenominator (b*N) N) := by
  have hd := positive_product (Γ := Γ) b (two*N) hb (positive_product _ _ (le_succ_self one) hN)
  have rep := RationalNonnegativePowers.power_represents (Γ := Γ) (monus (b*(two*N)) a) (b*(two*N)) (two*N) hd
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ ?_ rep
  · apply ZT.derive
    have e := natEq ((congrAp2 powF (.eqRefl (two*N)) (congrMonus (by ipra_ring : Γ ⊢[PRAAx] b*(two*N) ≐ two*(b*N)) (.eqRefl a))).eqTrans
      (AnalyticNumberTheory.RSA.pw_mul (monus (two*(b*N)) a) two N).eqSymm)
    simp only [ZT.toZ_ofNat]
    exact e
  · exact congrAp2 powF (.eqRefl _) (by ipra_ring)

/-- At the actual original scalar outputs, the one-step difference is
at most a²/(2b²N) times the later kernel. The numerator/denominator are
the exact later kernel fraction, not a radius-only replacement. -/
theorem original_doubling_relative_error (a b N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (value a b (two*N)) (value a b N)
      (relativeNumerator a b N) (relativeDenominator b N) := by
  let D := b*N
  let U := pw (larger a D) N
  let V := pw (smaller a D) N
  let H := two*b*b*N
  let K := commonDenominator D N
  have commonPos : Γ ⊢[PRAAx] le one K := RationalNonnegativePowers.denominator_positive _ _
    (positive_product _ _ (le_succ_self one) (positive_product b N h.andE₁ h.andE₂.andE₁))
  have native : Γ ⊢[PRAAx] le (H*U) (H*V+a*a*U) :=
    RationalValueBounds.positive_cancel h.andE₂.andE₁
      (le_congr (by dsimp only [D,U,V,H]; ipra_ring) (by dsimp only [D,U,V,H]; ipra_ring)
        (doubling_relative_cleared a D N h.andE₂.andE₂))
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat U) (ZT.ofNat V) K K
    (relativeNumerator a b N) (relativeDenominator b N) commonPos commonPos
    (second_common a b N h.andE₁ h.andE₂.andE₁) (first_common a b N h.andE₁ h.andE₂.andE₁)
  apply zle_of_toZ (K*K*monus (H*V+a*a*U) (H*U))
  have e := natEq (eq_add_of_le native)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  dsimp only [relativeNumerator,relativeDenominator,D,U,V,H,K] at e ⊢
  ipra_simps
  linear_combination -𝔞(commonDenominator (b*N) N)*𝔞(commonDenominator (b*N) N)*e

theorem original_kernel_doubling_relative_error (a b N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (GaussianBetaKernelExponential.kernel a b (two*N)))
      (fstT (GaussianBetaKernelExponential.kernel a b N))
      (relativeNumerator a b N) (relativeDenominator b N) := by
  have small : Γ ⊢[PRAAx] le a (b*N) := le_trans (le_of_eq_add (d := a) (by ipra_ring)) h.andE₂.andE₂
  have old : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b N := .andI h.andE₁ (.andI h.andE₂.andE₁ small)
  have later : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b (two*N) :=
    .andI h.andE₁ (.andI (positive_product _ _ (le_succ_self one) h.andE₂.andE₁)
      (le_trans small (le_of_eq_add (d := b*N) (by ipra_ring))))
  exact RationalValueBounds.upper_congr (GaussianBetaKernelRefinement.kernel_real_part a b (two*N) later).eqSymm
    (GaussianBetaKernelRefinement.kernel_real_part a b N old).eqSymm (.eqRefl _) (.eqRefl _)
    (original_doubling_relative_error a b N h)

theorem genuine_native_relative_power_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le (var 0) (var 1) ⋏ (var 1 ≐ var 0+var 2 ⋏ le (var 3) (var 1))) ⟶
      le (var 3*pw (var 1) (var 4))
        (var 3*pw (var 0) (var 4)+var 4*var 2*pw (var 1) (var 4))) :=
  closeUniv 5 (.impI (relative_power_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_half_interval_beta_kernel_doubling_relative_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (GaussianBetaKernelLogarithm.source (var 0) (var 1) (var 2) ⟶
        RationalValueBounds.upper (fstT (GaussianBetaKernelExponential.kernel (var 0) (var 1) (two*var 2)))
          (fstT (GaussianBetaKernelExponential.kernel (var 0) (var 1) (var 2)))
          (relativeNumerator (var 0) (var 1) (var 2)) (relativeDenominator (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_kernel_doubling_relative_error _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelDampedDoubling
