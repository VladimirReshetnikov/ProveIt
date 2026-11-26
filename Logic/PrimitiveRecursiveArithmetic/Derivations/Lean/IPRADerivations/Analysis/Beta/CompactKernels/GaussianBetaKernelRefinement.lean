import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelExponential
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntegerExponential
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CertificateTactics

/-!
# Full-interval beta kernel positivity and dyadic refinement

The SAME literal Gaussian beta kernel is the embedding of the original
nonnegative rational power ((bN-a)/(bN))^N. The genuine quadratic
Bernoulli comparison implies monotonicity under doubling N. A true
numerical QF induction carries that actual scalar order through every
internal dyadic refinement, including the endpoint a=bN.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical canonical_unique positive_product)
open GaussianBetaKernelExponential (base kernel)
open GaussianRationalReciprocal (qone)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalArgmin (rationalLE)
open RationalNonnegativePowers (power)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (a b N : PTm n) : Fm PTm n := le one b ⋏ (le one N ⋏ le a (b*N))
def value (a b N : PTm n) : PTm n := power (monus (b*N) a) (b*N) N
def cutoff (N j : PTm n) : PTm n := N*unit j
def refinementLaw (a b N j : PTm n) : Fm PTm n := rationalLE (value a b N) (value a b (cutoff N j))
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    (source a b N).subst σ = source (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (value a b N) = value (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [value]
@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (N j : PTm n) :
    Syn.subst σ (cutoff N j) = cutoff (Syn.subst σ N) (Syn.subst σ j) := by simp [cutoff]
@[simp] theorem subst_refinementLaw {m : ℕ} (σ : Fin n → PTm m) (a b N j : PTm n) :
    (refinementLaw a b N j).subst σ = refinementLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ j) := by simp [refinementLaw]

theorem value_congr {a a' b b' N N' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx]
    value a b N ≐ value a' b' N' := by
  ipra_congr (value (var 0) (var 1) (var 2) : PTm 3) with [ha, hb, hN]

theorem base_fraction (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    base a b N ≐ GaussianPositiveRationalLogarithm.fraction (monus (b*N) a) (b*N) := by
  let D := b*N
  have hd := positive_product (Γ := Γ) _ _ h.andE₁ h.andE₂.andE₁
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add (scale D oneCode) (GaussianBetaKernelLogarithm.negativeNumerator a)) (scale (monus D a) oneCode) := by
    have e := natEq (eq_add_of_le h.andE₂.andE₂)
    apply GaussianRootAlgebra.equal_of_values
    all_goals
      simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianBetaKernelLogarithm.negativeNumerator,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
      dsimp only [D]
      ipra_simps
    · linear_combination e
    · ring
  exact canonical_unique _ _ (scale (monus D a) oneCode) D (GaussianRationalHorner.qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _)
      (GaussianRationalHorner.qadd_represents _ _ _ _ _ hd (GaussianRationalReciprocal.qone_represents_scaled D)
        (ofGaussian_represents _ _ hd))) (ofGaussian_represents _ _ hd)

theorem kernel_embedding (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    kernel a b N ≐ RationalGaussianEmbedding.embed (value a b N) :=
  (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl N) (base_fraction a b N h)).eqTrans
    (GaussianHarmonicIntegerExponential.actual_rational_power _ _ _ (positive_product _ _ h.andE₁ h.andE₂.andE₁))

theorem kernel_real_part (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    fstT (kernel a b N) ≐ value a b N :=
  (congrFst (kernel_embedding a b N h)).eqTrans ((fst_pair _ _).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (RationalNonnegativePowers.power_canonical _ _ _ (positive_product _ _ h.andE₁ h.andE₂.andE₁))))

theorem kernel_nonnegative (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    rationalLE (RationalGaussianEmbedding.scalarZero : PTm n) (fstT (kernel a b N)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (kernel_real_part a b N h).eqSymm
    (RationalNonnegativePowers.power_nonnegative _ _ _ (positive_product _ _ h.andE₁ h.andE₂.andE₁))

/-- The quadratic surplus is literally a², with no strict base guard. -/
theorem doubling_square (a D : PTm n) (h : Γ ⊢[PRAAx] le a D) : Γ ⊢[PRAAx]
    le (monus D a*(num 4*D)) (pw (monus (two*D) a) two) := by
  have hd : Γ ⊢[PRAAx] le a (two*D) := le_trans h (le_of_eq_add (d := D) (by ipra_ring))
  have square : Γ ⊢[PRAAx] pw (monus (two*D) a) two ≐ monus (two*D) a*monus (two*D) a :=
    (pw_succ _ one).eqTrans (congrMul (pw_one _) (.eqRefl _))
  apply le_congr (.eqRefl _) square.eqSymm
  apply le_of_eq_add (d := a*a)
  ipra_lc -(𝔞(monus (two*D) a)+2*𝔞 D-𝔞 a)*natEq (eq_add_of_le hd)+4*𝔞 D*natEq (eq_add_of_le h)

theorem doubling_denominator (D N : PTm n) : Γ ⊢[PRAAx]
    pw (two*D) (two*N) ≐ pw (num 4*D) N*pw D N := by
  have square : Γ ⊢[PRAAx] pw (two*D) two ≐ (num 4*D)*D :=
    (pw_succ _ one).eqTrans ((congrMul (pw_one _) (.eqRefl _)).eqTrans (by ipra_ring))
  exact (AnalyticNumberTheory.RSA.pw_mul (two*D) two N).eqSymm.eqTrans
    ((congrAp2 powF (.eqRefl N) square).eqTrans (AnalyticNumberTheory.LocalFactor.pw_mul_base _ _ _))

theorem doubling_cleared (a D N : PTm n) (h : Γ ⊢[PRAAx] le a D) : Γ ⊢[PRAAx]
    le (pw (monus D a) N*pw (two*D) (two*N)) (pw (monus (two*D) a) (two*N)*pw D N) := by
  have raw := pw_le_pw N (doubling_square a D h)
  have first := le_congr (AnalyticNumberTheory.LocalFactor.pw_mul_base _ _ _) (AnalyticNumberTheory.RSA.pw_mul _ two N) raw
  have multiplied := mul_le_mul_right (pw D N) first
  have assoc : Γ ⊢[PRAAx] (pw (monus D a) N*pw (num 4*D) N)*pw D N ≐
      pw (monus D a) N*(pw (num 4*D) N*pw D N) := by ipra_ring
  exact le_congr (assoc.eqTrans (congrMul (.eqRefl _) (doubling_denominator D N).eqSymm)) (.eqRefl _) multiplied

theorem scalar_doubling (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    rationalLE (value a b N) (value a b (two*N)) := by
  let D := b*N
  have hd := positive_product (Γ := Γ) _ _ h.andE₁ h.andE₂.andE₁
  have hd2 := positive_product (Γ := Γ) _ _ (le_succ_self one) hd
  have cmp := GaussianRationalMetric.comparison_of_cleared (value a b N) (power (monus (two*D) a) (two*D) (two*N))
    _ _ _ _ (RationalNonnegativePowers.denominator_positive D N hd) (RationalNonnegativePowers.denominator_positive _ _ hd2)
    (RationalNonnegativePowers.power_represents _ _ _ hd) (RationalNonnegativePowers.power_represents _ _ _ hd2)
    (le_congr (mul_comm _ _) (.eqRefl _) (doubling_cleared a D N h.andE₂.andE₂))
  have e : Γ ⊢[PRAAx] value a b (two*N) ≐ power (monus (two*D) a) (two*D) (two*N) :=
    RationalNonnegativePowers.fraction_congr (congrAp2 powF (.eqRefl _) (congrMonus (by dsimp only [D]; ipra_ring) (.eqRefl _)))
      (congrAp2 powF (.eqRefl _) (by dsimp only [D]; ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm cmp

theorem cutoff_zero (N : PTm n) : Γ ⊢[PRAAx] cutoff N zero ≐ N :=
  (congrMul (.eqRefl N) (pw_zero two)).eqTrans (by ipra_ring)
theorem cutoff_succ (N j : PTm n) : Γ ⊢[PRAAx] cutoff N (succ j) ≐ two*cutoff N j :=
  (congrMul (.eqRefl N) (pw_succ two j)).eqTrans (by unfold cutoff unit; ipra_ring)
theorem cutoff_ge (N j : PTm n) : Γ ⊢[PRAAx] le N (cutoff N j) :=
  le_congr (by ipra_ring) (by unfold cutoff; ipra_ring) (mul_le_mul_right N (unit_positive j))
theorem refined_source (a b N j : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx] source a b (cutoff N j) :=
  .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ (cutoff_ge N j))
    (le_trans h.andE₂.andE₂ (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl b) (cutoff_ge N j))))

theorem dyadic_order (a b N j : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx] refinementLaw a b N j := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (refinementLaw (Syn.shift a) (Syn.shift b) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_refinementLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact RationalArgmin.rationalLE_congr (.eqRefl _) (value_congr (.eqRefl _) (.eqRefl _) (cutoff_zero N)).eqSymm (RationalArgmin.reflexive _)
    · simp only [subst_refinementLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let i : PTm (n+1) := var 0
      have second := scalar_doubling (Γ := refinementLaw (Syn.shift a) (Syn.shift b) (Syn.shift N) i :: Γ.map Fm.shift)
        (Syn.shift a) (Syn.shift b) (cutoff (Syn.shift N) i) (refined_source _ _ _ _ hs.wk)
      exact RationalArgmin.transitive Prf.hyp0 (RationalArgmin.rationalLE_congr (.eqRefl _)
        (value_congr (.eqRefl _) (.eqRefl _) (cutoff_succ (Syn.shift N) i)).eqSymm second)
  simpa only [subst_refinementLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem kernel_positive (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (kernel a b N) := by
  have hd := positive_product (Γ := Γ) _ _ h.andE₁ h.andE₂.andE₁
  have sign := GaussianRationalL1.nonnegative_of_representation (value a b N) (pw (monus (b*N) a) N) (pw (b*N) N)
    (RationalNonnegativePowers.denominator_positive (b*N) N hd)
    (RationalNonnegativePowers.power_represents (monus (b*N) a) (b*N) N hd)
  exact GaussianPositiveRealArithmetic.positive_congr (kernel_embedding a b N h).eqSymm
    (GaussianPositiveRealArithmetic.positive_embed _ sign)

theorem kernel_refinement_order (a b N j : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    rationalLE (fstT (kernel a b N)) (fstT (kernel a b (cutoff N j))) :=
  RationalArgmin.rationalLE_congr (kernel_real_part a b N h).eqSymm
    (kernel_real_part a b (cutoff N j) (refined_source a b N j h)).eqSymm (dyadic_order a b N j h)

theorem actual_full_interval_beta_kernel_scalar_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ kernel (var 0) (var 1) (var 2) ≐ RationalGaussianEmbedding.embed (value (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (kernel_embedding _ _ _ Prf.hyp0))
theorem actual_full_interval_beta_kernel_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ GaussianPositiveRealArithmetic.positive (kernel (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (kernel_positive _ _ _ Prf.hyp0))
theorem native_beta_kernel_doubling_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ le (pw (monus (var 1) (var 0)) (var 2)*pw (two*var 1) (two*var 2))
      (pw (monus (two*var 1) (var 0)) (two*var 2)*pw (var 1) (var 2))) :=
  closeUniv 3 (.impI (doubling_cleared _ _ _ Prf.hyp0))
theorem actual_full_interval_beta_kernel_dyadic_refinement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ rationalLE (fstT (kernel (var 0) (var 1) (var 2)))
      (fstT (kernel (var 0) (var 1) (cutoff (var 2) (var 3))))) :=
  closeUniv 4 (.impI (kernel_refinement_order _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelRefinement
