import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedWindow
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedFreeze

/-!
# Actual four-input chart with a shared dyadic pitch

The base, both shifted arguments and the shift radius are observed at
one original late input clock. All four fractions receive the same
denominator, including an extra factor of the dyadic precision.
This keeps the chart values exact and makes one error unit integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedChart

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactLogarithmBounds (domain)
open GaussianGammaDigammaTwoShiftNamedWindow (source orders frozen)
open GaussianGammaMinimumFreezeRational (numerator denominator fraction_at frozen_rational_domain)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingRationalTelescopers (fraction_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev clock (g h : PR 2) (s y z M : PTm n) : PTm n := GaussianGammaDigammaTwoShiftNamedFreeze.clock g h s y z M

def pitch (f g h j : PR 2) (k x y z w : PTm n) : PTm n :=
  GaussianGammaDigammaTwoShiftNamedFreeze.chartDenominator f g h k x y z*denominator j k w

def chartDenominator (f g h j : PR 2) (k s x y z w : PTm n) : PTm n := pitch f g h j k x y z w*unit s

def baseNumerator (f g h j : PR 2) (k s x y z w : PTm n) : PTm n :=
  GaussianGammaDigammaTwoShiftNamedFreeze.baseNumerator f g h k x y z*(denominator j k w*unit s)

def leftNumerator (f g h j : PR 2) (k s x y z w : PTm n) : PTm n :=
  GaussianGammaDigammaTwoShiftNamedFreeze.leftNumerator f g h k x y z*(denominator j k w*unit s)

def rightNumerator (f g h j : PR 2) (k s x y z w : PTm n) : PTm n :=
  GaussianGammaDigammaTwoShiftNamedFreeze.rightNumerator f g h k x y z*(denominator j k w*unit s)

def radiusNumerator (f g h j : PR 2) (k s x y z w : PTm n) : PTm n :=
  numerator j k w*(GaussianGammaDigammaTwoShiftNamedFreeze.chartDenominator f g h k x y z*unit s)

@[simp] theorem subst_pitch {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (k x y z w : PTm n) :
    Syn.subst σ (pitch f g h j k x y z w) =
      pitch f g h j (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [pitch]

@[simp] theorem subst_chartDenominator {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (k s x y z w : PTm n) :
    Syn.subst σ (chartDenominator f g h j k s x y z w) =
      chartDenominator f g h j (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [chartDenominator]

@[simp] theorem subst_baseNumerator {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (k s x y z w : PTm n) :
    Syn.subst σ (baseNumerator f g h j k s x y z w) =
      baseNumerator f g h j (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [baseNumerator]

@[simp] theorem subst_leftNumerator {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (k s x y z w : PTm n) :
    Syn.subst σ (leftNumerator f g h j k s x y z w) =
      leftNumerator f g h j (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [leftNumerator]

@[simp] theorem subst_rightNumerator {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (k s x y z w : PTm n) :
    Syn.subst σ (rightNumerator f g h j k s x y z w) =
      rightNumerator f g h j (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [rightNumerator]

@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (k s x y z w : PTm n) :
    Syn.subst σ (radiusNumerator f g h j k s x y z w) =
      radiusNumerator f g h j (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [radiusNumerator]

private theorem scale_domain (a b A B E K T : PTm n) (hs : Γ ⊢[PRAAx] domain a b K T)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] a*E ≐ A) (hb : Γ ⊢[PRAAx] b*E ≐ B) :
    Γ ⊢[PRAAx] domain A B K T := by
  have f : Γ ⊢[PRAAx] le (b*E) (K*(a*E)) := by ipra_le 𝔞 E*sl hs.andE₂.andE₁
  have g : Γ ⊢[PRAAx] le (a*E) (T*(b*E)) := by ipra_le 𝔞 E*sl hs.andE₂.andE₂
  exact .andI (.andI (le_congr (.eqRefl _) ha (positive_product _ _ hs.andE₁.andE₁ hE))
    (le_congr (.eqRefl _) hb (positive_product _ _ hs.andE₁.andE₂ hE)))
    (.andI (le_congr hb (congrMul (.eqRefl K) ha) f) (le_congr ha (congrMul (.eqRefl T) hb) g))

def domains (f g h j : PR 2) (k s x y z w M : PTm n) : Fm PTm n :=
  let b := chartDenominator f g h j k s x y z w
  domain (baseNumerator f g h j k s x y z w) b (two*M) (radius f x) ⋏
    (domain (leftNumerator f g h j k s x y z w) b (two*M) (radius g y) ⋏
      (domain (rightNumerator f g h j k s x y z w) b (two*M) (radius h z) ⋏
        domain (radiusNumerator f g h j k s x y z w) b (two*M) (radius j w)))

theorem chart_domains (f g h j : PR 2) (k s x y z w M : PTm n) (hs : Γ ⊢[PRAAx] source f g h j x y z w M)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) :
    Γ ⊢[PRAAx] domains f g h j k s x y z w M := by
  let U := unit s
  let b₁ := denominator f k x
  let b₂ := denominator g k y
  let b₃ := denominator h k z
  let b₄ := denominator j k w
  have h₁ := frozen_rational_domain f k x M hs.andE₁ hk
  have h₂ := frozen_rational_domain g k y M hs.andE₂.andE₁ hk
  have h₃ := frozen_rational_domain h k z M hs.andE₂.andE₂.andE₁ hk
  have h₄ := frozen_rational_domain j k w M hs.andE₂.andE₂.andE₂ hk
  have hU := unit_positive (Γ := Γ) s
  have p₁ := h₁.andE₁.andE₂
  have p₂ := h₂.andE₁.andE₂
  have p₃ := h₃.andE₁.andE₂
  have p₄ := h₄.andE₁.andE₂
  refine .andI (scale_domain _ _ _ _ ((b₂*b₃)*(b₄*U)) _ _ h₁
      (positive_product _ _ (positive_product _ _ p₂ p₃) (positive_product _ _ p₄ hU)) ?_ ?_)
    (.andI (scale_domain _ _ _ _ ((b₁*b₃)*(b₄*U)) _ _ h₂
      (positive_product _ _ (positive_product _ _ p₁ p₃) (positive_product _ _ p₄ hU)) ?_ ?_)
    (.andI (scale_domain _ _ _ _ ((b₁*b₂)*(b₄*U)) _ _ h₃
      (positive_product _ _ (positive_product _ _ p₁ p₂) (positive_product _ _ p₄ hU)) ?_ ?_)
      (scale_domain _ _ _ _ ((b₁*(b₂*b₃))*U) _ _ h₄
        (positive_product _ _ (positive_product _ _ p₁ (positive_product _ _ p₂ p₃)) hU) ?_ ?_)))
  all_goals
    simp only [baseNumerator,leftNumerator,rightNumerator,radiusNumerator,chartDenominator,pitch,
      GaussianGammaDigammaTwoShiftNamedFreeze.baseNumerator,GaussianGammaDigammaTwoShiftNamedFreeze.leftNumerator,
      GaussianGammaDigammaTwoShiftNamedFreeze.rightNumerator,GaussianGammaDigammaTwoShiftNamedFreeze.chartDenominator,b₁,b₂,b₃,b₄,U]
    first | exact .eqRefl _ | ipra_ring

def values (f g h j : PR 2) (k s x y z w : PTm n) : Fm PTm n :=
  let b := chartDenominator f g h j k s x y z w
  ap2 f k x ≐ fraction (baseNumerator f g h j k s x y z w) b ⋏
    (ap2 g k y ≐ fraction (leftNumerator f g h j k s x y z w) b ⋏
      (ap2 h k z ≐ fraction (rightNumerator f g h j k s x y z w) b ⋏
        ap2 j k w ≐ fraction (radiusNumerator f g h j k s x y z w) b))

theorem chart_values (f g h j : PR 2) (k s x y z w M : PTm n) (hs : Γ ⊢[PRAAx] source f g h j x y z w M)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) :
    Γ ⊢[PRAAx] values f g h j k s x y z w := by
  have hb := (chart_domains f g h j k s x y z w M hs hk).andE₁.andE₁.andE₂
  have p₁ := (frozen_rational_domain f k x M hs.andE₁ hk).andE₁.andE₂
  have p₂ := (frozen_rational_domain g k y M hs.andE₂.andE₁ hk).andE₁.andE₂
  have p₃ := (frozen_rational_domain h k z M hs.andE₂.andE₂.andE₁ hk).andE₁.andE₂
  have p₄ := (frozen_rational_domain j k w M hs.andE₂.andE₂.andE₂ hk).andE₁.andE₂
  refine .andI ((fraction_at f k x M hs.andE₁ hk).eqTrans (fraction_same _ _ _ _ p₁ hb ?_))
    (.andI ((fraction_at g k y M hs.andE₂.andE₁ hk).eqTrans (fraction_same _ _ _ _ p₂ hb ?_))
      (.andI ((fraction_at h k z M hs.andE₂.andE₂.andE₁ hk).eqTrans (fraction_same _ _ _ _ p₃ hb ?_))
        ((fraction_at j k w M hs.andE₂.andE₂.andE₂ hk).eqTrans (fraction_same _ _ _ _ p₄ hb ?_))))
  all_goals
    simp only [baseNumerator,leftNumerator,rightNumerator,radiusNumerator,chartDenominator,pitch,
      GaussianGammaDigammaTwoShiftNamedFreeze.baseNumerator,GaussianGammaDigammaTwoShiftNamedFreeze.leftNumerator,
      GaussianGammaDigammaTwoShiftNamedFreeze.rightNumerator,GaussianGammaDigammaTwoShiftNamedFreeze.chartDenominator]
    first | exact .eqRefl _ | ipra_ring

theorem chart_rates (f g h j : PR 2) (k s x y z w M : PTm n) (hs : Γ ⊢[PRAAx] source f g h j x y z w M)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) (hsk : Γ ⊢[PRAAx] le s k) :
    Γ ⊢[PRAAx] frozen f g h j x y z w (baseNumerator f g h j k s x y z w) (chartDenominator f g h j k s x y z w)
      (leftNumerator f g h j k s x y z w) (rightNumerator f g h j k s x y z w) (radiusNumerator f g h j k s x y z w) (unit s) := by
  have v := chart_values f g h j k s x y z w M hs hk
  exact .andI (GaussianNamedFrozenScalarOrder.own_rate f x s k _ hs.andE₁.andE₁.andE₁ hsk v.andE₁)
    (.andI (GaussianNamedFrozenScalarOrder.own_rate g y s k _ hs.andE₂.andE₁.andE₁.andE₁ hsk v.andE₂.andE₁)
      (.andI (GaussianNamedFrozenScalarOrder.own_rate h z s k _ hs.andE₂.andE₂.andE₁.andE₁.andE₁ hsk v.andE₂.andE₂.andE₁)
        (GaussianNamedFrozenScalarOrder.own_rate j w s k _ hs.andE₂.andE₂.andE₂.andE₁.andE₁ hsk v.andE₂.andE₂.andE₂)))

theorem chart_approximate_window (f g h j : PR 2) (k s x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) (hsk : Γ ⊢[PRAAx] le s k) :
    Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftWindowBuffer.approximateInput (baseNumerator f g h j k s x y z w)
      (chartDenominator f g h j k s x y z w) (leftNumerator f g h j k s x y z w) (rightNumerator f g h j k s x y z w)
      (radiusNumerator f g h j k s x y z w) (pitch f g h j k x y z w) :=
  GaussianGammaDigammaTwoShiftNamedWindow.approximate_window f g h j x y z w M _ _ _ _ _ _ s hs ho
    (chart_domains f g h j k s x y z w M hs hk).andE₁.andE₁ (.eqRefl _) (chart_rates f g h j k s x y z w M hs hk hsk)

theorem actual_named_two_shift_chart_correct_closed (f g h j : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source f g h j (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        le (threshold (var 6)) (var 0) ⟶ values f g h j (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (chart_values f g h j _ _ _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedChart
