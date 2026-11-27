import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedChart
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedBinding
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftChartProper
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.LogDifferences.GaussianGammaDigammaTwoShiftQuotientTranslation
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftCapRepair
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# A checked repaired chart at every precision of the original names

An explicit refinement pays for the local log-Gamma translation guard.
At each precision the original quotient logarithm and the original
cap are independently close to their exact values at the repaired
rational chart. The ordinary quadratic size assumption also certifies
the exact relative-error threshold in that very chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedRepairedChart

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaDigammaTwoShiftNamedWindow (source orders)
open GaussianGammaDigammaTwoShiftRationalWindow (input coefficient)
open GaussianGammaDigammaTwoShiftWindowBuffer (enlarged)
open GaussianGammaDigammaTwoShiftCapRepair (cap)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "RF" => GaussianGammaDigammaTwoShiftBinding.quotientLogF
local notation "RD" => GaussianGammaDigammaTwoShiftBinding.quotientLogData
local notation "RP" => GaussianStirlingGammaLogarithm.source

def translationFactor (j : PR 2) (w : PTm n) : PTm n :=
  GaussianGammaDigammaTwoShiftNamedSize.guardBudget j w+num 24*radius j w+num 48

def disk (f g h j : PR 2) (x y z w : PTm n) : PTm n :=
  two*(radius f x+radius g y+radius h z+translationFactor j w)

def refinement (f g h j : PR 2) (p x y z w M : PTm n) : PTm n :=
  GaussianFastValueCut.exponent
    (num 128*translationFactor j w*(disk f g h j x y z w+one)*((two*M)*(two*M))) p

def quotientBudget (f g h j : PR 2) (x y z w M : PTm n) : PTm n :=
  GaussianGammaDigammaTwoShiftNamedBinding.budget f g h x y z M+GaussianGammaDigammaTwoShiftQuotientTranslation.gain (two*M) (disk f g h j x y z w)*translationFactor j w

def capBudget (f j : PR 2) (x w M : PTm n) : PTm n :=
  GaussianGammaDigammaTwoShiftNamedCap.budget f j x w M+GaussianGammaDigammaTwoShiftCapRepair.gain (two*M) (radius j w) (translationFactor j w)

structure Chart (n : ℕ) where
  base : PTm n
  denominator : PTm n
  left : PTm n
  right : PTm n
  shiftBound : PTm n

def Chart.map {m : ℕ} (σ : Fin n → PTm m) (v : Chart n) : Chart m :=
  ⟨Syn.subst σ v.base,Syn.subst σ v.denominator,Syn.subst σ v.left,Syn.subst σ v.right,Syn.subst σ v.shiftBound⟩

def chart (f g h j : PR 2) (p x y z w M : PTm n) : Chart n :=
  let s := refinement f g h j p x y z w M
  let k := GaussianGammaDigammaTwoShiftNamedChart.clock g h s y z M
  let e := GaussianGammaDigammaTwoShiftNamedChart.pitch f g h j k x y z w
  let u := translationFactor j w*e
  ⟨GaussianGammaDigammaTwoShiftNamedChart.baseNumerator f g h j k s x y z w+u,GaussianGammaDigammaTwoShiftNamedChart.chartDenominator f g h j k s x y z w,
    GaussianGammaDigammaTwoShiftNamedChart.leftNumerator f g h j k s x y z w+u,GaussianGammaDigammaTwoShiftNamedChart.rightNumerator f g h j k s x y z w+u,
    enlarged (GaussianGammaDigammaTwoShiftNamedChart.radiusNumerator f g h j k s x y z w) e⟩

@[simp] theorem subst_translationFactor {m : ℕ} (σ : Fin n → PTm m) (j : PR 2) (w : PTm n) :
    Syn.subst σ (translationFactor j w) = translationFactor j (Syn.subst σ w) := by
  simp [translationFactor,GaussianNamedRightHalfPlane.radius]

@[simp] theorem subst_disk {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (x y z w : PTm n) :
    Syn.subst σ (disk f g h j x y z w) = disk f g h j (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [disk,GaussianNamedRightHalfPlane.radius,two]

@[simp] theorem subst_refinement {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (p x y z w M : PTm n) :
    Syn.subst σ (refinement f g h j p x y z w M) =
      refinement f g h j (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ M) := by
  simp [refinement,one,two]

@[simp] theorem subst_quotientBudget {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (x y z w M : PTm n) :
    Syn.subst σ (quotientBudget f g h j x y z w M) =
      quotientBudget f g h j (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ M) := by
  simp [quotientBudget,GaussianGammaDigammaTwoShiftQuotientTranslation.gain,two]

@[simp] theorem subst_capBudget {m : ℕ} (σ : Fin n → PTm m) (f j : PR 2) (x w M : PTm n) :
    Syn.subst σ (capBudget f j x w M) = capBudget f j (Syn.subst σ x) (Syn.subst σ w) (Syn.subst σ M) := by
  simp [capBudget,GaussianNamedRightHalfPlane.radius,two]

@[simp] theorem subst_chart {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (p x y z w M : PTm n) :
    (chart f g h j p x y z w M).map σ =
      chart f g h j (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ M) := by
  simp [chart,Chart.map,enlarged]

def sizeOrder (f j : PR 2) (x w : PTm n) : Fm PTm n :=
  realOrder (GaussianGammaDigammaTwoShiftNamedSize.nameF j) f (GaussianGammaDigammaTwoShiftNamedSize.data j w) x

@[simp] theorem subst_sizeOrder {m : ℕ} (σ : Fin n → PTm m) (f j : PR 2) (x w : PTm n) :
    (sizeOrder f j x w).subst σ = sizeOrder f j (Syn.subst σ x) (Syn.subst σ w) := by
  simp [sizeOrder]

def ready (f g h j : PR 2) (p x y z w M : PTm n) : Fm PTm n :=
  let F := chart f g h j p x y z w M
  input F.base F.denominator F.left F.right F.shiftBound ⋏
    (independentRate (GaussianGammaDigammaTwoShiftNamedBinding.quotientLogF f g h) RF (GaussianGammaDigammaTwoShiftNamedBinding.quotientLogData f g h x y z M)
      (RD F.base F.denominator F.left F.right) (quotientBudget f g h j x y z w M) (unit p) ⋏
    (independentRate (GaussianGammaDigammaTwoShiftNamedCap.nameF f j) constantF (GaussianGammaDigammaTwoShiftNamedCap.data f j x w M)
      (cap F.base F.denominator F.shiftBound) (capBudget f j x w M) (unit p) ⋏
    (sizeOrder f j x w ⟶ le (coefficient F.denominator F.shiftBound) (F.base*F.denominator))))

private theorem logarithmic_source (a b u E C T : PTm n) (hs : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T)
    (he : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le (two*T*b+u) (C*b))
    (hSmall : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmIncrementMargin.smallStep u E C b) :
    Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftLogGammaTranslation.domain a b u E C := by
  have size := hs.andE₂.andE₂
  have bound : Γ ⊢[PRAAx] le (a+(a+u)) (C*b) := by ipra_le 2*sl size+sl hC
  exact .andI hs.andE₁ (.andI he (.andI hs.andE₂.andE₁ (.andI bound hSmall)))

theorem actual_chart (f g h j : PR 2) (p x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w) :
    Γ ⊢[PRAAx] ready f g h j p x y z w M := by
  let s := refinement f g h j p x y z w M
  let k := GaussianGammaDigammaTwoShiftNamedChart.clock g h s y z M
  let r := GaussianGammaDigammaTwoShiftNamedFreeze.delay g h s y z M
  let A := GaussianGammaDigammaTwoShiftNamedChart.baseNumerator f g h j k s x y z w
  let B := GaussianGammaDigammaTwoShiftNamedChart.chartDenominator f g h j k s x y z w
  let C := GaussianGammaDigammaTwoShiftNamedChart.leftNumerator f g h j k s x y z w
  let D := GaussianGammaDigammaTwoShiftNamedChart.rightNumerator f g h j k s x y z w
  let L := GaussianGammaDigammaTwoShiftNamedChart.radiusNumerator f g h j k s x y z w
  let e := GaussianGammaDigammaTwoShiftNamedChart.pitch f g h j k x y z w
  let J := translationFactor j w
  let u := J*e
  let E := two*M
  let T := disk f g h j x y z w
  let R := radius j w
  let F := GaussianGammaDigammaTwoShiftNamedBinding.quotientLogF f g h
  let X := GaussianGammaDigammaTwoShiftNamedBinding.quotientLogData f g h x y z M
  let q := RD A B C D
  let q' := RD (A+u) B (C+u) (D+u)
  have hp : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have hr : Γ ⊢[PRAAx] le s r := le_trans (le_add_right _ _) (le_add_right _ _)
  have hk : Γ ⊢[PRAAx] le s k := le_trans hr (le_add_right _ _)
  have hkM : Γ ⊢[PRAAx] le (threshold M) k := le_add_left _ _
  have U := unit_positive (Γ := Γ) s
  have wide := GaussianGammaDigammaTwoShiftNamedChart.chart_domains f g h j k s x y z w M hs hkM
  have vf := GaussianGammaDigammaTwoShiftNamedChart.chart_values f g h j k s x y z w M hs hkM
  have rates := GaussianGammaDigammaTwoShiftNamedChart.chart_rates f g h j k s x y z w M hs hkM hk
  have wA := wide.andE₁
  have wC := wide.andE₂.andE₁
  have wD := wide.andE₂.andE₂.andE₁
  have wL := wide.andE₂.andE₂.andE₂
  have ha := wA.andE₁
  have hb := ha.andE₂
  have hL := wL.andE₂.andE₂
  have pitch : Γ ⊢[PRAAx] B ≐ e*unit s := .eqRefl _
  have he : Γ ⊢[PRAAx] le e B := le_congr (.eqRefl _) pitch.eqSymm (by ipra_le 𝔞 e*sl U)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (le_succ_self one) hs.andE₁.andE₁.andE₂.andE₁
  let H := num 128*J*(T+one)*(E*E)
  have q0 : Γ ⊢[PRAAx] le (H*unit p) (unit s) := GaussianFastValueCut.query_budget H p
  have q1 : Γ ⊢[PRAAx] le H (H*unit p) := by ipra_le 𝔞 H*sl (unit_positive (Γ := Γ) p)
  have query := le_trans q1 q0
  have q2 : Γ ⊢[PRAAx] le (e*H) (e*unit s) := by ipra_le 𝔞 e*sl query
  have small : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmIncrementMargin.smallStep u E T B := by
    exact le_congr (by dsimp only [H,u]; ipra_ring) pitch.eqSymm q2
  have buf := GaussianGammaDigammaTwoShiftNamedChart.chart_approximate_window f g h j k s x y z w M hs ho hkM hk
  have lower : Γ ⊢[PRAAx] le (num 9*e) u := by
    dsimp only [u,J,translationFactor]
    ipra_le 𝔞(GaussianGammaDigammaTwoShiftNamedSize.guardBudget j w)*𝔞 e+24*𝔞(radius j w)*𝔞 e+39*𝔞 e
  have repaired := GaussianGammaDigammaTwoShiftWindowBuffer.repairs_window A B C D L e u buf lower
  have domA : Γ ⊢[PRAAx] le (two*radius f x*B+u) (T*B) := by
    dsimp only [T,disk,u]
    ipra_le 𝔞 J*sl he+2*(𝔞(radius g y)+𝔞(radius h z))*𝔞 B+𝔞 J*𝔞 B
  have domC : Γ ⊢[PRAAx] le (two*radius g y*B+u) (T*B) := by
    dsimp only [T,disk,u]
    ipra_le 𝔞 J*sl he+2*(𝔞(radius f x)+𝔞(radius h z))*𝔞 B+𝔞 J*𝔞 B
  have domD : Γ ⊢[PRAAx] le (two*radius h z*B+u) (T*B) := by
    dsimp only [T,disk,u]
    ipra_le 𝔞 J*sl he+2*(𝔞(radius f x)+𝔞(radius g y))*𝔞 B+𝔞 J*𝔞 B
  have analytic : Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftQuotientTranslation.domain A B C D u E T :=
    .andI (logarithmic_source A B u E T _ wA hE domA small)
      (.andI (logarithmic_source C B u E T _ wC hE domC small) (logarithmic_source D B u E T _ wD hE domD small))
  let a₀ := GaussianGammaDigammaTwoShiftNamedFreeze.baseNumerator f g h k x y z
  let b₀ := GaussianGammaDigammaTwoShiftNamedFreeze.chartDenominator f g h k x y z
  let c₀ := GaussianGammaDigammaTwoShiftNamedFreeze.leftNumerator f g h k x y z
  let d₀ := GaussianGammaDigammaTwoShiftNamedFreeze.rightNumerator f g h k x y z
  let q₀ := RD a₀ b₀ c₀ d₀
  have sf : Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftNamedFreeze.source f g h x y z M := .andI hs.andE₁ (.andI hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁)
  have old := GaussianGammaDigammaTwoShiftNamedFreeze.charts f g h k x y z M sf hkM
  have new : Γ ⊢[PRAAx] RP A B ⋏ (RP C B ⋏ RP D B) := .andI ha (.andI wC.andE₁ wD.andE₁)
  have same := GaussianGammaDigammaTwoShiftChartProper.original_log_cross a₀ b₀ c₀ d₀ A B C D old new
    (by simp only [A,B,a₀,b₀,GaussianGammaDigammaTwoShiftNamedChart.baseNumerator,GaussianGammaDigammaTwoShiftNamedChart.chartDenominator,GaussianGammaDigammaTwoShiftNamedChart.pitch]; ipra_ring)
    (by simp only [C,B,c₀,b₀,GaussianGammaDigammaTwoShiftNamedChart.leftNumerator,GaussianGammaDigammaTwoShiftNamedChart.chartDenominator,GaussianGammaDigammaTwoShiftNamedChart.pitch]; ipra_ring)
    (by simp only [D,B,d₀,b₀,GaussianGammaDigammaTwoShiftNamedChart.rightNumerator,GaussianGammaDigammaTwoShiftNamedChart.chartDenominator,GaussianGammaDigammaTwoShiftNamedChart.pitch]; ipra_ring)
  have oldRate : Γ ⊢[PRAAx] independentRate F RF X q₀ (GaussianGammaDigammaTwoShiftNamedBinding.budget f g h x y z M) (unit s) :=
    GaussianGammaDigammaTwoShiftNamedBinding.frozen_log_rate f g h s x y z M sf
  have frozenRate : Γ ⊢[PRAAx] independentRate F RF X q (GaussianGammaDigammaTwoShiftNamedBinding.budget f g h x y z M) (unit s) :=
    GaussianNamedRateTransport.transport F RF F RF X q₀ X q (GaussianGammaDigammaTwoShiftNamedBinding.budget f g h x y z M) (unit s) U oldRate
      (GaussianNameEquivalence.cross_refl _ _ (GaussianGammaDigammaTwoShiftNamedBinding.quotient_log_regular f g h x y z M sf))
      (GaussianNameEquivalence.cross_symm _ _ _ _ same)
  have moved₀ := GaussianGammaDigammaTwoShiftQuotientTranslation.quotient_log_rate A B C D u E T analytic
  have align : Γ ⊢[PRAAx] le ((GaussianGammaDigammaTwoShiftQuotientTranslation.gain E T*u)*unit s) ((GaussianGammaDigammaTwoShiftQuotientTranslation.gain E T*J)*B) :=
    le_of_eq_add (d := ConciseIPRA.PTm.zero)
      ((congrMul (.eqRefl _) pitch).eqTrans (by dsimp only [u]; ipra_ring))
  have moved := GaussianNamedRateRadius.weaken RF RF q' q (GaussianGammaDigammaTwoShiftQuotientTranslation.gain E T*u) B (GaussianGammaDigammaTwoShiftQuotientTranslation.gain E T*J) (unit s) hb U align moved₀
  have allQ := GaussianNamedRateComposition.same_denominator F RF RF X q q' (GaussianGammaDigammaTwoShiftNamedBinding.budget f g h x y z M) (unit s) (GaussianGammaDigammaTwoShiftQuotientTranslation.gain E T*J) U
    frozenRate (GaussianNamedRateComposition.symmetric RF RF q' q (GaussianGammaDigammaTwoShiftQuotientTranslation.gain E T*J) (unit s) U moved)
  have hj := hs.andE₂.andE₂.andE₂.andE₁.andE₁
  have capOld := GaussianGammaDigammaTwoShiftNamedCap.frozen_rate f j s r x w M A B L hs.andE₁ hj ha hr vf.andE₁ hL rates.andE₂.andE₂.andE₂
  have capNew := GaussianGammaDigammaTwoShiftCapRepair.repaired_rate (GaussianGammaDigammaTwoShiftNamedCap.nameF f j) (GaussianGammaDigammaTwoShiftNamedCap.data f j x w M) (GaussianGammaDigammaTwoShiftNamedCap.budget f j x w M)
    A B L e u E R J s ha wA.andE₂.andE₁ he hL (le_refl _) pitch capOld
  refine .andI repaired (.andI (GaussianNamedRateRadius.weaken_dyadic F RF X q' (quotientBudget f g h j x y z w M) p s hp allQ)
    (.andI (GaussianNamedRateRadius.weaken_dyadic (GaussianGammaDigammaTwoShiftNamedCap.nameF f j) constantF (GaussianGammaDigammaTwoShiftNamedCap.data f j x w M) (cap (A+u) B (enlarged L e))
      (capBudget f j x w M) p s hp capNew) (.impI ?_)))
  have rel := GaussianGammaDigammaTwoShiftNamedSize.relative_guard f j x w A L B e s hj.wk hb.wk pitch.wk hL.wk rates.andE₂.andE₂.andE₂.wk rates.andE₁.wk Prf.hyp0
  exact GaussianGammaDigammaTwoShiftWindowBuffer.repairs_relative_threshold A B L e (GaussianGammaDigammaTwoShiftNamedSize.guardBudget j w) R rel

theorem actual_original_named_two_shift_repaired_chart_closed (f g h j : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f g h j (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ orders f g h j (var 1) (var 2) (var 3) (var 4) ⟶
        ready f g h j (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (actual_chart f g h j _ _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedRepairedChart
