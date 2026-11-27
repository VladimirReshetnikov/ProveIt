import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Terminal.GaussianGammaNegativeIntervalNamedTerminalInput
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedIncrementDifferenceQuotientProperness

/-!
# Named increments of the original pole-free Gamma

Adding an increment after the affine shift agrees at each observation
with shifting the sum. This identity transfers the upper endpoint's
pole certificate and allows the same reciprocal of the increment in
the two original divided-difference programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular)
open GaussianGammaNegativeIntervalNamedGammaNativeDomain (input radius shiftF shiftData shift_at shift_regular
  encodedNumerator encodedDenominator frozen_source frozen_shift_at)
open GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding (shift_source)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianReciprocalHorner (qadd_commutative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "incrementF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "incrementData" => GaussianNamedGammaSmallIncrementInput.sumData
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "pd" => GaussianGammaNamedPoleFree.data
local notation "QF" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data

private theorem recode_compare (u : PTm n) :
    Γ ⊢[PRAAx] GaussianFastValueCut.recode u ≐ GaussianTranslatedNonconstant.recode u :=
  GaussianRationalHorner.canonical_unique _ _ _ _
    (GaussianFastValueCut.recode_canonical u) (GaussianTranslatedNonconstant.recode_canonical u)
    (GaussianRationalL1.raw_den_positive u) (GaussianFastValueCut.recode_represents u)
    (GaussianTranslatedNonconstant.recode_represents u)

private theorem translate_sum (u v w : PTm n) :
    Γ ⊢[PRAAx] qadd (qsub (GaussianFastValueCut.recode u) w) v ≐
      qsub (GaussianFastValueCut.recode (qadd u v)) w := by
  let c := qnegative w
  have e : Γ ⊢[PRAAx] qadd (GaussianFastValueCut.recode u) c ≐ qadd u c :=
    (qadd_congr (recode_compare u) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticCoefficientValues.qadd_recode_left u c)
  exact (qadd_congr e (.eqRefl _)).eqTrans ((qadd_associative u c v).eqTrans
    ((qadd_congr (.eqRefl _) (qadd_commutative c v)).eqTrans
      ((qadd_associative u v c).eqSymm.eqTrans
        (qadd_congr (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical u v)).eqSymm
          (.eqRefl _)))))

theorem shifted_sum_at (f K : PR 2) (p x y N : PTm n) :
    Γ ⊢[PRAAx] ap2 (incrementF (shiftF f) K) p (incrementData (shiftData x N) y) ≐
      ap2 (shiftF (incrementF f K)) p (shiftData (incrementData x y) N) := by
  let k := GaussianNamedGammaIncrementInput.clock p
  have left := (GaussianNamedGammaSmallIncrementInput.sample_at (Γ := Γ) (shiftF f) K p (shiftData x N) y).eqTrans
    (qadd_congr (shift_at f k x N) (.eqRefl _))
  have right := (shift_at (Γ := Γ) (incrementF f K) p (incrementData x y) N).eqTrans
    (qsub_congr (GaussianNameArithmetic.recode_congr (GaussianNamedGammaSmallIncrementInput.sample_at f K p x y))
      (.eqRefl _))
  exact left.eqTrans ((translate_sum (ap2 f k x) (ap2 K k y) (naturalPoint (succ N))).eqTrans right.eqSymm)

theorem shifted_sum_source (f K : PR 2) (x y D N : PTm n)
    (h : Γ ⊢[PRAAx] input (incrementF f K) (incrementData x y) D)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN K y) :
    Γ ⊢[PRAAx] GaussianGammaNamedPoleFree.source (incrementF (shiftF f) K) (incrementData (shiftData x N) y) (radius N) D := by
  refine .andI (GaussianNamedGammaSmallIncrementInput.regular _ _ _ _ (shift_regular f x N hf) hk) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let X := incrementData (sh x) (sh y)
  let H := sh D
  let J := sh N
  have hs : Δ ⊢[PRAAx] input (incrementF f K) X H := by
    simpa only [input,Δ,sh,X,H,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source,
      GaussianNamedGammaSmallIncrementInput.subst_sumData] using h.shift
  let p : PTm (n+1) := var 0
  let q := ap2 (incrementF (shiftF f) K) p (incrementData (shiftData (sh x) J) (sh y))
  have exactFraction := (shifted_sum_at (Γ := Δ) f K p (sh x) (sh y) J).eqTrans
    (frozen_shift_at (incrementF f K) p X H J hs)
  have raw := GaussianGammaNamedPoleFreeEncoding.raw_source_of_fraction q
    (encodedNumerator (incrementF f K) p X J) (radius J) (encodedDenominator (incrementF f K) p X) one H
    (frozen_source (incrementF f K) p X H J hs) exactFraction
  simpa only [q,p,Δ,sh,J,H,Syn.shift,GaussianNamedGammaSmallIncrementInput.subst_sumData,
    GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_shiftData,
    GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_radius] using raw

theorem shifted_sum_cross (f K : PR 2) (x y N : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN K y) :
    Γ ⊢[PRAAx] crossEquivalent (incrementF (shiftF f) K) (shiftF (incrementF f K))
      (incrementData (shiftData x N) y) (shiftData (incrementData x y) N) := by
  refine GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNamedGammaSmallIncrementInput.regular _ _ _ _ (shift_regular f x N hf) hk)
    (shift_regular (incrementF f K) (incrementData x y) N (GaussianNamedGammaSmallIncrementInput.regular f K x y hf hk))
    (.allI ?_)
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianNamedGammaSmallIncrementInput.subst_sumData,
    GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_shiftData] using
    shifted_sum_at (Γ := Γ.map Fm.shift) f K (var 0) (Syn.shift x) (Syn.shift y) (Syn.shift N)

def offsetQuotientF (f K : PR 2) : PR 2 := QF (actualF (incrementF f K)) (actualF f) K
def offsetQuotientData (f K : PR 2) (x y E D N a : PTm n) : PTm n :=
  qd (actualF (incrementF f K)) (actualF f) K
    (actualData (incrementF f K) (incrementData x y) D N) (actualData f x E N) y a

def nativeQuotientF (f K : PR 2) : PR 2 := QF (P (incrementF (shiftF f) K)) (P (shiftF f)) K
def nativeQuotientData (f K : PR 2) (x y E D N a : PTm n) : PTm n :=
  qd (P (incrementF (shiftF f) K)) (P (shiftF f)) K
    (pd (incrementData (shiftData x N) y) (radius N) D) (pd (shiftData x N) (radius N) E) y a

theorem original_cross (f K : PR 2) (x y E D N a : PTm n)
    (hf : Γ ⊢[PRAAx] input f x E) (hg : Γ ⊢[PRAAx] input (incrementF f K) (incrementData x y) D)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a y) :
    Γ ⊢[PRAAx] crossEquivalent (offsetQuotientF f K) (nativeQuotientF f K)
      (offsetQuotientData f K x y E D N a) (nativeQuotientData f K x y E D N a) := by
  let g := incrementF f K
  let u := incrementData x y
  let v := incrementData (shiftData x N) y
  let F := actualF g
  let H := P (incrementF (shiftF f) K)
  let G := actualF f
  let J := P (shiftF f)
  let U := actualData g u D N
  let V := pd v (radius N) D
  let X := actualData f x E N
  let Y := pd (shiftData x N) (radius N) E
  have low := shift_source f x E N hf
  have exactHigh := shift_source g u D N hg
  have high := shifted_sum_source f K x y D N hg hf.andE₁ hk.andE₁
  have sameInput := shifted_sum_cross f K x y N hf.andE₁ hk.andE₁
  have joined := GaussianGammaNamedPoleFree.proper (shiftF g) (incrementF (shiftF f) K) (shiftData u N) v (radius N) D
    exactHigh high (cross_symm _ _ _ _ sameInput)
  have upperCross := cross_trans _ _ _ _ _ _
    (GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding.original_cross g u D N hg) joined
  exact GaussianNamedIncrementDifferenceQuotientProperness.proper F H G J K U V X Y y a
    (actual_regular g u D N hg) (GaussianGammaNamedPoleFree.name_regular _ _ _ _ high)
    (actual_regular f x E N hf) (GaussianGammaNamedPoleFree.name_regular _ _ _ _ low) hk upperCross
    (GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding.original_cross f x E N hf)

theorem small_real_increment_cross (f K : PR 2) (x y E N a : PTm n)
    (hf : Γ ⊢[PRAAx] input f x E) (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a y)
    (axis : Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples K y)
    (small : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples K y one (two*E)) :
    Γ ⊢[PRAAx] crossEquivalent (offsetQuotientF f K) (nativeQuotientF f K)
      (offsetQuotientData f K x y E (two*E) N a) (nativeQuotientData f K x y E (two*E) N a) :=
  original_cross f K x y E (two*E) N a hf
    (GaussianGammaNegativeIntervalNamedTerminalDerivative.shifted_offset_source f K x y E hf hk.andE₁ axis small) hk

theorem actual_named_negative_Gamma_increment_transport_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((input f (var 0) (var 2) ⋏ (input (incrementF f K) (incrementData (var 0) (var 1)) (var 3) ⋏
        GaussianNameReciprocal.input K (var 5) (var 1))) ⟶
        crossEquivalent (offsetQuotientF f K) (nativeQuotientF f K)
          (offsetQuotientData f K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (nativeQuotientData f K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_cross f K _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient
