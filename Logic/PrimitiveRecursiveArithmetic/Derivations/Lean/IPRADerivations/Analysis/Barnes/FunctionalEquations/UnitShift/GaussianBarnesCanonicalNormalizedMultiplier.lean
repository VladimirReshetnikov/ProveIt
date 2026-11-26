import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalNormalizedExponent
import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalTerminalPower
import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalGaussNormalizers

/-!
# Exact exponential normalizer of the finite Barnes recurrence

The literal terminal power and the original finite shift exponent,
multiplied by the original Gauss exponential, equal the exponential
of the normalized remainder times the exact factorial constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalizedMultiplier

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalBaseProductShift (terminal)
open GaussianBarnesCanonicalGaussNormalizers (integerLogF integerLogData integerExpData integer_log_exponential factorial_log_exponential)
open GaussianBarnesCanonicalNormalizedExponent (offset offsetF offsetData)
open GaussianBarnesCanonicalTerminalRemainder (source scaledF scaledData scaled_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (logF log_regular logExponentF logExponentData log_exponent_regular
  exponentialInputData exponential_input)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative add_associative add_commutative negativeF negativeData negative_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (qnegative)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (power)
open Products (fact)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "X" => GaussianBarnesCanonicalNormalizedExponent.nameF
local notation "xd" => GaussianBarnesCanonicalNormalizedExponent.data
local notation "F" => GaussianBarnesCanonicalPrefixShift.exponentF
local notation "fd" => GaussianBarnesCanonicalPrefixShift.exponentData
local notation "MF" => GaussianBarnesCanonicalPrefixShift.multiplierF
local notation "md" => GaussianBarnesCanonicalPrefixShift.multiplierData
local notation "G" => GaussianStirlingGammaLogarithm.logGammaF
local notation "gd" => GaussianStirlingGammaLogarithm.logGammaData

abbrev nameF : PR 2 := E X
def data (z R B K : PTm n) : PTm n := ed X (xd z R B K)
abbrev gaussF : PR 2 := E logExponentF
def gaussData (z B K : PTm n) : PTm n := ed logExponentF (logExponentData (translated z B one) B K)

private theorem exp_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (E f) (ed f x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ h)

private theorem merge (f g h : PR 2) (x y z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) (e : Γ ⊢[PRAAx] crossEquivalent (addF f g) h (addData x y) z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (E f) (E g)) (E h) (multiplyData (E f) (E g) (ed f x) (ed g y)) (ed h z) :=
  GaussianGammaFoldedApproximantBalance.exponential_product_equivalent f g h (U f x) (U g y) (U h z) x y z
    (exponential_input _ _ hf) (exponential_input _ _ hg) (exponential_input _ _ hh) e

private theorem add_back (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (addF (GaussianNamedDifference.nameF f g) g) f
      (addData (GaussianNamedDifference.data x y) y) x := by
  let N := negativeF g
  let t := negativeData y
  have hn := negative_fast g y hg
  have neg := cross_trans _ _ _ _ _ _ (add_commutative N g t y hn hg) (GaussianNameRingLaws.add_negative g y hg)
  have drop := add_cross f f (addF N g) GaussianNameRingLaws.zeroF x x (addData t y) y hf hf
    (add_fast _ _ _ _ hn hg) (GaussianNameRingLaws.zero_fast y) (cross_refl _ _ hf) neg
  have eq : Γ ⊢[PRAAx] crossEquivalent GaussianNameRingLaws.zeroF GaussianNameRingLaws.zeroF y x := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (GaussianNameRingLaws.zero_fast y) (GaussianNameRingLaws.zero_fast x)
    refine .allI ?_
    exact (GaussianNameRingLaws.zero_at (var 0) (Syn.shift y)).eqTrans (GaussianNameRingLaws.zero_at (var 0) (Syn.shift x)).eqSymm
  have replace := add_cross f f GaussianNameRingLaws.zeroF GaussianNameRingLaws.zeroF x x y x hf hf
    (GaussianNameRingLaws.zero_fast y) (GaussianNameRingLaws.zero_fast x) (cross_refl _ _ hf) eq
  exact cross_trans _ _ _ _ _ _ (add_associative f N g x t y hf hn hg)
    (cross_trans _ _ _ _ _ _ drop (cross_trans _ _ _ _ _ _ replace (GaussianNameRingLaws.add_zero f x hf)))

private theorem offset_cross (z B K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    crossEquivalent (addF integerLogF logExponentF) offsetF
      (addData (integerLogData K) (logExponentData (translated z B one) B K)) (offsetData z B K) := by
  let w := translated z B one
  let a := naturalPoint K
  let b := qnegative (ofGaussian w B)
  let x := multiplyData C logF a K
  let y := multiplyData C logF b K
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have hk := log_regular K hK
  have re := add_cross integerLogF integerLogF logExponentF integerLogF x x (logExponentData w B K) y
    (multiply_fast _ _ _ _ ha hk) (multiply_fast _ _ _ _ ha hk)
    (multiply_fast _ _ _ _ hk hb) (multiply_fast _ _ _ _ hb hk)
    (cross_refl _ _ (multiply_fast _ _ _ _ ha hk)) (multiply_commutative logF C K b hk hb)
  have dist := cross_symm _ _ _ _ (GaussianNameRingLaws.right_distributive C C logF a b K ha hb hk)
  have reduce := multiply_cross (addF C C) C logF logF (addData a b) (offset z B K) K K
    (add_fast _ _ _ _ ha hb) (constant_regular _) hk hk
    (GaussianNamedGammaHalfShift.constant_sum a b (offset z B K) (.eqRefl _)) (cross_refl _ _ hk)
  exact cross_trans _ _ _ _ _ _ re (cross_trans _ _ _ _ _ _ dist reduce)

private theorem rearrange (f g h j : PR 2) (x y z t : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) (hj : Γ ⊢[PRAAx] pointCN j t) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF (multiplyF f g) h) j) (multiplyF (multiplyF h g) (multiplyF f j))
      (multiplyData (multiplyF (multiplyF f g) h) j (multiplyData (multiplyF f g) h (multiplyData f g x y) z) t)
      (multiplyData (multiplyF h g) (multiplyF f j) (multiplyData h g z y) (multiplyData f j x t)) := by
  let a := multiplyData f g x y
  let b := multiplyData g f y x
  let c := multiplyData h g z y
  have ha := multiply_fast f g x y hf hg
  have hb := multiply_fast g f y x hg hf
  have hc := multiply_fast h g z y hh hg
  have inside := multiply_cross h h (multiplyF f g) (multiplyF g f) z z a b hh hh ha hb (cross_refl _ _ hh)
    (multiply_commutative f g x y hf hg)
  have e := cross_trans _ _ _ _ _ _ (multiply_commutative (multiplyF f g) h a z ha hh)
    (cross_trans _ _ _ _ _ _ inside (cross_symm _ _ _ _ (multiply_associative h g f z y x hh hg hf)))
  have outside := multiply_cross (multiplyF (multiplyF f g) h) (multiplyF (multiplyF h g) f) j j
    (multiplyData (multiplyF f g) h a z) (multiplyData (multiplyF h g) f c x) t t
    (multiply_fast _ _ _ _ ha hh) (multiply_fast _ _ _ _ hc hf) hj hj e (cross_refl _ _ hj)
  exact cross_trans _ _ _ _ _ _ outside (multiply_associative (multiplyF h g) f j c x t hc hf hj)

theorem multiplier_cross (z R B N : PTm n) (hs : Γ ⊢[PRAAx] source (translated z B one) R B (succ N)) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF MF gaussF) (multiplyF nameF C)
      (multiplyData MF gaussF (md z B (succ N)) (gaussData z B (succ N)))
      (multiplyData nameF C (data z R B (succ N)) (naturalPoint (fact N))) := by
  let K := succ N
  let w := translated z B one
  let t := scaledData w R B K
  let a := fd z B K
  let i := integerLogData K
  let j := logExponentData w B K
  let o := offsetData z B K
  let s := addData (addData a t) o
  let Z := addF (addF F scaledF) offsetF
  let x := xd z R B K
  let g := gd K one
  let q := terminal z B K
  let U' := multiplyF (E integerLogF) (E scaledF)
  let u := multiplyData (E integerLogF) (E scaledF) (ed integerLogF i) (ed scaledF t)
  have hK := hs.andE₂.andE₁
  have ha : Γ ⊢[PRAAx] pointCN F a := add_fast _ _ _ _
    (GaussianBarnesCanonicalPrefactorShift.difference_regular z B) (constant_regular _)
  have ht := scaled_regular w R B K hs
  have hi := multiply_fast C logF (naturalPoint K) K (constant_regular _) (log_regular K hK)
  have hj := log_exponent_regular w B K hK
  have ho := multiply_fast C logF (offset z B K) K (constant_regular _) (log_regular K hK)
  have hg := GaussianStirlingGammaLogarithm.log_gamma_regular K one (.andI hK (le_refl one))
  have hz := add_fast _ _ _ _ (add_fast _ _ _ _ ha ht) ho
  have hx : Γ ⊢[PRAAx] pointCN X x := GaussianNamedDifference.name_regular Z G s g hz hg
  have hI := exp_regular integerLogF i hi
  have hT := exp_regular scaledF t ht
  have hF := exp_regular F a ha
  have hJ := exp_regular logExponentF j hj
  have hU := multiply_fast _ _ _ _ hI hT
  have eqTerm := multiply_cross (E integerLogF) C (E scaledF) C (ed integerLogF i) (power (naturalPoint K) K)
    (ed scaledF t) (GaussianBarnesCanonicalTerminalPower.normalizedPower w B K) hI (constant_regular _) hT (constant_regular _)
    (integer_log_exponential K hK) (GaussianBarnesCanonicalTerminalPower.exponentiated_scaled w R B K hs)
  have qprod := constant_product_cross (Γ := Γ) (power (naturalPoint K) K) (GaussianBarnesCanonicalTerminalPower.normalizedPower w B K)
  have toTerm : Γ ⊢[PRAAx] crossEquivalent U' C u q := cross_trans _ _ _ _ _ _ eqTerm
    (cross_trans _ _ _ _ _ _ qprod (constant_data_cross _ _
      (GaussianBarnesCanonicalTerminalPower.terminal_factorization z B K hs.andE₁ hK).eqSymm))
  have a1 := multiply_cross C U' (E F) (E F) q u (ed F a) (ed F a) (constant_regular _) hU hF hF
    (cross_symm _ _ _ _ toTerm) (cross_refl _ _ hF)
  have a2 := multiply_cross MF (multiplyF U' (E F)) gaussF gaussF (md z B K) (multiplyData U' (E F) u (ed F a))
    (gaussData z B K) (gaussData z B K) (multiply_fast _ _ _ _ (constant_regular _) hF)
    (multiply_fast _ _ _ _ hU hF) hJ hJ a1 (cross_refl _ _ hJ)
  have a3 := rearrange (E integerLogF) (E scaledF) (E F) gaussF (ed integerLogF i) (ed scaledF t) (ed F a) (gaussData z B K)
    hI hT hF hJ
  have p := add_fast F scaledF a t ha ht
  have l := merge F scaledF (addF F scaledF) a t (addData a t) ha ht p (cross_refl _ _ p)
  have m := merge integerLogF logExponentF offsetF i j o hi hj ho (offset_cross z B K hK)
  have join := multiply_cross (multiplyF (E F) (E scaledF)) (E (addF F scaledF)) (multiplyF (E integerLogF) gaussF) (E offsetF)
    (multiplyData (E F) (E scaledF) (ed F a) (ed scaledF t)) (ed (addF F scaledF) (addData a t))
    (multiplyData (E integerLogF) gaussF (ed integerLogF i) (gaussData z B K)) (ed offsetF o)
    (multiply_fast _ _ _ _ hF hT) (exp_regular _ _ p) (multiply_fast _ _ _ _ hI hJ) (exp_regular _ _ ho) l m
  have toSum := merge (addF F scaledF) offsetF Z (addData a t) o s p ho hz (cross_refl _ _ hz)
  have back := merge X G Z x g s hx hg hz (add_back Z G s g hz hg)
  have fact := multiply_cross nameF nameF (E G) C (data z R B K) (data z R B K)
    (ed G g) (naturalPoint (fact N)) (exp_regular _ _ hx) (exp_regular _ _ hx)
    (exp_regular _ _ hg) (constant_regular _) (cross_refl _ _ (exp_regular _ _ hx)) (factorial_log_exponential N)
  exact cross_trans _ _ _ _ _ _ a2 (cross_trans _ _ _ _ _ _ a3 (cross_trans _ _ _ _ _ _ join
    (cross_trans _ _ _ _ _ _ toSum (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ back) fact))))

theorem actual_Barnes_normalized_exponential_multiplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let N := var 3
     let K := succ N
     source (translated z B one) R B K ⟶ crossEquivalent (multiplyF MF gaussF) (multiplyF nameF C)
       (multiplyData MF gaussF (md z B K) (gaussData z B K))
       (multiplyData nameF C (data z R B K) (naturalPoint (fact N)))) :=
  closeUniv 4 (.impI (multiplier_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalizedMultiplier
