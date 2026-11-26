import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelZero
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart

/-!
# Sharp upper bound for the actual Binet kernel

At a fixed π sample, increasing `t²` only increases the denominator of
each positive rational row. Finite summation preserves the comparison
with the zero input, whose cofinal value is exactly `1/12`.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelPi (denominator_positive sample_margins)
open GaussianBinetKernelRows (inputData rowF rowBody rowData row_at row_sample nativeNum nativeDen weight value_fraction subst_inputData)
open GaussianBinetKernelZero (endpoint endpoint_equivalent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianNameEquivalence (cross_at)
open GaussianNamedFiniteSumFamily (finite body term_at)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (comparison_of_cleared)
open GaussianStirlingConstant (piNumerator piDenominator)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalFiniteSum (termwiseLE sum_monotone)
open RationalGaussianRealPart (realBody real_sum)
open RationalValueBounds (upper upper_of_radius upper_order_left upper_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetKernelCofinal.nameF

theorem row_order (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    rationalLE (fstT (ap2 rowF p (rowData i A B))) (fstT (ap2 rowF p (rowData i zero B))) := by
  let j := succ i
  let u := piNumerator p
  let v := piDenominator p
  let D := two*nativeDen B v
  let K := nativeNum A B j u v
  let L := nativeNum zero B j u v
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hu := le_trans (positive_product _ _ (le_succ_self one) (denominator_positive (Γ := Γ) p))
    (sample_margins p).andE₁
  have hw : Γ ⊢[PRAAx] le one (weight j) := positive_product _ _ (by ipra_le 3) (positive_product _ _ hj hj)
  have hL : Γ ⊢[PRAAx] le one L := le_congr (.eqRefl _) (by dsimp only [L,nativeNum]; ipra_ring)
    (positive_product _ _ (positive_product _ _ hw (positive_product _ _ hu hu)) (positive_product _ _ hB hB))
  have grows : Γ ⊢[PRAAx] le L K := le_congr (by dsimp only [L,nativeNum]; ipra_ring) (.eqRefl _)
    (le_add_left ((weight j*(u*u))*(B*B)) (A*A*(v*v)))
  have hK := le_trans hL grows
  have left := (row_sample (Γ := Γ) p i A B).eqTrans (value_fraction p j A B hB hj)
  have right := (row_sample (Γ := Γ) p i zero B).eqTrans (value_fraction p j zero B hB hj)
  have order := comparison_of_cleared _ _ D D K L hK hL
    (fraction_first_represents D K hK) (fraction_first_represents D L hL)
    (le_congr (.eqRefl _) (mul_comm K D) (mul_le_mul_right D grows))
  exact rationalLE_congr (congrFst left).eqSymm (congrFst right).eqSymm order

private theorem read (p i A B : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term (realBody (body rowF rowBody)) i (pairT p (inputData A B)) ≐
      fstT (ap2 rowF p (rowData i A B)) := by
  simpa only [RationalFiniteSum.term,realBody,inst2,subst_fstT] using
    congrFst ((term_at (Γ := Γ) rowF rowBody i p (inputData A B)).eqTrans
      (congrAp2 rowF (.eqRefl _) (row_at i A B)))

theorem finite_order (p N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    rationalLE (fstT (finite rowF rowBody p N (inputData A B))) (fstT (finite rowF rowBody p N (inputData zero B))) := by
  let t := body rowF rowBody
  let x := pairT p (inputData A B)
  let y := pairT p (inputData zero B)
  have rows : Γ ⊢[PRAAx] termwiseLE (realBody t) (realBody t) N x y := by
    refine .allI (.impI ?_)
    let s (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift.wk
    simpa only [Δ,t,x,y,s,Syn.shift,subst_pairT,subst_inputData,ConciseIPRA.PTm.subst_zero] using
      rationalLE_congr (read (s p) (var 0) (s A) (s B)).eqSymm (read (s p) (var 0) zero (s B)).eqSymm
        (row_order (s p) (var 0) (s A) (s B) hs)
  exact rationalLE_congr (real_sum t N x).eqSymm (real_sum t N y).eqSymm (sum_monotone _ _ N x y rows)

theorem same_clock_order (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    rationalLE (fstT (ap2 F p (inputData A B))) (fstT (ap2 F p (inputData zero B))) := by
  let N := GaussianBinetKernelCofinal.cutoff p
  let k := GaussianFastValueCut.exponent N (succ p)
  have a := (GaussianBinetKernelCofinal.sample_at (Γ := Γ) p A B).eqTrans
    (GaussianNamedFiniteSumFamily.sample_at rowF rowBody (succ p) N (inputData A B))
  have b := (GaussianBinetKernelCofinal.sample_at (Γ := Γ) p zero B).eqTrans
    (GaussianNamedFiniteSumFamily.sample_at rowF rowBody (succ p) N (inputData zero B))
  exact rationalLE_congr (congrFst a).eqSymm (congrFst b).eqSymm (finite_order k N A B hB)

theorem upper_observations (p q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    upper (fstT (ap2 F p (inputData A B))) (fstT (ap2 constantF q endpoint)) (unit p+unit q) (unit p*unit q) := by
  have order := same_clock_order p A B hB
  have eq := cross_at F constantF (inputData zero B) endpoint p q (endpoint_equivalent B hB)
  have up := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive q)) eq)
  exact upper_order_left _ _ _ _ _ order up

/-- The actual sampled real coordinate is at most `1/12 + 2⁻ᵖ`. -/
theorem sample_upper (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    upper (fstT (ap2 F p (inputData A B))) (fstT endpoint) one (unit p) := by
  let a := fstT (ap2 F p (inputData A B))
  let b := fstT (endpoint : PTm n)
  let q := GaussianNamedRealOrderTransport.precision a b (unit p) one
  apply GaussianNamedRealOrderTransport.remove_upper_slack a b one (unit p) one
  exact upper_congr (.eqRefl _) (congrFst (constant_at q endpoint)) (by ipra_ring) (.eqRefl _)
    (upper_observations p q A B hB)

theorem upper_order (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    realOrder F constantF (inputData A B) endpoint := by
  refine .allI (.allI ?_)
  let s (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have h : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift.shift
  simpa only [realOrder,Δ,s,Syn.shift,subst_inputData,endpoint,GaussianPositiveRationalLogarithm.subst_fraction,
    LeanProofs.IPRA.PTm.subst_num,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    upper_observations (var 1) (var 0) (s A) (s B) h

theorem actual_Binet_kernel_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ realOrder F constantF (inputData (var 0) (var 1)) endpoint) :=
  closeUniv 2 (.impI (upper_order _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelUpper
