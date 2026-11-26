import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelRows
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelTailMajorant
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyRange
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSumMajorant

/-!
# Sharp tails for the actual finite Binet kernel names

At a common row precision, the difference of two finite prefixes is the
exact interval sum. Bounding the interval by `1/(8N)` and transporting
the named samplers gives the same leading bound at independent precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelRows (rowF rowBody rowData inputData row_at row_bound regular_rows)
open GaussianBinetKernelTailMajorant (eight_positive)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedFiniteSumFamily (finite term_at)
open GaussianNamedFiniteSumFamilyRange (rangeBody range_row_at finite_split)
open GaussianNamedFiniteSumFamilySplit (finite_sample_distance)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (bounded qsub distanceBounded comparison_to_cleared)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSumMajorant (majorized termsMajorized from_representation majorized_congr sum_majorized)
open GaussianRationalSyntheticDivision (qsub_congr qadd_sub_cancel)
open RationalSupMetric (denominatorOf)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "eight" => num 8

abbrev finiteF : PR 2 := GaussianNamedFiniteSumFamily.nameF rowF rowBody
abbrev finiteData (N A B : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data N (inputData A B)

private abbrev intervalBody : PTm 2 := GaussianNamedFiniteSumFamily.body rowF (rangeBody rowBody)
private def intervalData (p N A B : PTm n) : PTm n := pairT p (pairT N (inputData A B))

@[simp] private theorem subst_intervalData {m : ℕ} (σ : Fin n → PTm m) (p N A B : PTm n) :
    Syn.subst σ (intervalData p N A B) = intervalData (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) :=
  by simp [intervalData, inputData]

private theorem interval_row (p N i A B : PTm n) : Γ ⊢[PRAAx]
    inst2 intervalBody i (intervalData p N A B) ≐ ap2 rowF p (rowData (N+i) A B) := by
  let x := inputData A B
  have row := (range_row_at (Γ := Γ) rowBody N i x).eqTrans (row_at (N+i) A B)
  exact (term_at rowF (rangeBody rowBody) i p (pairT N x)).eqTrans (congrAp2 rowF (.eqRefl _) row)

private theorem interval_row_majorized (p N i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    majorized (inst2 intervalBody i (intervalData p N A B))
      (inst2 GaussianBinetKernelTailMajorant.body i (GaussianBinetKernelTailMajorant.data N)) := by
  let k := succ (N+i)
  let D := eight*(k*k)
  let x := ap2 rowF p (rowData (N+i) A B)
  let y := fraction one D
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ eight_positive (positive_product _ _ hk hk)
  have rep := fraction_represents (Γ := Γ) one D hd
  have sign := GaussianRationalL1.nonnegative_of_representation y one D hd rep
  exact majorized_congr (interval_row p N i A B).eqSymm (GaussianBinetKernelTailMajorant.term_at N i).eqSymm
    (from_representation x y one D hd sign rep (row_bound p (N+i) A B hB))

theorem interval_bound (p N r A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (finite rowF (rangeBody rowBody) p r (pairT N (inputData A B))) one (eight*N) := by
  let x := intervalData p N A B
  let S := GaussianRationalFiniteSum.sum intervalBody r x
  let M := GaussianBinetKernelTailMajorant.sum N r
  have rows : Γ ⊢[PRAAx] termsMajorized intervalBody GaussianBinetKernelTailMajorant.body r x
      (GaussianBinetKernelTailMajorant.data N) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s r) :: Γ.map Fm.shift
    have hbs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift.wk
    simpa only [Δ,x,s,Syn.shift,subst_intervalData,GaussianBinetKernelTailMajorant.subst_data] using
      interval_row_majorized (s p) (s N) (var 0) (s A) (s B) hbs
  have a : Γ ⊢[PRAAx] majorized S M := sum_majorized _ _ r _ _ rows
  have hD : Γ ⊢[PRAAx] le one (eight*N) := positive_product _ _ eight_positive hN
  have hM := RationalArgmin.denominator_positive (Γ := Γ) M
  have clear := comparison_to_cleared M (fraction one (eight*N))
    (GaussianPositiveRealArithmetic.numerator M) one (denominatorOf M) (eight*N)
    (GaussianPositiveRealArithmetic.natural_representation M a.andE₁) (fraction_represents _ _ hD)
    (GaussianBinetKernelTailMajorant.bound N r hN)
  exact bounded_radius_mono _ _ _ _ _ hM hD
    (le_congr (mul_comm _ _) (.eqRefl _) clear) a.andE₂

theorem finite_gap (p N r A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (finite rowF rowBody p (N+r) (inputData A B)) (finite rowF rowBody p N (inputData A B)) one (eight*N) := by
  let x := inputData A B
  let u := finite rowF rowBody p N x
  let v := finite rowF (rangeBody rowBody) p r (pairT N x)
  have split := finite_split (Γ := Γ) rowF rowBody p N r x
  have cancel := (qsub_congr split (.eqRefl u)).eqTrans (qadd_sub_cancel u v
    (GaussianRationalFiniteSum.sum_canonical intervalBody r (intervalData p N A B)))
  exact bound_congr cancel.eqSymm (.eqRefl _) (.eqRefl _) (interval_bound p N r A B hN hB)

private theorem diagonal (p N r A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 finiteF p (finiteData (N+r) A B)) (ap2 finiteF p (finiteData N A B))
      (diagonalNumerator one (eight*N) (num 4) p) (diagonalDenominator (eight*N) p) := by
  let x := inputData A B
  let k := exponent (N+r) p
  let U := unit p
  let V := eight*N
  let D := V*U
  have hU := unit_positive (Γ := Γ) p
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ eight_positive hN
  have hD := positive_product _ _ hV hU
  have hk := query_budget (Γ := Γ) (N+r) p
  have hk' := le_trans (mul_le_mul_right U (le_add_right (Γ := Γ) N r)) hk
  have left := distance_symmetric _ _ _ _ hU
    (finite_sample_distance rowF rowBody k p (N+r) x (regular_rows (N+r) A B hB) hk)
  have middle := finite_gap k N r A B hN hB
  have right := finite_sample_distance rowF rowBody k p N x (regular_rows N A B hB) hk'
  have lift (y z C E P : PTm n) (he : Γ ⊢[PRAAx] le one E)
      (balance : Γ ⊢[PRAAx] C*D ≐ P*E) (e : Γ ⊢[PRAAx] distanceBounded y z C E) : Γ ⊢[PRAAx]
      distanceBounded y z P D :=
    distance_radius_mono _ _ _ _ _ _ he hD (le_congr balance.eqSymm (.eqRefl _) (le_refl _)) e
  have a := lift _ _ two U (two*V) hU (by dsimp only [D]; ipra_ring) left
  have b := lift _ _ one V U hV (by dsimp only [D]; ipra_ring) middle
  have c := lift _ _ two U (two*V) hU (by dsimp only [D]; ipra_ring) right
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [diagonalNumerator,V,U]; ipra_ring) (.eqRefl D)
    (distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD a b) c)

theorem finite_rate (N r A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    independentRate finiteF finiteF (finiteData (N+r) A B) (finiteData N A B) one (eight*N) := by
  let x := inputData A B
  apply GaussianNamedLipschitzRate.independent_rate finiteF finiteF _ _ one (eight*N) (num 4)
    (positive_product _ _ eight_positive hN) (GaussianNamedFiniteSumFamily.regular rowF rowBody (N+r) x (regular_rows (N+r) A B hB))
    (GaussianNamedFiniteSumFamily.regular rowF rowBody N x (regular_rows N A B hB))
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hN.shift
  have hb : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift
  simp only [Syn.shift, x, GaussianNamedFiniteSumFamily.subst_data, GaussianBinetKernelRows.subst_inputData,
    PTm.subst_mul, PTm.subst_add, PTm.subst_num, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  exact diagonal (var 0) (s N) (s r) (s A) (s B) hn hb

theorem ordered_observations (p q M N A B : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hnm : Γ ⊢[PRAAx] le N M) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 finiteF p (finiteData M A B)) (ap2 finiteF q (finiteData N A B))
      (rateNumerator one (eight*N) p q) (rateDenominator (eight*N) p q) := by
  let r := monus M N
  have e : Γ ⊢[PRAAx] M ≐ N+r := eq_add_of_le hnm
  have raw := rate_at finiteF finiteF (finiteData (N+r) A B) (finiteData N A B) one (eight*N) p q (finite_rate N r A B hN hB)
  exact distance_congr (congrAp2 finiteF (.eqRefl _) (congrPairT e.eqSymm (.eqRefl _)))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

theorem actual_finite_Binet_kernel_tail_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 0) ⟶ le one (var 3) ⟶ independentRate finiteF finiteF
        (finiteData (var 0+var 1) (var 2) (var 3)) (finiteData (var 0) (var 2) (var 3)) one (eight*var 0)) :=
  closeUniv 4 (.impI (.impI (finite_rate _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelTail
