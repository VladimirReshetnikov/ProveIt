import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelRows

/-!
# Strictly positive finite Binet kernel observations

The original finite sum retains a nonnegative real tail. Its first
row supplies a positive rational lower bound throughout a bounded
real time interval, at the sum program's actual common row clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelPositive

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelRows (inputData rowBody rowF rowData row_lower row_positive lowerDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRealArithmetic (positive positive_add positive_congr positiveTerms positive_sum)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalSupMetric (numeratorOf denominatorOf)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "observedBody" => GaussianNamedFiniteSumFamily.body rowF rowBody
local notation "finite" => GaussianNamedFiniteSumFamily.finite rowF rowBody

abbrev nameF : PR 2 := GaussianNamedFiniteSumFamily.nameF rowF rowBody
abbrev data (N A B : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data N (inputData A B)

private theorem entry_at (p i A B : PTm n) :
    Γ ⊢[PRAAx] inst2 observedBody i (pairT p (inputData A B)) ≐ ap2 rowF p (rowData i A B) :=
  (GaussianNamedFiniteSumFamily.term_at rowF rowBody i p (inputData A B)).eqTrans
    (congrAp2 rowF (.eqRefl p) (GaussianBinetKernelRows.row_at i A B))

private theorem positive_tail (p M A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] positive (GaussianRationalFiniteSum.sum (shiftBody observedBody) M (pairT p (inputData A B))) := by
  apply positive_sum
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh M) :: Γ.map Fm.shift
  have hh : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ, sh, Fm.shift, Syn.shift, one] using hB.shift.wk
  have term := positive_congr (entry_at (Γ := Δ) (sh p) (succ (var 0)) (sh A) (sh B)).eqSymm
    (row_positive (sh p) (succ (var 0)) (sh A) (sh B) hh)
  simpa only [positiveTerms, Syn.shift, sh, subst_pairT, GaussianBinetKernelRows.subst_inputData,
    inst2_shiftBody, Δ] using term

private theorem real_le_add (x y : PTm n) (hy : Γ ⊢[PRAAx] positive y) :
    Γ ⊢[PRAAx] rationalLE (fstT x) (fstT (qadd x y)) := by
  let a := fstT x
  let b := fstT y
  let A := denominatorOf a
  let B := denominatorOf b
  let c := numeratorOf a
  let e := GaussianPositiveRealArithmetic.numerator b
  have hA := RationalArgmin.denominator_positive (Γ := Γ) a
  have hB := RationalArgmin.denominator_positive (Γ := Γ) b
  have ar := RationalRepresentations.represents_self (Γ := Γ) a
  have br := GaussianPositiveRealArithmetic.natural_representation b hy.andE₂
  have both := RationalRepresentations.represents_add a b c (ZT.ofNat e) A B ar br
  have bound : Γ ⊢[PRAAx] rationalLE a (RationalArithmetic.add a b) := by
    apply RationalArithmetic.order_of_representations _ _ _ _ A (A*B) ar both hA (positive_product _ _ hA hB)
    apply zle_of_toZ (e*A*A)
    simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_ofNat, Q.mk_mul, map_mul]
    ring
  exact rationalLE_congr (.eqRefl _) (fst_pair _ _).eqSymm bound

theorem finite_at (p N A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] positive (finite p N (inputData A B)) ⋏
      rationalLE (fstT (fraction two (lowerDenominator T zero))) (fstT (finite p N (inputData A B))) := by
  let M := pred N
  let X := pairT p (inputData A B)
  let head := ap2 rowF p (rowData zero A B)
  let tail := GaussianRationalFiniteSum.sum (shiftBody observedBody) M X
  have read : Γ ⊢[PRAAx] finite p N (inputData A B) ≐ qadd head tail :=
    (GaussianRationalFiniteSum.sum_index_congr observedBody (RationalIntegerNormalization.positive_form hN)
      (.eqRefl X)).eqTrans ((GaussianRationalFiniteSum.sum_shift_first observedBody M X).eqTrans
        (qadd_congr (entry_at p zero A B) (.eqRefl tail)))
  have hHead := row_positive p zero A B hB
  have hTail := positive_tail p M A B hB
  exact .andI (positive_congr read.eqSymm (positive_add head tail hHead hTail))
    (rationalLE_congr (.eqRefl _) (congrFst read).eqSymm
      (RationalArgmin.transitive (row_lower p zero A B T hB hT) (real_le_add head tail hTail)))

theorem named_finite_at (p N A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] positive (ap2 nameF p (data N A B)) ⋏
      rationalLE (fstT (fraction two (lowerDenominator T zero))) (fstT (ap2 nameF p (data N A B))) := by
  have e := GaussianNamedFiniteSumFamily.sample_at (Γ := Γ) rowF rowBody p N (inputData A B)
  have h := finite_at (GaussianFastValueCut.exponent N p) N A B T hB hN hT
  exact .andI (positive_congr e.eqSymm h.andE₁) (rationalLE_congr (.eqRefl _) (congrFst e).eqSymm h.andE₂)

theorem actual_nonempty_finite_Binet_kernel_strict_positive_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 3) ⟶ le one (var 1) ⟶ le (var 2) (var 4*var 3) ⟶
        (positive (ap2 nameF (var 0) (data (var 1) (var 2) (var 3))) ⋏
          rationalLE (fstT (fraction two (lowerDenominator (var 4) zero)))
            (fstT (ap2 nameF (var 0) (data (var 1) (var 2) (var 3)))))) :=
  closeUniv 5 (.impI (.impI (.impI (named_finite_at _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelPositive
