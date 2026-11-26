import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalPositiveHeadLogarithm
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSumAxis
import IPRADerivations.Analysis.Stirling.GaussianStirlingNames
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianRealNameExponentialInjectivity

/-! Every observation in the original kept Barnes logarithm is on the real axis. -/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadRealAxis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalPositiveHeadLogarithm (body parameters rowData row_at nameF data)
open GaussianBarnesCanonicalThirdLogarithmRows (shiftedNumerator)
open GaussianHarmonicIntegerExponential (originalExponentF)
open GaussianRealNameExponentialInjectivity (axisSamples)
open GaussianRationalFiniteSumAxis (rowAxes sum_axis)
open RationalGaussianEmbedding (axis axis_congr axis_multiply)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => originalExponentF

theorem row_axis (p A B i : PTm n) : Γ ⊢[PRAAx] axis (ap2 F p (rowData A B i)) := by
  let k := succ i
  let a := shiftedNumerator A B i
  let b := B*k
  let L := GaussianPositiveRationalLogarithm.logF
  let x := GaussianPositiveRationalLogarithm.data a b
  let t := GaussianNaturalScaleProductName.clock L p k x
  have number : Γ ⊢[PRAAx] axis (GaussianRationalNaturalScale.naturalPoint k) :=
    GaussianStirlingNames.fraction_axis k one (le_refl one)
  have realLog := GaussianPositiveRationalLogarithm.sample_axis (Γ := Γ) t a b
  have eq := (GaussianNaturalScaleProductName.product_at (Γ := Γ) L p k x).eqTrans
    (GaussianRationalNaturalScale.natScale_as_product k (ap2 L t x))
  exact axis_congr eq.eqSymm (axis_multiply _ _ number realLog)

theorem sample_axis (p A B N : PTm n) : Γ ⊢[PRAAx] axis (ap2 nameF p (data A B N)) := by
  let q := GaussianFastValueCut.exponent N p
  let x := parameters A B
  let t := GaussianNamedFiniteSumFamily.body F body
  have rows : Γ ⊢[PRAAx] rowAxes t (pairT q x) := by
    refine .allI ?_
    let sh (u : PTm n) := Syn.shift u
    let Δ := Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have e := (GaussianNamedFiniteSumFamily.term_at (Γ := Δ) F body i (sh q) (parameters (sh A) (sh B))).eqTrans
      (congrAp2 F (.eqRefl _) (row_at (sh A) (sh B) i))
    simpa only [t,x,i,sh,Syn.shift,subst_pairT,GaussianBarnesCanonicalPositiveHeadLogarithm.subst_parameters] using
      axis_congr e.eqSymm (row_axis (sh q) (sh A) (sh B) i)
  exact axis_congr (GaussianNamedFiniteSumFamily.sample_at F body p N x).eqSymm (sum_axis t N _ rows)

theorem real_samples (A B N : PTm n) : Γ ⊢[PRAAx] axisSamples nameF (data A B N) := by
  refine .allI ?_
  simpa only [Syn.shift,GaussianBarnesCanonicalPositiveHeadLogarithm.subst_data] using
    sample_axis (Γ := Γ.map Fm.shift) (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift N)

theorem actual_Barnes_kept_power_logarithm_real_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (axisSamples nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (real_samples _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadRealAxis
