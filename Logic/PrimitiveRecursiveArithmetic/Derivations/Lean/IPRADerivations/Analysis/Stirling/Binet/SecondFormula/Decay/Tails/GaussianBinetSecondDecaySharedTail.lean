import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.Tails.GaussianBinetSecondDecayFrozenTail
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# Frozen second Binet tail at an externally chosen mesh and clock

All finite terms use the same physical interval and the same actual
observations. The largest geometric index controls the minimum mesh
and precision. Any common refinement meeting these bounds retains the
integrated reciprocal-square majorant.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecaySharedTail

open GaussianBinetSecondDecayFrozenTail (mesh body row_at_sample_data)
open_ipra
open GaussianBinetSecondDecayGrid (value)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator)
open GaussianCoefficientNameBounds (unit)
open GaussianStirlingConstant (piDenominator)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev clockFloor (N T M k : PTm n) : PTm n :=
  GaussianBinetSecondDecayFrozenTail.clockFloor N T M k

@[simp] theorem subst_clockFloor {m : ℕ} (σ : Fin n → PTm m) (N T M k : PTm n) :
    Syn.subst σ (clockFloor N T M k) =
      clockFloor (Syn.subst σ N) (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ k) :=
  GaussianBinetSecondDecayFrozenTail.subst_clockFloor σ N T M k

theorem shared_row_bound (q N T M k m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le m M) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hn : Γ ⊢[PRAAx] le (mesh T M k) N) (hq : Γ ⊢[PRAAx] le (clockFloor N T M k) (unit q)) :
    Γ ⊢[PRAAx] bounded (value q N T (frozenPiNumerator m k) (piDenominator k) X Y D sign)
      (num 11*K) (m*m) :=
  GaussianBinetSecondDecayFrozenTail.row_bound_at q N T M k m K X Y D sign hz hT hm hM hK hn hq

def data (q N T k C X Y D sign : PTm n) : PTm n :=
  GaussianBinetSecondDecayFrozenTail.data_at q N T k C X Y D sign

ipra_subst data

theorem row_at (i q N T k C X Y D sign : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data q N T k C X Y D sign) ≐
      value q N T (frozenPiNumerator (succ (C+i)) k) (piDenominator k) X Y D sign := by
  exact row_at_sample_data i q N T k C _

theorem tail_bound (q N T k C r K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hn : Γ ⊢[PRAAx] le (mesh T (succ (C+r)) k) N)
    (hq : Γ ⊢[PRAAx] le (clockFloor N T (succ (C+r)) k) (unit q)) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum body r (data q N T k C X Y D sign)) (num 11*K) C :=
  GaussianBinetSecondDecayFrozenTail.tail_bound_at q N T k C r K X Y D sign hz hT hC hK hn hq

/-- The two prefixes traverse the same mesh and share the same π observation. -/
theorem prefix_split (q N T k C r X Y D sign : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum body (C+r) (data q N T k zero X Y D sign) ≐
      GaussianRationalHorner.qadd (GaussianRationalFiniteSum.sum body C (data q N T k zero X Y D sign))
        (GaussianRationalFiniteSum.sum body r (data q N T k C X Y D sign)) := by
  let x := data q N T k zero X Y D sign
  let y := data q N T k C X Y D sign
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (offB body) body r (pairT C x) y := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s r) :: Γ.map Fm.shift
    let x' := data (s q) (s N) (s T) (s k) zero (s X) (s Y) (s D) (s sign)
    let y' := data (s q) (s N) (s T) (s k) (s C) (s X) (s Y) (s D) (s sign)
    let a := frozenPiNumerator (succ (zero+(s C+i))) (s k)
    let b := frozenPiNumerator (succ (s C+i)) (s k)
    have e : Δ ⊢[PRAAx] a ≐ b := congrMul (congrSucc (zero_add (s C+i))) (.eqRefl _)
    have parsed : Δ ⊢[PRAAx] value (s q) (s N) (s T) a (piDenominator (s k)) (s X) (s Y) (s D) (s sign) ≐
        value (s q) (s N) (s T) b (piDenominator (s k)) (s X) (s Y) (s D) (s sign) := by
      simpa only [GaussianBinetSecondDecayGrid.subst_value,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        Prf.eqCongr1 (value (Syn.shift (s q)) (Syn.shift (s N)) (Syn.shift (s T)) (var 0) (Syn.shift (piDenominator (s k)))
          (Syn.shift (s X)) (Syn.shift (s Y)) (Syn.shift (s D)) (Syn.shift (s sign))) e
    have read := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) body (s C) i x').eqTrans
      ((row_at (s C+i) (s q) (s N) (s T) (s k) zero (s X) (s Y) (s D) (s sign)).eqTrans
        (parsed.eqTrans (row_at i (s q) (s N) (s T) (s k) (s C) (s X) (s Y) (s D) (s sign)).eqSymm))
    simpa only [GaussianRationalFiniteSum.termsEqual,Δ,i,s,x,y,x',y',Syn.shift,subst_pairT,subst_data,
      ConciseIPRA.PTm.subst_zero] using read
  exact (GaussianRationalMatrixFiniteSums.sum_split body C r x).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
      (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows))

theorem tail_gap (q N T k C r K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hn : Γ ⊢[PRAAx] le (mesh T (succ (C+r)) k) N)
    (hq : Γ ⊢[PRAAx] le (clockFloor N T (succ (C+r)) k) (unit q)) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalFiniteSum.sum body (C+r) (data q N T k zero X Y D sign))
      (GaussianRationalFiniteSum.sum body C (data q N T k zero X Y D sign)) (num 11*K) C := by
  let x := GaussianRationalFiniteSum.sum body C (data q N T k zero X Y D sign)
  let y := GaussianRationalFiniteSum.sum body r (data q N T k C X Y D sign)
  have exactGap := (GaussianRationalSyntheticDivision.qsub_congr (prefix_split (Γ := Γ) q N T k C r X Y D sign)
    (.eqRefl x)).eqTrans (GaussianRationalSyntheticDivision.qadd_sub_cancel x y
      (GaussianRationalFiniteSum.sum_canonical _ _ _))
  exact bound_congr exactGap.eqSymm (.eqRefl _) (.eqRefl _) (tail_bound q N T k C r K X Y D sign hz hT hC hK hn hq)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecaySharedTail
