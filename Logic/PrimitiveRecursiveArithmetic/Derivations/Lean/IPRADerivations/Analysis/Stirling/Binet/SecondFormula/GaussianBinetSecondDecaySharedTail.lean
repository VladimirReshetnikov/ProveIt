import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondDecayFrozenTail
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

open GaussianBinetSecondDecayFrozenTail (mesh body mesh_bounds clock_bounds row_at_sample_data)
open_ipra
open GaussianBinetSecondDecayFinite (finite_bound)
open GaussianBinetSecondDecayGrid (value)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator frozen_pi_rate)
open GaussianBinetSecondDecayTail (rowBounds finite_tail)
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (sampleData)
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
      (num 11*K) (m*m) := by
  have rate := frozen_pi_rate (Γ := Γ) m k
  have meshBound := mesh_bounds N T M k m hM hn
  have clockBound := clock_bounds q N T M k m hM hq
  exact finite_bound q N T _ _ m K X Y D sign hz meshBound.andE₁ hT rate.andE₁ hm rate.andE₂ hK
    meshBound.andE₂.andE₁ meshBound.andE₂.andE₂ clockBound.andE₁ clockBound.andE₂.andE₁ clockBound.andE₂.andE₂

def data (q N T k C X Y D sign : PTm n) : PTm n :=
  sampleData q N T k C (pairT (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign))

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
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum body r (data q N T k C X Y D sign)) (num 11*K) C := by
  have rows : Γ ⊢[PRAAx] rowBounds body (data q N T k C X Y D sign) (num 11*K) C r := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s r) :: Γ.map Fm.shift
    let m := succ (s C+i)
    let M := succ (s C+s r)
    have sz : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have st : Δ ⊢[PRAAx] le one (s T) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hT.shift.wk
    have sk : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    have sn : Δ ⊢[PRAAx] le (mesh (s T) M (s k)) (s N) := by
      simpa only [Δ,M,s,Fm.shift,Syn.shift,subst_le,GaussianBinetSecondDecayFrozenTail.subst_mesh,
        ConciseIPRA.PTm.subst_succ,PTm.subst_add] using hn.shift.wk
    have sq : Δ ⊢[PRAAx] le (clockFloor (s N) (s T) M (s k)) (unit (s q)) := by
      simpa only [Δ,M,s,Fm.shift,Syn.shift,subst_le,subst_clockFloor,
        ConciseIPRA.PTm.subst_succ,PTm.subst_add,GaussianCoefficientNameBounds.subst_unit] using hq.shift.wk
    have hi : Δ ⊢[PRAAx] le i (s r) := le_of_lt Prf.hyp0
    have order : Δ ⊢[PRAAx] le m M :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
        (add_le_add_right one (add_le_add_left (s C) hi))
    have estimate := shared_row_bound (s q) (s N) (s T) M (s k) m (s K) (s X) (s Y) (s D) (s sign)
      sz st (zero_lt_succ _) order sk sn sq
    have read := row_at (Γ := Δ) i (s q) (s N) (s T) (s k) (s C) (s X) (s Y) (s D) (s sign)
    simpa only [rowBounds,Δ,i,m,M,s,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num] using
      bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) estimate
  exact finite_tail _ _ _ _ _ hC rows

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
