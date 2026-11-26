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

open GaussianBinetSecondDecayFrozenTail (mesh body)
open_ipra
open GaussianBinetSecondDecayFinite (finite_bound)
open GaussianBinetSecondDecayGrid (value rowBody)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator frozen_pi_rate)
open GaussianBinetSecondDecayTail (rowBounds finite_tail)
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4 field5
  field0_at field1_at field2_at field3_at field4_at field5_at
  subst_field0 subst_field1 subst_field2 subst_field3 subst_field4 subst_field5)
open GaussianStirlingConstant (piDenominator)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalRiemannRefinement (leftSum)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clockFloor (N T M k : PTm n) : PTm n :=
  let H := frozenPiNumerator M k
  num 20*N+(two*(T*N*H)+(M*M)*T*(num 8+num 10*T))

ipra_subst clockFloor [frozenPiNumerator, one, two]

theorem shared_row_bound (q N T M k m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le m M) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hn : Γ ⊢[PRAAx] le (mesh T M k) N) (hq : Γ ⊢[PRAAx] le (clockFloor N T M k) (unit q)) :
    Γ ⊢[PRAAx] bounded (value q N T (frozenPiNumerator m k) (piDenominator k) X Y D sign)
      (num 11*K) (m*m) := by
  let H := frozenPiNumerator m k
  let Hmax := frozenPiNumerator M k
  let J := piDenominator k
  let C := Hmax*T
  let A := num 20*N
  let B := two*(T*N*Hmax)
  let E := (M*M)*T*(num 8+num 10*T)
  have rate := frozen_pi_rate (Γ := Γ) m k
  have ho : Γ ⊢[PRAAx] le H Hmax := mul_le_mul_right _ hM
  have hN : Γ ⊢[PRAAx] le one N := le_trans (zero_lt_succ _) hn
  have hC : Γ ⊢[PRAAx] le (H*T) C := mul_le_mul_right T ho
  have upC : Γ ⊢[PRAAx] le C N := le_trans (le_trans (le_add_right _ _) (le_succ_self _)) hn
  have sharp : Γ ⊢[PRAAx] le (num 3*((H*T)*(H*T))) N :=
    le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) (sq_le_sq hC)))
      (le_trans (le_trans (le_add_left (num 3*(C*C)) C) (le_succ_self _)) hn)
  have step : Γ ⊢[PRAAx] le (H*T) (J*N) :=
    le_trans (le_trans hC upC) (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N rate.andE₁))
  have grow : Γ ⊢[PRAAx] le (A+(B+E)) (unit q) := hq
  have hA : Γ ⊢[PRAAx] le A (unit q) := le_trans (le_add_right A _) grow
  have hBE : Γ ⊢[PRAAx] le (B+E) (unit q) := le_trans (le_add_left _ A) grow
  have hB : Γ ⊢[PRAAx] le (two*(T*N*H)) (unit q) :=
    le_trans (le_congr (by ipra_ring) (by dsimp only [B]; ipra_ring)
      (mul_le_mul_right (two*T*N) ho)) (le_trans (le_add_right B E) hBE)
  have hE : Γ ⊢[PRAAx] le ((m*m)*T*(num 8+num 10*T)) (unit q) :=
    le_trans (mul_le_mul_right (num 8+num 10*T) (mul_le_mul_right T (sq_le_sq hM)))
      (le_trans (le_add_left E B) hBE)
  exact finite_bound q N T H J m K X Y D sign hz hN hT rate.andE₁ hm rate.andE₂ hK step sharp hA hB hE

private theorem val_five {α : Type} {m : ℕ} (a : α) (u : Fin (m+5) → α) :
    Matrix.vecCons a u 5 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) := rfl
private theorem val_six {α : Type} {m : ℕ} (a : α) (u : Fin (m+6) → α) :
    Matrix.vecCons a u 6 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) := rfl

@[simp] private theorem subst_piNumerator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (GaussianStirlingConstant.piNumerator k) = GaussianStirlingConstant.piNumerator (Syn.subst σ k) := by
  simp [GaussianStirlingConstant.piNumerator,BaselQuadrature.Q,GaussianGammaHalfPiName.clearing,
    GaussianGammaHalfPiName.meshAt,GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,
    GaussianGammaHalfPiName.orderIndex,WallisFinite.Dm,one,two]

@[simp] private theorem subst_piDenominator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (piDenominator k) = piDenominator (Syn.subst σ k) := by
  simp [piDenominator,Products.fact,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
    GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,
    WallisFinite.Dm,one,two]

private def term (i p N T k C x : PTm n) : PTm n :=
  leftSum rowBody N (sampleData p N T (frozenPiNumerator (succ (C+i)) k) (piDenominator k) x) T one

@[simp] private theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (i p N T k C x : PTm n) :
    Syn.subst σ (term i p N T k C x) = term (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ k) (Syn.subst σ C) (Syn.subst σ x) := by
  simp [term,frozenPiNumerator,one]

def data (q N T k C X Y D sign : PTm n) : PTm n :=
  sampleData q N T k C (pairT (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign))

ipra_subst data

theorem row_at (i q N T k C X Y D sign : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data q N T k C X Y D sign) ≐
      value q N T (frozenPiNumerator (succ (C+i)) k) (piDenominator k) X Y D sign := by
  let x := pairT (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign)
  let d := sampleData q N T k C x
  change Γ ⊢[PRAAx] inst2 (term (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1))
    (field3 (var 1)) (field4 (var 1)) (field5 (var 1)) : PTm 2) i d ≐ term i q N T k C x
  simpa only [inst2,subst_term,subst_field0,subst_field1,subst_field2,subst_field3,subst_field4,
    subst_field5,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,val_five,val_six,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![i,field0 d,field1 d,field2 d,field3 d,field4 d,field5 d]) (σ' := ![i,q,N,T,k,C,x])
      (fun j => by
        fin_cases j
        exact .eqRefl _
        exact field0_at _ _ _ _ _ _
        exact field1_at _ _ _ _ _ _
        exact field2_at _ _ _ _ _ _
        exact field3_at _ _ _ _ _ _
        exact field4_at _ _ _ _ _ _
        exact field5_at _ _ _ _ _ _)

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
        (add_le_add_right one (le_congr (add_comm i (s C)) (add_comm (s r) (s C))
          (add_le_add_right (s C) hi)))
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
