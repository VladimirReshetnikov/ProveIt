import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedDiscreteDerivativeBounds

/-!
# Third-difference lower bound from nested fine derivative rates

For fine step 1/D and coarse stride M, let E0, E1, and E2 bound
the three original scaled derivative residuals at every fine step.
If the actual third derivative observations are at least -T, the
original coarse third difference times D³ is at least
-M³T - 4D²M E0 - 2DM² E1 - M³ E2.

The coarse stride and the fine derivative precisions remain
independent. No third-order estimate on the coarse first derivative
is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1550000

namespace LeanProofs.IPRA.Analysis.SignedDiscreteThirdDerivativeEstimate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open SignedDiscreteDerivativeBlock (source subst_source)
open SignedDiscreteDerivativeOperators (width divisor delta accumulate accumulate_at subst_width subst_divisor)
open SignedDiscreteThirdDerivativeIdentity (defect coarseThird third_decomposition decomposition)
open SignedDiscreteDerivativeBounds
  (floorOn bandOn floor_at band_at block_floor block_band delta_band defect_band subst_floorOn subst_bandOn)
open PeriodicThirdDifferenceConstancy (band_congr)
open PolynomialBisection (zle_add zle_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem stride_lt (x i K L : PTm n) (hi : Γ ⊢[PRAAx] lt i K)
    (h : Γ ⊢[PRAAx] le (K+width x) L) : Γ ⊢[PRAAx] lt (i+width x) L :=
  le_trans (le_congr (succ_add i (width x)) (.eqRefl _) (add_le_add_right (width x) hi)) h

private theorem shift_window (x K L : PTm n) (h : Γ ⊢[PRAAx] le (K+width x) L) :
    lt (var 0) (Syn.shift K) :: Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift K+width (Syn.shift x)) (Syn.shift L) := by
  simpa only [Fm.shift,Syn.shift,subst_le,LeanProofs.IPRA.PTm.subst_add,subst_width] using h.shift.wk

private theorem defect_window (b g : ZB) (x K L E : PTm n)
    (h : Γ ⊢[PRAAx] source b g x L (divisor x) E) (hKL : Γ ⊢[PRAAx] le (K+width x) L) :
    Γ ⊢[PRAAx] bandOn (defect b g) x K (width x*E) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh K) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source b g (sh x) (sh L) (divisor (sh x)) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source,subst_divisor] using h.shift.wk
  have he := le_of_lt (stride_lt (sh x) i (sh K) (sh L) (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh K))
    (shift_window x K L hKL))
  simpa only [Δ,i,sh,Syn.shift,LeanProofs.IPRA.PTm.subst_mul,subst_width] using
    defect_band b g (sh x) (sh L) (sh E) i hs he

private theorem floor_window (b : ZB) (x K L E : PTm n)
    (h : Γ ⊢[PRAAx] floorOn b x L E) (hKL : Γ ⊢[PRAAx] le (K+width x) L) :
    Γ ⊢[PRAAx] floorOn (accumulate b) x K (width x*E) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh K) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] floorOn b (sh x) (sh L) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_floorOn] using h.shift.wk
  have he := le_of_lt (stride_lt (sh x) i (sh K) (sh L) (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh K))
    (shift_window x K L hKL))
  have hb := block_floor b (sh x) (sh L) (sh E) i (width (sh x)) hs he
  have result := zle_congr rfl (accumulate_at (Γ := Δ) b (sh x) i).symm hb
  simpa only [Δ,i,sh,Syn.shift,LeanProofs.IPRA.PTm.subst_mul,subst_width] using result

private theorem sum_window (b : ZB) (x K L E : PTm n)
    (h : Γ ⊢[PRAAx] bandOn b x L E) (hKL : Γ ⊢[PRAAx] le (K+width x) L) :
    Γ ⊢[PRAAx] bandOn (accumulate b) x K (width x*E) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh K) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] bandOn b (sh x) (sh L) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_bandOn] using h.shift.wk
  have he := le_of_lt (stride_lt (sh x) i (sh K) (sh L) (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh K))
    (shift_window x K L hKL))
  have hb := block_band b (sh x) (sh L) (sh E) i (width (sh x)) hs he
  have e := accumulate_at (Γ := Δ) b (sh x) i
  have result : Δ ⊢[PRAAx] PeriodicThirdDifferenceConstancy.band ((accumulate b).val i (sh x))
      (width (sh x)*sh E) := band_congr e.symm (.eqRefl _) hb
  simpa only [Δ,i,sh,Syn.shift,LeanProofs.IPRA.PTm.subst_mul,subst_width] using result

private theorem difference_window (b : ZB) (x K L E : PTm n)
    (h : Γ ⊢[PRAAx] bandOn b x L E) (hKL : Γ ⊢[PRAAx] le (K+width x) L) :
    Γ ⊢[PRAAx] bandOn (delta b) x K (divisor x*(two*E)) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh K) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] bandOn b (sh x) (sh L) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_bandOn] using h.shift.wk
  have he := stride_lt (sh x) i (sh K) (sh L) (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh K))
    (shift_window x K L hKL)
  simpa only [Δ,i,sh,Syn.shift,LeanProofs.IPRA.PTm.subst_mul,subst_divisor,two,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    delta_band b (sh x) (sh L) (sh E) i hs he

def window (x i : PTm n) : PTm n := ((succ i+width x)+width x)+width x

def budget (x T E₀ E₁ E₂ : PTm n) : PTm n :=
  let M := width x
  let D := divisor x
  M*(M*M)*T+num 4*(D*D)*(M*E₀)+two*D*(M*M)*E₁+M*(M*M)*E₂

theorem coarse_lower (b g h j : ZB) (x i T E₀ E₁ E₂ : PTm n)
    (h₀ : Γ ⊢[PRAAx] source b g x (window x i) (divisor x) E₀)
    (h₁ : Γ ⊢[PRAAx] source g h x (window x i) (divisor x) E₁)
    (h₂ : Γ ⊢[PRAAx] source h j x (window x i) (divisor x) E₂)
    (hj : Γ ⊢[PRAAx] floorOn j x (window x i) T) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (budget x T E₀ E₁ E₂)) (coarseThird b x i) := by
  let M := width x
  let D := divisor x
  let L₀ := succ i
  let L₁ := L₀+M
  let L₂ := L₁+M
  let L₃ := L₂+M
  have top := floor_window j x L₂ L₃ T hj (le_refl L₃)
  have mid := floor_window _ x L₁ L₂ (M*T) top (le_refl L₂)
  have end' := floor_window _ x L₀ L₁ (M*(M*T)) mid (le_refl L₁)
  have init0 := defect_window b g x L₂ L₃ E₀ h₀ (le_refl L₃)
  have init1 := defect_window g h x L₂ L₃ E₁ h₁ (le_refl L₃)
  have init2 := defect_window h j x L₂ L₃ E₂ h₂ (le_refl L₃)
  have end0 := difference_window _ x L₀ L₁ (D*(two*(M*E₀)))
    (difference_window _ x L₁ L₂ (M*E₀) init0 (le_refl L₂)) (le_refl L₁)
  have end1 := sum_window _ x L₀ L₁ (D*(two*(M*E₁)))
    (difference_window _ x L₁ L₂ (M*E₁) init1 (le_refl L₂)) (le_refl L₁)
  have end2 := sum_window _ x L₀ L₁ (M*(M*E₂))
    (sum_window _ x L₁ L₂ (M*E₂) init2 (le_refl L₂)) (le_refl L₁)
  have atI : Γ ⊢[PRAAx] lt i L₀ := le_refl L₀
  have a := floor_at _ x L₀ (M*(M*(M*T))) i end' atI
  have b₀ := band_at _ x L₀ _ i end0 atI
  have b₁ := band_at _ x L₀ _ i end1 atI
  have b₂ := band_at _ x L₀ _ i end2 atI
  have total := zle_add (zle_add (zle_add a b₀.andE₁) b₁.andE₁) b₂.andE₁
  refine zle_congr ?_ ?_ total
  · simp only [budget,M,D,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_add,map_add,Q.mk_mul,map_mul]
    ipra_simps
    ring
  · simpa only [decomposition,ZT.toZ_add] using (third_decomposition (Γ := Γ) b g h j x i).symm

theorem actual_signed_coarse_third_derivative_lower_closed (b g h j : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let x := var 0
       let i := var 1
       let T := var 2
       let E₀ := var 3
       let E₁ := var 4
       let E₂ := var 5
       source b g x (window x i) (divisor x) E₀ ⟶
         source g h x (window x i) (divisor x) E₁ ⟶
           source h j x (window x i) (divisor x) E₂ ⟶
             floorOn j x (window x i) T ⟶
               zle (-ZT.ofNat (budget x T E₀ E₁ E₂)) (coarseThird b x i)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (coarse_lower b g h j _ _ _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.SignedDiscreteThirdDerivativeEstimate
