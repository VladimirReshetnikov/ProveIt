import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaParameterRates
import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletCofinal
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Effective parameter continuity of the original Dirichlet sampler

A precision chooses one common internal truncation for two parameters.
The actual cutoff rates pay for the two tails, and a later input clock
pays for variation of the original common finite prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletParameterRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerPositiveScalingConstant (inverseF inverseData)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaDirichletFiniteRate (budget prefixData)
open GaussianGammaZetaDirichletRowDecay (block block_positive)
open GaussianGammaZetaMellinDampedImproper (dirichletF dirichletBody dirichlet_at parameters)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianNamedRateRadius (weaken)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianGammaZetaDirichletCofinal.nameF
local notation "cd" => GaussianGammaZetaDirichletCofinal.data
local notation "gain" => GaussianEulerCompactPowerParameterRate.gain

def prefixGain (R N : PTm n) : PTm n := N*gain (R+one+one) N one

def pay (s : PTm n) : PTm n := succ (succ s)

def tailLevel (s A : PTm n) : PTm n := exponent (budget A) (pay s)

def cutoff (s A : PTm n) : PTm n := block A (tailLevel s A)

def demand (s R A : PTm n) : PTm n := exponent (prefixGain R (cutoff s A)) (pay s)

@[simp] theorem subst_demand {m : ℕ} (σ : Fin n → PTm m) (s R A : PTm n) :
    Syn.subst σ (demand s R A) = demand (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ A) := by
  simp [demand,prefixGain,cutoff,tailLevel,pay,one]

private theorem row_data_congr (x y x' y' H D : PTm n)
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') (h : Γ ⊢[PRAAx] independentRate inverseF inverseF x y H D) :
    Γ ⊢[PRAAx] independentRate inverseF inverseF x' y' H D := by
  let φ : Fm PTm 4 := independentRate inverseF inverseF (var 0) (var 1) (var 2) (var 3)
  have h' := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) φ ![x,y,H,D] ![x',y',H,D]
    (fun i => by
      fin_cases i
      · exact hx
      · exact hy
      · exact .eqRefl H
      · exact .eqRefl D)
    (by simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val] using h)
  simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val] using h'

private theorem original_rows (N z w R B D A H E : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) H E) :
    Γ ⊢[PRAAx] GaussianNamedFiniteSumFamilyRate.rows inverseF inverseF dirichletBody dirichletBody N
      (parameters (shifted z B) (R+one) B A) (parameters (shifted w D) (R+one) D A)
      (gain (R+one+one) N one*H) E := by
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  let j : PTm (n+1) := succ (var 0)
  let zs := shifted (sh z) (sh B)
  let ws := shifted (sh w) (sh D)
  have za : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift.wk
  have wa : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift.wk
  have hn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hN.shift.wk
  have he : Δ ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hE.shift.wk
  have hdist : Δ ⊢[PRAAx] distanceBounded (ofGaussian (sh z) (sh B)) (ofGaussian (sh w) (sh D)) (sh H) (sh E) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hd.shift.wk
  have lr := GaussianGammaZetaDirichletPowerOrder.shifted_source (sh z) (sh R) (sh B) (sh A) za
  have rr := GaussianGammaZetaDirichletPowerOrder.shifted_source (sh w) (sh R) (sh D) (sh A) wa
  have hb := lr.andE₁.andE₂.andE₁.andE₁
  have hD := rr.andE₁.andE₂.andE₁.andE₁
  have lx : Δ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source zs (sh R+one) (sh B) (sh N) :=
    .andI hb (.andI hn lr.andE₁.andE₂.andE₁.andE₂)
  have rx : Δ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source ws (sh R+one) (sh D) (sh N) :=
    .andI hD (.andI hn rr.andE₁.andE₂.andE₁.andE₂)
  have hv := GaussianGammaZetaParameterRates.shifted_distance (sh z) (sh w) (sh B) (sh D) (sh H) (sh E) hb hD he hdist
  have row := GaussianGammaZetaParameterRates.dirichlet_rate zs ws (sh R+one) (sh B) (sh D) (sh N) j (sh H) (sh E)
    lx rx (zero_lt_succ _) Prf.hyp0 he hv
  have read := row_data_congr (inverseData zs (sh B) j one) (inverseData ws (sh D) j one)
    (inst2 dirichletBody (var 0) (parameters zs (sh R+one) (sh B) (sh A)))
    (inst2 dirichletBody (var 0) (parameters ws (sh R+one) (sh D) (sh A)))
    (gain (sh R+one+one) (sh N) one*sh H) (sh E)
    (dirichlet_at (var 0) zs (sh R+one) (sh B) (sh A)).eqSymm
    (dirichlet_at (var 0) ws (sh R+one) (sh D) (sh A)).eqSymm row
  simpa only [Syn.shift,sh,Δ,zs,ws,GaussianGammaZetaMellinDampedImproper.subst_parameters,
    GaussianGammaEulerHeadShift.subst_shifted,GaussianEulerCompactPowerParameterRate.subst_gain,
    PTm.subst_add,PTm.subst_mul,one,PTm.subst_succ,PTm.subst_zero] using read

theorem finite_rate (N z w R B D A H E : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) H E) :
    Γ ⊢[PRAAx] independentRate dirichletF dirichletF (prefixData N z R B A) (prefixData N w R D A)
      (prefixGain R N*H) E := by
  have h := GaussianNamedFiniteSumFamilyRate.original_rate inverseF inverseF dirichletBody dirichletBody N
    (parameters (shifted z B) (R+one) B A) (parameters (shifted w D) (R+one) D A)
    (gain (R+one+one) N one*H) E hE (original_rows N z w R B D A H E hz hw hN hE hd)
  exact GaussianNamedDifferenceRate.rate_parameters_congr dirichletF dirichletF
    (prefixData N z R B A) (prefixData N w R D A) (N*(gain (R+one+one) N one*H)) E
    (prefixGain R N*H) E (by unfold prefixGain; ipra_ring) (.eqRefl E) h

private theorem unit_pay (s : PTm n) : Γ ⊢[PRAAx] unit (pay s) ≐ two*(two*unit s) :=
  (GaussianRationalHalfAngleRecovery.unit_succ (succ s)).eqTrans
    (congrMul (.eqRefl two) (GaussianRationalHalfAngleRecovery.unit_succ s))

theorem original_demand_rate (s z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (demand s R A))) :
    Γ ⊢[PRAAx] independentRate C C (cd z R B A) (cd w R D A) one (unit s) := by
  let t := pay s
  let h := tailLevel s A
  let N := cutoff s A
  let U := unit t
  let X := prefixData N z R B A
  let Y := prefixData N w R D A
  let xd := cd z R B A
  let yd := cd w R D A
  let k := demand s R A
  have hp := unit_positive (Γ := Γ) t
  have ht : Γ ⊢[PRAAx] le (budget A*U) (one*unit h) :=
    le_congr (.eqRefl _) (one_mul (unit h)).eqSymm (query_budget (budget A) t)
  have htL := GaussianGammaZetaDirichletCofinal.cutoff_rate N z R B A h hz (le_refl N)
  have htR := GaussianGammaZetaDirichletCofinal.cutoff_rate N w R D A h hw (le_refl N)
  have nl := weaken dirichletF C X xd (budget A) (unit h) one U (unit_positive h) hp ht htL
  have nr := weaken dirichletF C Y yd (budget A) (unit h) one U (unit_positive h) hp ht htR
  have fin := finite_rate N z w R B D A one (unit k) hz hw (block_positive A h) (unit_positive k) hd
  have hc : Γ ⊢[PRAAx] le ((prefixGain R N*one)*U) (one*unit k) :=
    le_congr (by ipra_ring) (one_mul (unit k)).eqSymm (query_budget (prefixGain R N) t)
  have mid := weaken dirichletF dirichletF X Y (prefixGain R N*one) (unit k) one U (unit_positive k) hp hc fin
  have first := symmetric dirichletF C X xd one U hp nl
  have both := same_denominator C dirichletF C xd Y yd (one+one) U one hp
    (same_denominator C dirichletF dirichletF xd X Y one U one hp first mid) nr
  refine weaken C C xd yd (one+one+one) U one (unit s) hp (unit_positive s) ?_ both
  exact le_of_eq_add (d := unit s) ((by ipra_ring :
    Γ ⊢[PRAAx] (one+one+one)*unit s+unit s ≐ one*(two*(two*unit s))).eqTrans
      (congrMul (.eqRefl one) (unit_pay s).eqSymm)).eqSymm

theorem actual_original_Dirichlet_parameter_demand_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 1) (var 3) (var 4) (var 6) ⟶ source (var 2) (var 3) (var 5) (var 6) ⟶
        distanceBounded (ofGaussian (var 1) (var 4)) (ofGaussian (var 2) (var 5)) one
          (unit (demand (var 0) (var 3) (var 6))) ⟶
        independentRate C C (cd (var 1) (var 3) (var 4) (var 6)) (cd (var 2) (var 3) (var 5) (var 6))
          one (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (.impI (original_demand_rate _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletParameterRate
