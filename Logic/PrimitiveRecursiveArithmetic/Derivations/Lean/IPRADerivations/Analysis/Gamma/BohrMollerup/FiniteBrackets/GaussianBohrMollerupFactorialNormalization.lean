import IPRADerivations.Analysis.Gamma.BohrMollerup.FiniteBrackets.GaussianBohrMollerupFiniteRecurrence
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyCongruence

/-!
# Integer values of a fixed Bohr–Mollerup presentation

Iterating the original recurrence from 1 yields the literal harmonic
sum of integer logarithms. The checked factorial logarithm identity
then identifies f(j+1) with log(j!).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupFactorialNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupBracketEndpoints (rowBody row_at sumData sum_regular)
open GaussianBohrMollerupChords (base argument_congr rescale_from)
open GaussianBohrMollerupPresentation (Presentation argument laws observe_value)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianLogGammaFactorialLogSum (harmonicBody harmonic_factorial_cross)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF zero_fast add_zero_left)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamilyCongruence (family_sum_cross)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianStirlingGammaLogarithm (source)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "logData" => GaussianHarmonicLogarithmName.data
local notation "Sum" => GaussianBohrMollerupBracketEndpoints.sumF

theorem integer_sum (j : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent Sum H (sumData one one j) (logData (fact j) one) := by
  have rows : Γ ⊢[PRAAx] equalRows H H rowBody harmonicBody j (pairT one one) zero := by
    refine .allI (.impI ?_)
    let i : PTm (n+1) := var 0
    let Δ := lt i (Syn.shift j)::Γ.map Fm.shift
    have ei : Δ ⊢[PRAAx] one+one*i ≐ succ i := by ipra_ring
    have left := (row_at (Γ := Δ) i one one).eqTrans (congrPairT ei (.eqRefl _))
    have r := GaussianHarmonicLogarithmName.name_regular (Γ := Δ) (succ i) one (.andI (zero_lt_succ _) (le_refl one))
    simpa only [i,Δ,Syn.shift,subst_pairT,GaussianLogGammaFactorialLogSum.harmonic_row,GaussianHarmonicLogarithmName.data,
      one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
      cross_data_congr H H _ _ _ _ left.eqSymm (.eqRefl _) (cross_refl _ _ r)
  exact cross_trans _ _ _ _ _ _ (family_sum_cross H H rowBody harmonicBody j (pairT one one) zero rows)
    (cross_symm _ _ _ _ (harmonic_factorial_cross j zero))

theorem at_integer (P : Presentation) (j : PTm n) (hp : Γ ⊢[PRAAx] laws P) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF H (argument P (succ j) one) (logData (fact j) one) := by
  let x : PTm n := argument P one one
  let y := sumData one one j
  have hs : Γ ⊢[PRAAx] source (one : PTm n) one := .andI (le_refl _) (le_refl _)
  have hV := hp.andE₂.andE₁
  have hx := (observe_value P one one hV hs).andE₁
  have hy := sum_regular one one j hs
  have old := GaussianBohrMollerupFiniteRecurrence.iterated_cross P one one j hV hp.andE₂.andE₂.andE₁ hs
  have e : Γ ⊢[PRAAx] argument P (one+one*j) one ≐ argument P (succ j) one :=
    argument_congr P _ _ _ _ (by ipra_ring) (.eqRefl _)
  have start := cross_data_congr P.nameF (addF P.nameF Sum) _ _ _ _ e (.eqRefl _) old
  have zeros := cross_trans P.nameF zeroF zeroF x zero y hp.andE₁
    (GaussianGammaRationalWendelBoundary.zero_data_cross zero y)
  have norm := add_cross P.nameF zeroF Sum Sum x y y y
    hx (zero_fast _) hy hy zeros (cross_refl _ _ hy)
  exact cross_trans _ _ _ _ _ _ start (cross_trans _ _ _ _ _ _ norm
    (cross_trans _ _ _ _ _ _ (add_zero_left Sum y hy) (integer_sum j)))

theorem at_scaled_integer (P : Presentation) (b j : PTm n) (hp : Γ ⊢[PRAAx] laws P)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF H (argument P (base b j) b) (logData (fact j) one) :=
  cross_trans _ _ _ _ _ _
    (rescale_from P (base b j) b (succ j) one b hp.andE₂.andE₂.andE₂.andE₁
      (.andI (zero_lt_succ _) (le_refl one)) hb (.eqRefl _) (by ipra_ring))
    (at_integer P j hp)

theorem actual_original_Bohr_Mollerup_factorial_values_closed (P : Presentation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (laws P ⟶ le one (var 0) ⟶
        crossEquivalent P.nameF H (argument P (base (var 0) (var 1)) (var 0)) (logData (fact (var 1)) one)) :=
  closeUniv 2 (.impI (.impI (at_scaled_integer P _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupFactorialNormalization
