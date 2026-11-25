import IPRADerivations.Analysis.GaussianArctangentPartialQuadrature
import IPRADerivations.Analysis.GaussianArctangentRationalTarget

/-!
# Clipping a nonnegative finite arctangent target

The finite inverse uses the original crossing in range and returns the
right endpoint for a target above the largest grid value. Extending the
factorial clearing denominator preserves every original prefix value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentClampedTarget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentExponentialPrefix (source total prefixValue subst_prefixValue)
open GaussianArctangentGridSearch (crossing_spec)
open GaussianArctangentRationalTarget (chosen target target_admitted targetPoint rational_target_distance)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open RationalArithmetic (select select_zero select_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_le sg_lt)
open LeanProofs.IPRA.Signum (sg)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def upper (Q D M L : PTm n) : Fm PTm n := le (Q*fact L) ((two*D)*total M M L)
def above (Q D M L : PTm n) : Fm PTm n := lt ((two*D)*total M M L) (Q*fact L)
def clamped (Q D M L : PTm n) : PTm n :=
  select (sg (monus (Q*fact L) ((two*D)*total M M L))) (chosen Q D M L) M

theorem in_range (Q D M L : PTm n) (h : Γ ⊢[PRAAx] upper Q D M L) :
    Γ ⊢[PRAAx] clamped Q D M L ≐ chosen Q D M L :=
  select_zero _ _ _ (sg_le h)

theorem above_range (Q D M L : PTm n) (h : Γ ⊢[PRAAx] above Q D M L) :
    Γ ⊢[PRAAx] clamped Q D M L ≐ M :=
  select_one _ _ _ (sg_lt h)

theorem cutoff_independent (j M L K : PTm n)
    (hL : Γ ⊢[PRAAx] source M L) (hK : Γ ⊢[PRAAx] source M K) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] prefixValue j M L ≐ prefixValue j M K :=
  (GaussianArctangentPartialQuadrature.prefix_as_sum j M L hL hj).eqTrans
    (GaussianArctangentPartialQuadrature.prefix_as_sum j M K hK hj).eqSymm

theorem clamped_le (Q D M L : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le (two*D) L) :
    Γ ⊢[PRAAx] le (clamped Q D M L) M := by
  refine .orE (lt_or_le ((two*D)*total M M L) (Q*fact L)) ?_ ?_
  · exact le_congr (above_range Q D M L Prf.hyp0).eqSymm (.eqRefl _) (le_refl _)
  · have admissible := target_admitted (Γ := upper Q D M L :: Γ) Q D M L hD.wk hL.wk Prf.hyp0
    exact le_congr (in_range Q D M L Prf.hyp0).eqSymm (.eqRefl _)
      (crossing_spec M (target Q D L) M L admissible).andE₁

theorem zero_index (D M L : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le (two*D) L) :
    Γ ⊢[PRAAx] clamped zero D M L ≐ zero := by
  have range : Γ ⊢[PRAAx] upper zero D M L :=
    le_congr (zero_mul (fact L)).eqSymm (.eqRefl _) (zero_le _)
  have ht : Γ ⊢[PRAAx] target zero D L ≐ zero := zero_mul _
  have chosenLe : Γ ⊢[PRAAx] le (chosen zero D M L) zero := by
    have h := crossing_spec zero (target zero D L) M L (target_admitted zero D M L hD hL range)
    refine .orE (lt_or_le zero (chosen zero D M L)) ?_ Prf.hyp0
    exact lt_zero_absurd _ (lt_congr (.eqRefl _) ht.wk (.impE h.andE₂.andE₂.wk Prf.hyp0))
  exact (in_range zero D M L range).eqTrans (le_antisymm chosenLe (zero_le _))

private theorem prefix_congr {j k : PTm n} (M L : PTm n) (h : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] prefixValue j M L ≐ prefixValue k M L := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (prefixValue (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![j,M,L]) (σ' := ![k,M,L]) (fun i => by fin_cases i; exact h; exact .eqRefl _; exact .eqRefl _)
  simpa only [subst_prefixValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using e

def nativeValue (j M : PTm n) : PTm n := prefixValue j M (two*(M*M))

def clampedSpec (Q D M L : PTm n) : Fm PTm n :=
  le (clamped Q D M L) M ⋏
    ((upper Q D M L ⟶ distanceBounded (nativeValue (clamped Q D M L) M) (targetPoint Q D) two M) ⋏
      (above Q D M L ⟶ nativeValue (clamped Q D M L) M ≐ nativeValue M M))

theorem native_clamped (Q D M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le (two*D) L) :
    Γ ⊢[PRAAx] clampedSpec Q D M L := by
  let j := clamped Q D M L
  let K := two*(M*M)
  have hj : Γ ⊢[PRAAx] le j M := clamped_le Q D M L hD hL
  have hK : Γ ⊢[PRAAx] source M K := .andI hs.andE₁ (le_refl K)
  have e : Γ ⊢[PRAAx] nativeValue j M ≐ prefixValue j M L := cutoff_independent j M K L hK hs hj
  refine .andI hj (.andI (.impI ?_) (.impI ?_))
  · have q : upper Q D M L :: Γ ⊢[PRAAx] j ≐ chosen Q D M L := in_range Q D M L Prf.hyp0
    exact distance_congr ((prefix_congr M L q.eqSymm).eqTrans e.wk.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (rational_target_distance Q D M L hs.wk hD.wk hL.wk Prf.hyp0)
  · exact prefix_congr M K (above_range Q D M L Prf.hyp0)

theorem actual_native_arctangent_clamped_target_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 2) (var 3) ⟶ le one (var 1) ⟶ le (two*var 1) (var 3) ⟶ clampedSpec (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (native_clamped _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_arctangent_clamped_zero_target_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le (two*var 0) (var 2) ⟶ clamped zero (var 0) (var 1) (var 2) ≐ zero) :=
  closeUniv 3 (.impI (.impI (zero_index _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentClampedTarget
