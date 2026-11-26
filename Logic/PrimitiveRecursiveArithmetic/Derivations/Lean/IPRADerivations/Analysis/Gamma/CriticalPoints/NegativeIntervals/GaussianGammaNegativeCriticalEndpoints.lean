import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalCorrection
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaCriticalSigns

/-!
# Uniform reciprocal endpoint margins on the negative Gamma intervals

For (x=-N-1+a/b), take (b=4(N+2)) and use the two endpoints
(a=1) and (a=b-1). The computed reciprocal correction is at most
(-2(N+3)) on the first endpoint and at least (b-2) on the second.
The regular shifted digamma name adds this exact rational correction
to the original positive digamma at ((b+a)/b).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalEndpoints

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalCorrection
  (guard row bottomDen correction positiveSum prefix_upper first_lower)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (qnegative qsub)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def mesh (N : PTm n) : PTm n := num 4*succ (succ N)
def rightNumerator (N : PTm n) : PTm n := monus (mesh N) one
def leftCap (N : PTm n) : PTm n := qnegative (fraction (two*succ (succ (succ N))) one)
def rightFloor (N : PTm n) : PTm n := fraction (monus (mesh N) two) one

def nameF : PR 2 := addF DF constantF
def nameData (a b N : PTm n) : PTm n := addData (dd (b+a) b) (correction a b N)

ipra_subst mesh
ipra_subst rightNumerator
ipra_subst nameData

theorem shifted_source (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (b+a) b := by
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  exact .andI (le_trans hb (le_add_right _ _)) hb

theorem name_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN nameF (nameData a b N) :=
  add_fast _ _ _ _ (GaussianGammaDigammaNative.name_regular _ _ (shifted_source a b h)) (constant_regular _)

theorem mesh_minimum (N : PTm n) : Γ ⊢[PRAAx] le (num 8) (mesh N) := by
  unfold mesh
  ipra_le 4*𝔞(N)

theorem left_guard (N : PTm n) : Γ ⊢[PRAAx] guard one (mesh N) :=
  .andI (le_refl _) (le_trans (by ipra_le 6) (mesh_minimum N))

theorem right_add (N : PTm n) : Γ ⊢[PRAAx] mesh N ≐ one+rightNumerator N :=
  eq_add_of_le (le_trans (by ipra_le 7) (mesh_minimum N))

theorem right_guard (N : PTm n) : Γ ⊢[PRAAx] guard (rightNumerator N) (mesh N) := by
  have e := natEq (right_add (Γ := Γ) N)
  exact .andI
    (by ipra_le sl (mesh_minimum N)+6 with -e)
    (le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps; linear_combination e))

private theorem negate_congr {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] qnegative x ≐ qnegative y := by
  simpa only [GaussianRationalMetric.subst_qnegative,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (qnegative (var 0) : PTm 1) (σ := ![x]) (σ' := ![y]) (fun j => by fin_cases j; exact e)

theorem left_correction_upper (N : PTm n) :
    Γ ⊢[PRAAx] rationalLE (fstT (correction one (mesh N) N)) (fstT (leftCap N)) := by
  let B := mesh N
  let H := two*succ N
  have h := (left_guard (Γ := Γ) N).andE₂
  have e := natEq (eq_add_of_le (le_of_lt h))
  have cap : Γ ⊢[PRAAx] le B (two*monus B one) :=
    by ipra_le sl (mesh_minimum N)+6 with -2*e
  have upper := prefix_upper one B two (succ N) h cap
  have diff := point_add_order (positiveSum one B (succ N)) (fraction H one)
    (qnegative (fraction B one)) (qnegative (fraction B one)) upper (point_order_refl _)
  have hg : Γ ⊢[PRAAx] le H B := by dsimp only [H,B,mesh]; ipra_le 2*𝔞(N)+6
  have gap : Γ ⊢[PRAAx] monus B H ≐ two*succ (succ (succ N)) := by
    have he := natEq (eq_add_of_le hg)
    apply deriveNat
    dsimp only [H,B,mesh] at he ⊢
    ipra_simps
    linear_combination -he
  have endpoint := (GaussianRationalDistanceOrder.reversed_difference (fraction B one) (fraction H one)).eqSymm.eqTrans
    (negate_congr ((GaussianEulerPositivePowerChartImageWeights.fraction_difference H B one (le_refl _) hg).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ gap (.eqRefl _))))
  exact rationalLE_congr (.eqRefl _) (congrFst endpoint) diff

theorem right_correction_lower (N : PTm n) :
    Γ ⊢[PRAAx] rationalLE (fstT (rightFloor N)) (fstT (correction (rightNumerator N) (mesh N) N)) := by
  let B := mesh N
  let A := rightNumerator N
  have h := right_guard (Γ := Γ) N
  have eq : Γ ⊢[PRAAx] bottomDen A B zero ≐ one :=
    (congrMonus ((one_mul B).eqTrans (right_add N)) (.eqRefl _)).eqTrans (add_monus _ _)
  have first := rationalLE_congr
    (congrFst (GaussianCompactRiemannName.fraction_congr B B (bottomDen A B zero) one (.eqRefl _) eq)) (.eqRefl _)
    (first_lower A B N h.andE₂)
  have e := natEq (right_add (Γ := Γ) N)
  have div : Γ ⊢[PRAAx] le B (two*A) := by
    ipra_le sl (mesh_minimum N)+6 with -2*e
  have small := fractions_order B A two one h.andE₁ (le_refl one)
    (le_congr (one_mul B).eqSymm (.eqRefl _) div)
  have reversed : Γ ⊢[PRAAx]
      rationalLE (fstT (qnegative (fraction two one))) (fstT (qnegative (fraction B A))) :=
    rationalLE_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (RationalAlgebra.negative_antitone _ _ small)
  have diff := point_add_order (fraction B one) (positiveSum A B (succ N))
    (qnegative (fraction two one)) (qnegative (fraction B A)) first reversed
  have eqFloor := GaussianEulerPositivePowerChartImageWeights.fraction_difference (Γ := Γ) two B one (le_refl one)
    (le_trans (by ipra_le 6) (mesh_minimum N))
  exact rationalLE_congr (congrFst eqFloor) (.eqRefl _) diff

theorem original_negative_interval_reciprocal_endpoint_brackets_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (rationalLE (fstT (correction one (mesh (var 0)) (var 0))) (fstT (leftCap (var 0))) ⋏
        rationalLE (fstT (rightFloor (var 0))) (fstT (correction (rightNumerator (var 0)) (mesh (var 0)) (var 0)))) :=
  closeUniv 1 (.andI (left_correction_upper _) (right_correction_lower _))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalEndpoints
