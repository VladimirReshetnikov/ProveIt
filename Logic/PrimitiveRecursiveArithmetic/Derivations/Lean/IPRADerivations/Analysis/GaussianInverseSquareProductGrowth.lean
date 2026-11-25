import IPRADerivations.Analysis.GaussianInverseSquareProductTail
import IPRADerivations.Analysis.PowerIncrement
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Uniform growth for finite inverse-square products

For (k\ge2), the rational majorant (k^2/((k-1)(k+1)))
dominates (1+1/k^2). Its literal prefix product, including
(2) for (k=1), is (4j/(j+1)) for (j\ge1).
Integer Bernoulli then gives growth at most (2^{2C})
for any finite Gaussian product with factors within (C/k^2) of one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianInverseSquareProductGrowth

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianRationalFiniteProduct (qprod product_zero product_succ)
open GaussianRationalReciprocal (qone qone_bounded bounded_product bound_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianCoefficientNameBounds (unit bounded_radius_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def prefixNumerator (j : PTm n) : PTm n := num 4*j+monus one j
def prefixDenominator (j : PTm n) : PTm n := succ j
def rowDenominator (j : PTm n) : PTm n := j*succ (succ j)+monus one j
def rowNumerator (j : PTm n) : PTm n := succ (rowDenominator j)

@[simp] theorem subst_prefixNumerator {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (prefixNumerator j) = prefixNumerator (Syn.subst σ j) := by simp [prefixNumerator]
@[simp] theorem subst_prefixDenominator {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (prefixDenominator j) = prefixDenominator (Syn.subst σ j) := by simp [prefixDenominator]
@[simp] theorem subst_rowDenominator {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (rowDenominator j) = rowDenominator (Syn.subst σ j) := by simp [rowDenominator]
@[simp] theorem subst_rowNumerator {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (rowNumerator j) = rowNumerator (Syn.subst σ j) := by simp [rowNumerator]

theorem row_positive (j : PTm n) : Γ ⊢[PRAAx] le one (rowDenominator j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have e := natEq (Prf.hyp0 : (j ≐ zero) :: Γ ⊢[PRAAx] j ≐ zero)
    have m := natEq ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_zero one) :
      (j ≐ zero) :: Γ ⊢[PRAAx] monus one j ≐ one)
    have h : (j ≐ zero) :: Γ ⊢[PRAAx] rowDenominator j ≐ one := by
      unfold rowDenominator
      apply deriveNat
      ipra_simps
      rw [m,e]
      ring
    exact le_congr (.eqRefl _) h.eqSymm (le_refl one)
  · have hj : (j ≐ succ (pred j)) :: Γ ⊢[PRAAx] le one j :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have p := positive_product j (succ (succ j)) hj (zero_lt_succ _)
    exact le_trans p (le_add_right _ _)

private theorem row_below_square (j : PTm n) :
    Γ ⊢[PRAAx] le (rowDenominator j) (succ j*succ j) := by
  unfold rowDenominator
  ipra_le sl (GaussianMonicResidualRadius.monus_le_left one j)

theorem prefix_identity (j : PTm n) : Γ ⊢[PRAAx]
    prefixNumerator j*rowNumerator j*prefixDenominator (succ j) ≐
      prefixNumerator (succ j)*prefixDenominator j*rowDenominator j := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have e := natEq (Prf.hyp0 : (j ≐ zero) :: Γ ⊢[PRAAx] j ≐ zero)
    have m := natEq ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_zero one) :
      (j ≐ zero) :: Γ ⊢[PRAAx] monus one j ≐ one)
    have m' := natEq (zero_lt_succ (Γ := (j ≐ zero) :: Γ) j : (j ≐ zero) :: Γ ⊢[PRAAx] monus one (succ j) ≐ zero)
    unfold prefixNumerator prefixDenominator rowNumerator rowDenominator
    apply deriveNat
    ipra_simps
    rw [m,m',e]
    ring
  · have m := natEq (le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ (pred j)) :
      (j ≐ succ (pred j)) :: Γ ⊢[PRAAx] monus one j ≐ zero)
    have m' := natEq (zero_lt_succ (Γ := (j ≐ succ (pred j)) :: Γ) j :
      (j ≐ succ (pred j)) :: Γ ⊢[PRAAx] monus one (succ j) ≐ zero)
    unfold prefixNumerator prefixDenominator rowNumerator rowDenominator
    apply deriveNat
    ipra_simps
    rw [m,m']
    ring

private theorem bernoulli (A C : PTm n) :
    Γ ⊢[PRAAx] le ((A+C)*pw A C) (A*pw (succ A) C) := by
  refine .orE (zero_or_succ C) ?_ ?_
  · have u := natEq ((congrAp2 powF Prf.hyp0 (.eqRefl A)).eqTrans (pw_zero A) :
      (C ≐ zero) :: Γ ⊢[PRAAx] pw A C ≐ one)
    have v := natEq ((congrAp2 powF Prf.hyp0 (.eqRefl (succ A))).eqTrans (pw_zero (succ A)) :
      (C ≐ zero) :: Γ ⊢[PRAAx] pw (succ A) C ≐ one)
    have e := natEq (Prf.hyp0 : (C ≐ zero) :: Γ ⊢[PRAAx] C ≐ zero)
    exact le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps; rw [u,v,e]; ring)
  · let Δ := (C ≐ succ (pred C)) :: Γ
    have e := natEq (Prf.hyp0 : Δ ⊢[PRAAx] C ≐ succ (pred C))
    have u := natEq ((congrAp2 powF Prf.hyp0 (.eqRefl A)).eqTrans (pw_succ A (pred C)) :
      Δ ⊢[PRAAx] pw A C ≐ pw A (pred C)*A)
    have v := natEq ((congrAp2 powF Prf.hyp0 (succ_eq_add_one A)).eqTrans (.eqRefl _) :
      Δ ⊢[PRAAx] pw (succ A) C ≐ pw (A+one) (succ (pred C)))
    have a := natEq (pw_succ (Γ := Δ) A (pred C))
    exact le_congr (by apply deriveNat; ipra_simps; rw [a,u,e]; ring)
      (by apply deriveNat; ipra_simps; rw [v])
      (le_mul_mono (le_refl A) (PowerIncrement.power_inc_lower A one (pred C)))

theorem row_growth (C j : PTm n) : Γ ⊢[PRAAx]
    le ((succ j*succ j+C)*pw (rowDenominator j) C) ((succ j*succ j)*pw (rowNumerator j) C) := by
  let D := succ j*succ j
  let B := rowDenominator j
  let P := pw B C
  let Q := pw (rowNumerator j) C
  have hB : Γ ⊢[PRAAx] le one B := row_positive j
  have hBD : Γ ⊢[PRAAx] le B D := row_below_square j
  have h₁ : Γ ⊢[PRAAx] le ((B*(D+C))*P) ((D*(B+C))*P) := by
    ipra_le 𝔞 P*𝔞 C*sl hBD
  have h₂ : Γ ⊢[PRAAx] le (D*((B+C)*P)) (D*(B*Q)) :=
    le_mul_mono (le_refl D) (bernoulli B C)
  exact RationalValueBounds.positive_cancel hB
    (le_trans (le_congr (by dsimp only [D,P]; ipra_ring) (by ipra_ring) h₁)
      (le_congr (.eqRefl _) (by dsimp only [D,Q]; ipra_ring) h₂))

theorem row_bound (q C j : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded q qone C (succ j*succ j)) :
    Γ ⊢[PRAAx] bounded q (pw (rowNumerator j) C) (pw (rowDenominator j) C) := by
  let D := succ j*succ j
  have hD := positive_product (Γ := Γ) (succ j) (succ j) (zero_lt_succ _) (zero_lt_succ _)
  have near := norm_from_distance q qone C D one one hD (le_refl one) h qone_bounded
  have normalized : Γ ⊢[PRAAx] bounded q (D+C) D :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) near
  exact bounded_radius_mono _ _ _ _ _ hD
    (RationalNonnegativePowers.denominator_positive _ _ (row_positive j))
    (le_congr (.eqRefl _) (mul_comm _ _) (row_growth C j)) normalized

theorem prefix_power_identity (C j : PTm n) : Γ ⊢[PRAAx]
    (pw (prefixNumerator j) C*pw (rowNumerator j) C)*pw (prefixDenominator (succ j)) C ≐
    pw (prefixNumerator (succ j)) C*(pw (prefixDenominator j) C*pw (rowDenominator j) C) := by
  have e : Γ ⊢[PRAAx] prefixNumerator j*rowNumerator j*prefixDenominator (succ j) ≐
      prefixNumerator (succ j)*(prefixDenominator j*rowDenominator j) :=
    (prefix_identity j).eqTrans (mul_assoc _ _ _)
  exact ((pw_mul_base _ _ C).eqTrans (congrMul (pw_mul_base _ _ C) (.eqRefl _))).eqSymm.eqTrans
    ((congrAp2 powF (.eqRefl C) e).eqTrans ((pw_mul_base _ _ C).eqTrans (congrMul (.eqRefl _) (pw_mul_base _ _ C))))

theorem prefix_power_positive (C j : PTm n) : Γ ⊢[PRAAx] le one (pw (prefixDenominator j) C) :=
  RationalNonnegativePowers.denominator_positive _ _ (zero_lt_succ _)

theorem prefix_power_upper (C j : PTm n) : Γ ⊢[PRAAx]
    le (pw (prefixNumerator j) C) (unit (two*C)*pw (prefixDenominator j) C) := by
  have major : Γ ⊢[PRAAx] le (prefixNumerator j) (num 4*prefixDenominator j) := by
    unfold prefixNumerator prefixDenominator
    ipra_le 3+sl (GaussianMonicResidualRadius.monus_le_left one j)
  have u : Γ ⊢[PRAAx] pw (num 4) C ≐ unit (two*C) :=
    (congrAp2 powF (.eqRefl C) (by ipra_ring : Γ ⊢[PRAAx] num 4 ≐ two*two)).eqTrans
      (GaussianBalancedRadiusArithmetic.unit_four_power C).eqSymm
  exact le_congr (.eqRefl _) ((pw_mul_base _ _ C).eqTrans (congrMul u (.eqRefl _))) (pw_le_pw C major)

private def prefixBound (f : PTm 2) (x C j : PTm n) : Fm PTm n :=
  bounded (qprod f j x) (pw (prefixNumerator j) C) (pw (prefixDenominator j) C)

@[simp] private theorem subst_prefixBound {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x C j : PTm n) :
    (prefixBound f x C j).subst σ = prefixBound f (Syn.subst σ x) (Syn.subst σ C) (Syn.subst σ j) :=
  by simp [prefixBound]

private theorem prefix_zero (f : PTm 2) (x C : PTm n) : Γ ⊢[PRAAx] prefixBound f x C zero := by
  have e : Γ ⊢[PRAAx] prefixNumerator (zero : PTm n) ≐ one :=
    (congrAdd (.eqRefl (num 4*zero)) (monus_zero one)).eqTrans (by ipra_ring)
  have p := (congrAp2 powF (.eqRefl C) e).eqTrans (pw_one_base C)
  exact bound_congr (product_zero _ _).eqSymm p.eqSymm (pw_one_base C).eqSymm qone_bounded

private theorem prefix_succ (f : PTm 2) (x C j : PTm n)
    (h : Γ ⊢[PRAAx] prefixBound f x C j)
    (hj : Γ ⊢[PRAAx] distanceBounded (inst2 f j x) qone C (succ j*succ j)) :
    Γ ⊢[PRAAx] prefixBound f x C (succ j) := by
  have hP := prefix_power_positive (Γ := Γ) C j
  have hD := RationalNonnegativePowers.denominator_positive _ C (row_positive (Γ := Γ) j)
  have product := bounded_product _ _ _ _ _ _ hP hD h (row_bound _ _ _ hj)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hP hD) (prefix_power_positive C (succ j))
    (le_of_eq_add (d := zero) ((prefix_power_identity C j).eqSymm.eqTrans (add_zero _).eqSymm))
    (bound_congr (product_succ f j x).eqSymm (.eqRefl _) (.eqRefl _) product)

theorem prefix_bound (f : PTm 2) (x C j : PTm n)
    (h : Γ ⊢[PRAAx] GaussianInverseSquareProductTail.factorBounds f x C zero) :
    Γ ⊢[PRAAx] prefixBound f x C j := by
  have h' : Γ.map Fm.shift ⊢[PRAAx]
      GaussianInverseSquareProductTail.factorBounds f (Syn.shift x) (Syn.shift C) zero := by
    simpa only [Fm.shift, Syn.shift, GaussianInverseSquareProductTail.subst_factorBounds,
      ConciseIPRA.PTm.subst_zero] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixBound f (Syn.shift x) (Syn.shift C) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero f x C
    · let Δ := prefixBound f (Syn.shift x) (Syn.shift C) (var 0) :: Γ.map Fm.shift
      have gap := GaussianInverseSquareProductTail.factor_bound_at (Γ := Δ)
        f (Syn.shift x) (Syn.shift C) zero (var 0) h'.wk
      have e : Δ ⊢[PRAAx] zero+var 0 ≐ var 0 := zero_add _
      have cell := GaussianRationalDistanceOrder.distance_congr
        (congrInst2 f e (.eqRefl _)) (.eqRefl _) (.eqRefl _)
        (congrMul (congrSucc e) (congrSucc e)) gap
      simpa only [subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_succ f (Syn.shift x) (Syn.shift C) (var 0) Prf.hyp0 cell
  simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem uniform_bound (f : PTm 2) (x C j : PTm n)
    (h : Γ ⊢[PRAAx] GaussianInverseSquareProductTail.factorBounds f x C zero) :
    Γ ⊢[PRAAx] bounded (qprod f j x) (unit (two*C)) one :=
  bounded_radius_mono _ _ _ _ _ (prefix_power_positive _ _) (le_refl one)
    (le_congr ((mul_comm _ _).eqTrans (one_mul _)).eqSymm (.eqRefl _) (prefix_power_upper C j))
    (prefix_bound f x C j h)

theorem actual_inverse_square_product_growth_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianInverseSquareProductTail.factorBounds f (var 2) (var 1) zero ⟶
      bounded (qprod f (var 0) (var 2)) (unit (two*var 1)) one) :=
  closeUniv 3 (.impI (uniform_bound f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianInverseSquareProductGrowth
