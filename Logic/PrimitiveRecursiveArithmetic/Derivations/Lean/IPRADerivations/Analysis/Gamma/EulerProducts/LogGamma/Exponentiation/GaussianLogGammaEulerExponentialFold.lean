import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Exponentiation.GaussianLogGammaEulerExponentialFactors
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# Exponential of the original finite residual logarithm sum

Appending one logarithm supplies the original exponential addition law.
At a fixed precision the finite error then satisfies a quantifier-free
recurrence, using the exact Euler factor and its numerical disk bound.
The named limit of that observation error identifies the exponential of
the sum with the original numerical Euler product.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFold

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianLogGammaEulerFactorSum (residualBody residualF residual_rows)
open GaussianLogGammaEulerHead (rowData)
open GaussianLogGammaEulerResidualDomain (source native)
open GaussianLogGammaEulerExponentialFactors (rowExpF rowExpBody)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_at)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalSyntheticDivision (qone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "sd" => GaussianNamedFiniteSumFamily.data

def prefixF : PR 2 := E residualF
def prefixData (i x : PTm n) : PTm n := exponentialInputData residualF (sd i x)
def localCost (i x : PTm n) : PTm n :=
  multiplyModulus prefixF rowExpF (prefixData i x) (inst2 rowExpBody i x)+num 3+two*U prefixF (prefixData i x)
def budgetStep : PTm 3 := var 1*(one+fstT (var 2))+localCost (var 0) (sndT (var 2))
def budgetF : PR 2 := rec2 (zero : PTm 1) budgetStep
def budget (R i x : PTm n) : PTm n := ap2 budgetF i (pairT R x)

@[simp] theorem subst_prefixData {m : ℕ} (σ : Fin n → PTm m) (i x : PTm n) :
    Syn.subst σ (prefixData i x) = prefixData (Syn.subst σ i) (Syn.subst σ x) := by
  simp [prefixData,exponentialInputData]

@[simp] private theorem subst_localCost {m : ℕ} (σ : Fin n → PTm m) (i x : PTm n) :
    Syn.subst σ (localCost i x) = localCost (Syn.subst σ i) (Syn.subst σ x) := by
  simp [localCost,two,one]

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (R i x : PTm n) :
    Syn.subst σ (budget R i x) = budget (Syn.subst σ R) (Syn.subst σ i) (Syn.subst σ x) := by
  simp [budget]

private theorem local_cost_congr {i x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] localCost i x ≐ localCost i y := by
  simpa only [subst_localCost,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (Prf.eqCongr (localCost (var 0) (var 1) : PTm 2) (σ := ![i,x]) (σ' := ![i,y])
      (fun j => by fin_cases j; exact .eqRefl _; exact e))

private theorem budget_zero (R x : PTm n) : Γ ⊢[PRAAx] budget R zero x ≐ zero := by
  simpa only [budget,budgetF,ConciseIPRA.PTm.subst_zero] using
    (rec2_zero (Γ := Γ) (zero : PTm 1) budgetStep (pairT R x))

private theorem budget_succ (R i x : PTm n) : Γ ⊢[PRAAx]
    budget R (succ i) x ≐ budget R i x*(one+R)+localCost i x := by
  have raw := rec2_succ (Γ := Γ) (zero : PTm 1) budgetStep i (pairT R x)
  have e : Γ ⊢[PRAAx] budget R i x*(one+fstT (pairT R x))+localCost i (sndT (pairT R x)) ≐
      budget R i x*(one+R)+localCost i x :=
    congrAdd (congrMul (.eqRefl _) (congrAdd (.eqRefl _) (fst_pair R x))) (local_cost_congr (snd_pair R x))
  exact (by simpa [budget,budgetF,budgetStep,inst3,one] using raw :
    Γ ⊢[PRAAx] budget R (succ i) x ≐ budget R i x*(one+fstT (pairT R x))+localCost i (sndT (pairT R x))).eqTrans e

def foldError (p A B D neg R i : PTm n) : Fm PTm n :=
  distanceBounded (ap2 prefixF p (prefixData i (rowData A B D neg)))
    (GaussianGammaEulerHead.product (native A B neg) D i) (budget R i (rowData A B D neg)) (unit p)

@[simp] theorem subst_foldError {m : ℕ} (σ : Fin n → PTm m) (p A B D neg R i : PTm n) :
    (foldError p A B D neg R i).subst σ =
      foldError (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg)
        (Syn.subst σ R) (Syn.subst σ i) := by
  simp [foldError]

private theorem prefix_zero_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 prefixF p (prefixData zero x) ≐ qone := by
  let t := sd zero x
  let R := U residualF t
  let k := GaussianRadiusExponentialName.inputPrecision R p
  have sum := (GaussianNamedFiniteSumFamily.sample_at (Γ := Γ) L residualBody k zero x).eqTrans
    (GaussianRationalFiniteSum.sum_zero _ _)
  exact (GaussianRadiusExponentialName.sample_at residualF R p t).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl _) sum).eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

private theorem fold_zero (p A B D neg R : PTm n) : Γ ⊢[PRAAx] foldError p A B D neg R zero :=
  distance_congr (prefix_zero_at p (rowData A B D neg)).eqSymm
    (GaussianRationalFiniteProduct.product_zero _ (GaussianGammaEulerHead.data (native A B neg) D)).eqSymm
    (budget_zero R (rowData A B D neg)).eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qone (unit p) (unit_positive p))

private theorem at_same (f g : PR 2) (x y p : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) two (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at f g x y p p h)

theorem prefix_regular (A B D neg i : PTm n) (hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] pointCN prefixF (prefixData i (rowData A B D neg)) := by
  have h := GaussianNamedFiniteSumFamily.regular _ _ _ _ (residual_rows A B D neg i hs)
  exact GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ h)

private theorem fold_succ (p A B D neg R i : PTm n) (hs : Γ ⊢[PRAAx] source A B D neg R)
    (ih : Γ ⊢[PRAAx] foldError p A B D neg R i) : Γ ⊢[PRAAx] foldError p A B D neg R (succ i) := by
  let x := rowData A B D neg
  let z := native A B neg
  let a := prefixData i x
  let b := inst2 rowExpBody i x
  let c := prefixData (succ i) x
  let d := multiplyData prefixF rowExpF a b
  let t := inst2 residualBody i x
  let s := GaussianGammaEulerHead.product z D i
  let v := GaussianGammaEulerHead.factor i z D
  let e := ap2 prefixF p a
  let w := ap2 rowExpF p b
  let P := unit p
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have premise := residual_rows A B D neg (succ i) hs.andE₁
  have append := GaussianNamedFiniteSumFamilySplit.append_cross L residualBody i x premise
  have hr := GaussianNamedFiniteProductFamily.regular_at L residualBody (succ i) x i premise (le_refl _)
  have hi := GaussianNamedFiniteSumFamily.regular _ _ _ _ (residual_rows A B D neg i hs.andE₁)
  have hj := GaussianNamedFiniteSumFamily.regular _ _ _ _ premise
  have hI := exponential_input residualF (sd i x) hi
  have hR := exponential_input L t hr
  have hJ := exponential_input residualF (sd (succ i) x) hj
  have readBody : b = exponentialInputData L t := by
    simp only [b,t,rowExpBody,inst2,exponentialInputData,GaussianRadiusExponentialName.subst_data,GaussianNameBounds.subst_U]
  have hE := prefix_regular A B D neg i hs.andE₁
  have hW : Γ ⊢[PRAAx] pointCN rowExpF b := by
    rw [readBody]
    exact GaussianRadiusExponentialName.name_regular _ _ _ hR
  have expAppend : Γ ⊢[PRAAx] crossEquivalent (multiplyF prefixF rowExpF) prefixF d c := by
    dsimp only [d]
    rw [readBody]
    exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent _ _ _ _ _ _ _ _ _
      hI hR hJ (cross_symm _ _ _ _ append)
  have first := at_same _ _ _ _ p (cross_symm _ _ _ _ expAppend)
  have second := multiply_sample_error prefixF rowExpF a b p hE hW
  have row : Γ ⊢[PRAAx] distanceBounded w v two P :=
    distance_congr (.eqRefl _) (constant_at p v) (.eqRefl _) (.eqRefl _)
      (at_same rowExpF constantF b v p (GaussianLogGammaEulerExponentialFactors.row_recovery i A B D neg hs.andE₁))
  have boundV := GaussianGammaEulerHead.factor_bound i z R D hs.andE₁.andE₂ hs.andE₂
  have boundE := GaussianNameBounds.sample_bound prefixF a p hE
  have prev : Γ ⊢[PRAAx] distanceBounded e s (budget R i x) P := ih
  have core := GaussianNameArithmetic.product_distance s e v w (budget R i x) two P (one+R) (U prefixF a)
    hp (distance_symmetric _ _ _ _ hp prev) (distance_symmetric _ _ _ _ hp row) boundV boundE
  have step := distance_triangle_same _ _ _ _ _ _ hp
    (distance_triangle_same _ _ _ _ _ _ hp first second) (distance_symmetric _ _ _ _ hp core)
  have gain : Γ ⊢[PRAAx]
      two+(multiplyModulus prefixF rowExpF a b+one)+(budget R i x*(one+R)+U prefixF a*two) ≐
      budget R i x*(one+R)+localCost i x := by
    dsimp only [localCost,a,b]
    ipra_ring
  exact distance_congr (.eqRefl _) (GaussianGammaEulerHead.product_step z D i).eqSymm
    (gain.eqTrans (budget_succ R i x).eqSymm) (.eqRefl _) step

/-- A numerical induction at a fixed precision gives the finite fold
error. The induction formula is the quantifier-free distance test. -/
theorem fold_error (p A B D neg R i : PTm n) (hs : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] foldError p A B D neg R i := by
  let sh (t : PTm n) := Syn.shift t
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh R) := by
    simpa only [Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,sh] using hs.shift
  have induction : Γ ⊢[PRAAx] .all (foldError (sh p) (sh A) (sh B) (sh D) (sh neg) (sh R) (var 0)) := by
    refine PRA.qfInd _ (by unfold foldError distanceBounded bounded RationalArgmin.rationalLE; exact le_QF _ _) ?_ ?_
    · simpa only [sh,subst_foldError,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using fold_zero p A B D neg R
    · simp only [sh,subst_foldError,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact fold_succ _ _ _ _ _ _ _ hs'.wk Prf.hyp0
  simpa only [sh,subst_foldError,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using induction.allE i

theorem exponential_product (A B D neg R i : PTm n) (hs : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] crossEquivalent prefixF constantF (prefixData i (rowData A B D neg))
      (GaussianGammaEulerHead.product (native A B neg) D i) := by
  let x := rowData A B D neg
  let q := GaussianGammaEulerHead.product (native A B neg) D i
  refine cross_of_diagonal_rate _ _ _ _ (budget R i x) (prefix_regular A B D neg i hs.andE₁)
    (constant_regular q) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh R) := by
    simpa only [Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,sh] using hs.shift
  have raw := fold_error (var 0) (sh A) (sh B) (sh D) (sh neg) (sh R) (sh i) hs'
  have read := constant_at (Γ := Γ.map Fm.shift) (var 0)
    (GaussianGammaEulerHead.product (native (sh A) (sh B) (sh neg)) (sh D) (sh i))
  simpa only [diagonalRate,Syn.shift,subst_prefixData,GaussianLogGammaEulerHead.subst_rowData,
    GaussianGammaEulerHead.subst_product,GaussianLogGammaEulerResidualDomain.subst_native,subst_budget,sh,x,q]
    using distance_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl _) raw

theorem actual_canonical_Euler_residual_exponential_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        crossEquivalent prefixF constantF (prefixData (var 5) (rowData (var 0) (var 1) (var 2) (var 3)))
          (GaussianGammaEulerHead.product (native (var 0) (var 1) (var 3)) (var 2) (var 5))) :=
  closeUniv 6 (.impI (exponential_product _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFold
