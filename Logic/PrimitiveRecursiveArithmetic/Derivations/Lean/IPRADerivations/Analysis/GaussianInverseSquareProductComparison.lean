import IPRADerivations.Analysis.GaussianInverseSquareProductGrowth

/-!
# Weighted comparison of two inverse-square products

The actual finite products are compared at matching row indices. At
each prefix, the same multiplicative majorant controls the two
products. Errors of size (E(H/k^2+1)/M) accumulate to at most
(E(2H+j)/M) before the common growth factor.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianInverseSquareProductComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianInverseSquareProductGrowth (prefixNumerator prefixDenominator rowNumerator rowDenominator
  row_bound row_positive prefix_bound prefix_power_identity prefix_power_positive prefix_power_upper)
open GaussianInverseSquareProductTail (factorBounds factor_bound_at)
open GaussianRationalFiniteProduct (qprod product_zero product_succ)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianCoefficientNameBounds (unit)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def rowErrorNumerator (E H j : PTm n) : PTm n := E*(H+succ j*succ j)
def rowErrorDenominator (M j : PTm n) : PTm n := M*(succ j*succ j)
def errorNumerator (E H j : PTm n) : PTm n := E*(two*H*j+j*succ j)
def errorDenominator (M j : PTm n) : PTm n := M*succ j

@[simp] theorem subst_rowErrorNumerator {m : ℕ} (σ : Fin n → PTm m) (E H j : PTm n) :
    Syn.subst σ (rowErrorNumerator E H j) = rowErrorNumerator (Syn.subst σ E) (Syn.subst σ H) (Syn.subst σ j) := by
  simp [rowErrorNumerator]
@[simp] theorem subst_rowErrorDenominator {m : ℕ} (σ : Fin n → PTm m) (M j : PTm n) :
    Syn.subst σ (rowErrorDenominator M j) = rowErrorDenominator (Syn.subst σ M) (Syn.subst σ j) := by
  simp [rowErrorDenominator]
@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (E H j : PTm n) :
    Syn.subst σ (errorNumerator E H j) = errorNumerator (Syn.subst σ E) (Syn.subst σ H) (Syn.subst σ j) := by
  simp [errorNumerator]
@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (M j : PTm n) :
    Syn.subst σ (errorDenominator M j) = errorDenominator (Syn.subst σ M) (Syn.subst σ j) := by
  simp [errorDenominator]

def rowErrors (f g : PTm 2) (x y E H M K : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift K) ⟶
    distanceBounded (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y))
      (rowErrorNumerator (Syn.shift E) (Syn.shift H) (var 0)) (rowErrorDenominator (Syn.shift M) (var 0)))

@[simp] theorem subst_rowErrors {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (x y E H M K : PTm n) :
    (rowErrors f g x y E H M K).subst σ = rowErrors f g (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ E) (Syn.subst σ H) (Syn.subst σ M) (Syn.subst σ K) := by
  simp [rowErrors,Syn.subst_shift,Syn.shift_subst]

theorem row_error_at (f g : PTm 2) (x y E H M K j : PTm n)
    (h : Γ ⊢[PRAAx] rowErrors f g x y E H M K) (hj : Γ ⊢[PRAAx] lt j K) :
    Γ ⊢[PRAAx] distanceBounded (inst2 f j x) (inst2 g j y) (rowErrorNumerator E H j) (rowErrorDenominator M j) := by
  have e : Γ ⊢[PRAAx] lt j K ⟶
      distanceBounded (inst2 f j x) (inst2 g j y) (rowErrorNumerator E H j) (rowErrorDenominator M j) := by
    simpa only [rowErrors,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_distanceBounded,subst_inst2,
      subst_rowErrorNumerator,subst_rowErrorDenominator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using h.allE j
  exact .impE e hj

private theorem add_row_error (E H M j : PTm n) : Γ ⊢[PRAAx]
    le ((errorNumerator E H j*rowErrorDenominator M j+rowErrorNumerator E H j*errorDenominator M j)*
          errorDenominator M (succ j))
      (errorNumerator E H (succ j)*(errorDenominator M j*rowErrorDenominator M j)) := by
  unfold errorNumerator errorDenominator rowErrorNumerator rowErrorDenominator
  ipra_le 𝔞 E*𝔞 M*𝔞 M*𝔞 H*𝔞 j*(𝔞 j+1)

private theorem multiply_distance (c a b U V A B : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] bounded c U V) (hab : Γ ⊢[PRAAx] distanceBounded a b A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul c a) (qmul c b) (U*A) (V*B) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference c a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hV hB hc hab)

def prefixDistance (f g : PTm 2) (x y C E H M j : PTm n) : Fm PTm n :=
  distanceBounded (qprod f j x) (qprod g j y) (pw (prefixNumerator j) C*errorNumerator E H j)
    (pw (prefixDenominator j) C*errorDenominator M j)

@[simp] theorem subst_prefixDistance {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (x y C E H M j : PTm n) :
    (prefixDistance f g x y C E H M j).subst σ =
      prefixDistance f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ C) (Syn.subst σ E)
        (Syn.subst σ H) (Syn.subst σ M) (Syn.subst σ j) := by simp [prefixDistance]

private theorem prefix_zero (f g : PTm 2) (x y C E H M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] prefixDistance f g x y C E H M zero := by
  unfold prefixDistance
  have hD := positive_product _ _ (prefix_power_positive C zero) (positive_product _ _ hM (le_refl one))
  exact distance_congr (product_zero f x).eqSymm (product_zero g y).eqSymm
    (by unfold errorNumerator; ipra_ring) (.eqRefl _)
    (distance_refl_zero _ _ hD)

private theorem prefix_succ (f g : PTm 2) (x y C E H M j : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hf : Γ ⊢[PRAAx] factorBounds f x C zero)
    (hg : Γ ⊢[PRAAx] factorBounds g y C zero)
    (h : Γ ⊢[PRAAx] prefixDistance f g x y C E H M j)
    (hrow : Γ ⊢[PRAAx] distanceBounded (inst2 f j x) (inst2 g j y)
      (rowErrorNumerator E H j) (rowErrorDenominator M j)) :
    Γ ⊢[PRAAx] prefixDistance f g x y C E H M (succ j) := by
  let P := qprod f j x
  let Q := qprod g j y
  let a := inst2 f j x
  let b := inst2 g j y
  let U := pw (prefixNumerator j) C
  let V := pw (prefixDenominator j) C
  let W := pw (rowNumerator j) C
  let L := pw (rowDenominator j) C
  let A := errorNumerator E H j
  let B := errorDenominator M j
  let N := rowErrorNumerator E H j
  let D := rowErrorDenominator M j
  let X := (V*L)*(B*D)
  let U' := pw (prefixNumerator (succ j)) C
  let V' := pw (prefixDenominator (succ j)) C
  let A' := errorNumerator E H (succ j)
  let B' := errorDenominator M (succ j)
  have hV : Γ ⊢[PRAAx] le one V := prefix_power_positive C j
  have hL : Γ ⊢[PRAAx] le one L := RationalNonnegativePowers.denominator_positive _ _ (row_positive j)
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hM (zero_lt_succ _)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hM (positive_product _ _ (zero_lt_succ _) (zero_lt_succ _))
  have hX : Γ ⊢[PRAAx] le one X :=
    positive_product _ _ (positive_product _ _ hV hL) (positive_product _ _ hB hD)
  have heal := factor_bound_at f x C zero j hf
  have e : Γ ⊢[PRAAx] zero+j ≐ j := zero_add _
  have near := distance_congr (congrInst2 f e (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (congrMul (congrSucc e) (congrSucc e)) heal
  have hfa : Γ ⊢[PRAAx] bounded a W L := row_bound a C j near
  have hq : Γ ⊢[PRAAx] bounded Q U V := prefix_bound g y C j hg
  have leftRaw : Γ ⊢[PRAAx] distanceBounded (qmul P a) (qmul Q a) (W*(U*A)) (L*(V*B)) :=
    distance_congr (qmul_commutative a P) (qmul_commutative a Q) (.eqRefl _) (.eqRefl _)
      (multiply_distance a P Q W L (U*A) (V*B) hL (positive_product _ _ hV hB) hfa h)
  have left := distance_radius_mono _ _ _ _ ((U*W)*(A*D)) X
    (positive_product _ _ hL (positive_product _ _ hV hB)) hX
    (le_of_eq_add (d := zero) (by dsimp only [X]; ipra_ring)) leftRaw
  have rightRaw : Γ ⊢[PRAAx] distanceBounded (qmul Q a) (qmul Q b) (U*N) (V*D) :=
    multiply_distance Q a b U V N D hV hD hq hrow
  have rowMono : Γ ⊢[PRAAx] le L W := pw_le_pw C (le_succ_self _)
  have right := distance_radius_mono _ _ _ _ ((U*W)*(N*B)) X (positive_product _ _ hV hD) hX
    (le_congr (by dsimp only [X]; ipra_ring) (by ipra_ring)
      (le_mul_mono rowMono (le_refl (U*N*V*B*D)))) rightRaw
  have combined := distance_congr (product_succ f j x).eqSymm (product_succ g j y).eqSymm
    (by ipra_ring : Γ ⊢[PRAAx] (U*W)*(A*D)+(U*W)*(N*B) ≐ (U*W)*(A*D+N*B)) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hX left right)
  unfold prefixDistance
  have expEq : Γ ⊢[PRAAx] U'*((V*L)) ≐ (U*W)*V' := (prefix_power_identity C j).eqSymm
  have compare : Γ ⊢[PRAAx] le (((U*W)*(A*D+N*B))*(V'*B')) ((U'*A')*X) := by
    have localError : Γ ⊢[PRAAx] le ((A*D+N*B)*B') (A'*(B*D)) := add_row_error E H M j
    have grow := le_mul_mono (le_refl (U'*(V*L))) localError
    have expNat := natEq expEq
    exact le_congr (by apply deriveNat; ipra_simps; rw [expNat]; ring)
      (by dsimp only [X]; ipra_ring) grow
  exact distance_radius_mono _ _ _ _ _ _ hX
    (positive_product _ _ (prefix_power_positive C (succ j)) (positive_product _ _ hM (zero_lt_succ _)))
    compare combined

private def law (f g : PTm 2) (x y C E H M K j : PTm n) : Fm PTm n :=
  le j K ⟶ prefixDistance f g x y C E H M j

@[simp] private theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (x y C E H M K j : PTm n) :
    (law f g x y C E H M K j).subst σ = law f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ H) (Syn.subst σ M) (Syn.subst σ K) (Syn.subst σ j) := by simp [law]

theorem compare_prefix (f g : PTm 2) (x y C E H M K j : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hf : Γ ⊢[PRAAx] factorBounds f x C zero)
    (hg : Γ ⊢[PRAAx] factorBounds g y C zero) (h : Γ ⊢[PRAAx] rowErrors f g x y E H M K)
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx] prefixDistance f g x y C E H M j := by
  let Δ := Γ.map Fm.shift
  let sx := Syn.shift x
  let sy := Syn.shift y
  let sC := Syn.shift C
  let sE := Syn.shift E
  let sH := Syn.shift H
  let sM := Syn.shift M
  let sK := Syn.shift K
  have hhM : Δ ⊢[PRAAx] le one sM := by simpa [Fm.shift,Syn.shift,Δ,sM,one] using hM.shift
  have hhf : Δ ⊢[PRAAx] factorBounds f sx sC zero := by simpa [Fm.shift,Syn.shift,Δ,sx,sC] using hf.shift
  have hhg : Δ ⊢[PRAAx] factorBounds g sy sC zero := by simpa [Fm.shift,Syn.shift,Δ,sy,sC] using hg.shift
  have hh : Δ ⊢[PRAAx] rowErrors f g sx sy sE sH sM sK := by
    simpa [Fm.shift,Syn.shift,Δ,sx,sy,sE,sH,sM,sK] using h.shift
  have all : Γ ⊢[PRAAx] .all (law f g sx sy sC sE sH sM sK (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sx,sy,sC,sE,sH,sM,sK]
      exact .impI (prefix_zero f g x y C E H M hM.wk)
    · simp only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sx,sy,sC,sE,sH,sM,sK,Δ]
      refine .impI ?_
      exact prefix_succ f g sx sy sC sE sH sM (var 0) hhM.wk.wk hhf.wk.wk hhg.wk.wk
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
        (row_error_at f g sx sy sE sH sM sK (var 0) hh.wk.wk Prf.hyp0)
  have rule : Γ ⊢[PRAAx] law f g x y C E H M K j := by
    simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sx,sy,sC,sE,sH,sM,sK] using all.allE j
  exact .impE rule hj

theorem compare_products (f g : PTm 2) (x y C E H M K : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hf : Γ ⊢[PRAAx] factorBounds f x C zero)
    (hg : Γ ⊢[PRAAx] factorBounds g y C zero) (h : Γ ⊢[PRAAx] rowErrors f g x y E H M K) :
    Γ ⊢[PRAAx] distanceBounded (qprod f K x) (qprod g K y) (unit (two*C)*(E*(two*H+K))) M := by
  let U := pw (prefixNumerator K) C
  let V := pw (prefixDenominator K) C
  let A := errorNumerator E H K
  let D := errorDenominator M K
  let W := unit (two*C)
  have hV : Γ ⊢[PRAAx] le one V := prefix_power_positive C K
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hM (zero_lt_succ _)
  have residual : Γ ⊢[PRAAx] le (A*M) (E*(two*H+K)*D) := by
    dsimp only [A,D,errorNumerator,errorDenominator]
    ipra_le 2*𝔞 E*𝔞 H*𝔞 M
  have comparison : Γ ⊢[PRAAx] le ((U*A)*M) ((W*(E*(two*H+K)))*(V*D)) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (prefix_power_upper C K) residual)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hV hD) hM comparison
    (compare_prefix f g x y C E H M K K hM hf hg h (le_refl K))

theorem actual_weighted_inverse_square_product_comparison_closed (f g : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 1) ⟶ factorBounds f (var 6) (var 4) zero ⟶ factorBounds g (var 5) (var 4) zero ⟶
        rowErrors f g (var 6) (var 5) (var 3) (var 2) (var 1) (var 0) ⟶
        distanceBounded (qprod f (var 0) (var 6)) (qprod g (var 0) (var 5))
          (unit (two*var 4)*(var 3*(two*var 2+var 0))) (var 1)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (compare_products f g _ _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianInverseSquareProductComparison
