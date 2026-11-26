import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianGeneralFTAConstants
import IPRADerivations.Analysis.Geometry.GaussianGeometricProductBound

/-!
# The computed general-FTA product is uniformly bounded

The actual constants C, K and T discharge the finite tail budget; the
actual product recursors therefore satisfy u_j<=v_j R and 1<=U_j<=R.
Only the original positive degree is assumed. No tail-smallness, product
bound, successful search or iteration invariant is a source premise.
The coefficient observer is a fixed PR3 syntax parameter; every degree,
precision, data value and product index is an internal number.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralProductBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (C K T R)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (a : PR 3) (N h x j : PTm n) : PTm n := GaussianGeometricProduct.numerator (C a N h x) (K N) j
def denominator (a : PR 3) (N h x j : PTm n) : PTm n := GaussianGeometricProduct.denominator (C a N h x) (K N) j
def value (a : PR 3) (N h x j : PTm n) : PTm n := GaussianGeometricProduct.value (C a N h x) (K N) j

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (numerator a N h x j) = numerator a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by
  simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (denominator a N h x j) = denominator a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by
  simp [denominator]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (value a N h x j) = value a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by
  simp [value]

theorem computed_tail_small (a : PR 3) (N h x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianGeometricProductTail.small (C a N h x) (K N) (T a N h x) :=
  le_congr (by unfold GaussianGeometricProductTail.tailNumerator GaussianGeneralFTAConstants.rhoNum; ipra_ring) (.eqRefl _)
    (GaussianGeneralFTAConstants.tail_small a N h x hN)

theorem denominator_positive (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (denominator a N h x j) :=
  GaussianGeometricProduct.denominator_positive _ _ _ (GaussianGeneralFTAConstants.K_positive N hN)

theorem numerator_positive (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (numerator a N h x j) :=
  GaussianGeometricProduct.numerator_positive _ _ _ (GaussianGeneralFTAConstants.K_positive N hN)

/-- The actual computed cutoff discharges the generic finite-tail rule. -/
theorem uniform_bound (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (numerator a N h x j) (denominator a N h x j*R a N h x) :=
  GaussianGeometricProductBound.uniform_bound _ _ _ _ (GaussianGeneralFTAConstants.K_positive N hN)
    (computed_tail_small a N h x hN)

theorem value_lower (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (fraction one one) (value a N h x j) :=
  GaussianGeometricProduct.value_ge_one _ _ _ (GaussianGeneralFTAConstants.K_positive N hN)

theorem value_upper (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (value a N h x j) (fraction (R a N h x) one) :=
  GaussianGeometricProductBound.value_uniform_bound _ _ _ _ (GaussianGeneralFTAConstants.K_positive N hN)
    (computed_tail_small a N h x hN)

theorem value_bounds (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (fraction one one) (value a N h x j) ⋏ rationalLE (value a N h x j) (fraction (R a N h x) one) :=
  .andI (value_lower a N h x j hN) (value_upper a N h x j hN)

theorem value_canonical (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (value a N h x j) :=
  GaussianGeometricProduct.value_canonical _ _ _ (GaussianGeneralFTAConstants.K_positive N hN)

def output (a : PR 3) (N h x j : PTm n) : PTm n := pairT (value a N h x j)
  (pairT (R a N h x) (pairT (numerator a N h x j) (denominator a N h x j)))
def outputF (a : PR 3) : PR 4 := PTm.toPR (output a (var 0) (var 1) (var 2) (var 3))
def run (a : PR 3) (N h x j : PTm n) : PTm n := PTm.app (outputF a) ![N,h,x,j]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (output a N h x j) = output a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by
  simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (run a N h x j) = run a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] run a N h x j ≐ output a N h x j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,h,x,j]
theorem returned_value (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] fstT (run a N h x j) ≐ value a N h x j :=
  (congrFst (program_at a N h x j)).eqTrans (fst_pair _ _)
theorem returned_radius (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run a N h x j)) ≐ R a N h x :=
  (congrFst ((congrSnd (program_at a N h x j)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_numerator (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run a N h x j))) ≐ numerator a N h x j :=
  (congrFst ((congrSnd ((congrSnd (program_at a N h x j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run a N h x j))) ≐ denominator a N h x j :=
  (congrSnd ((congrSnd ((congrSnd (program_at a N h x j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_value_bounds (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (fraction one one) (fstT (run a N h x j)) ⋏
      rationalLE (fstT (run a N h x j)) (fraction (fstT (sndT (run a N h x j))) one) :=
  .andI (RationalArgmin.rationalLE_congr (.eqRefl _) (returned_value a N h x j).eqSymm (value_lower a N h x j hN))
    (RationalArgmin.rationalLE_congr (returned_value a N h x j).eqSymm
      (RationalNonnegativePowers.fraction_congr (returned_radius a N h x j).eqSymm (.eqRefl _)) (value_upper a N h x j hN))

theorem computed_general_product_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le (numerator a (var 0) (var 1) (var 2) (var 3))
      (denominator a (var 0) (var 1) (var 2) (var 3)*R a (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (uniform_bound _ _ _ _ _ Prf.hyp0))

theorem computed_general_product_value_bounds_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶
      (rationalLE (fraction one one) (value a (var 0) (var 1) (var 2) (var 3)) ⋏
        rationalLE (value a (var 0) (var 1) (var 2) (var 3)) (fraction (R a (var 0) (var 1) (var 2)) one))) :=
  closeUniv 4 (.impI (value_bounds _ _ _ _ _ Prf.hyp0))

theorem computed_general_product_positive_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶
      (le one (denominator a (var 0) (var 1) (var 2) (var 3)) ⋏ le one (numerator a (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.andI (denominator_positive _ _ _ _ _ Prf.hyp0) (numerator_positive _ _ _ _ _ Prf.hyp0)))

theorem computed_general_product_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run a (var 0) (var 1) (var 2) (var 3) ≐ output a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _ _)

theorem returned_general_product_value_bounds_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶
      (rationalLE (fraction one one) (fstT (run a (var 0) (var 1) (var 2) (var 3))) ⋏
        rationalLE (fstT (run a (var 0) (var 1) (var 2) (var 3)))
          (fraction (fstT (sndT (run a (var 0) (var 1) (var 2) (var 3)))) one))) :=
  closeUniv 4 (.impI (returned_value_bounds _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGeneralProductBound
