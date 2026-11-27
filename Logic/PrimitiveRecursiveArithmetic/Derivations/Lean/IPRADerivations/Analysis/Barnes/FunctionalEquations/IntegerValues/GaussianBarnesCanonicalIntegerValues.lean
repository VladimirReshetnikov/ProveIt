import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.GaussianBarnesCanonicalIntegerRecurrence
import IPRADerivations.Analysis.Barnes.CanonicalProducts.Values.GaussianBarnesCanonicalNormalization
import IPRADerivations.Analysis.Barnes.CanonicalProducts.Values.GaussianBarnesCanonicalProperness
import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.BarnesInteger

/-!
# The original Barnes value equals the superfactorial at every integer

Fix an observation precision and induct on the numerical error in the
original value at successive integer arguments. Multiplication by the
exact factorial gives a primitive-recursive error budget. The regular
names are then compared at arbitrary independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerValues

open_ipra
open GaussianBarnesCanonicalValue (nameF)
open GaussianBarnesCanonicalIntegerRecurrence
  (center data value modulus center_norm center_native integer_source value_regular successor_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qone)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open ComplexLogarithmRemainder (oneCode scale)
open BarnesInteger (barnes)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def integerValue (i : PTm n) : PTm n := naturalPoint (barnes i)
def errorF : PR 2 := rec2 (two : PTm 1)
  (two+(modulus (var 0)+one)+var 1*fact (var 0))
def error (i : PTm n) : PTm n := ap2 errorF i zero
def errorLaw (p i : PTm n) : Fm PTm n := distanceBounded (value p i) (integerValue i) (error i) (unit p)

@[simp] theorem subst_integerValue {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (integerValue i) = integerValue (Syn.subst σ i) := by simp [integerValue]

@[simp] theorem subst_error {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (error i) = error (Syn.subst σ i) := by simp [error]

@[simp] theorem subst_errorLaw {m : ℕ} (σ : Fin n → PTm m) (p i : PTm n) :
    (errorLaw p i).subst σ = errorLaw (Syn.subst σ p) (Syn.subst σ i) := by simp [errorLaw]

private theorem error_zero : Γ ⊢[PRAAx] error (zero : PTm n) ≐ two := by
  simpa [error,errorF,two] using
    rec2_zero (Γ := Γ) (two : PTm 1) (two+(modulus (var 0)+one)+var 1*fact (var 0)) zero

theorem error_succ (i : PTm n) : Γ ⊢[PRAAx]
    error (succ i) ≐ two+(modulus i+one)+error i*fact i := by
  have h := rec2_succ (Γ := Γ) (two : PTm 1) (two+(modulus (var 0)+one)+var 1*fact (var 0)) i zero
  simp only [PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,
    GaussianBarnesCanonicalIntegerRecurrence.subst_modulus,fact,subst_ap2,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,
    one,two,ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem integer_value_succ (i : PTm n) : Γ ⊢[PRAAx]
    qmul (integerValue i) (GaussianGammaFactorialValues.factorialValue i) ≐ integerValue (succ i) :=
  (GaussianGammaFactorialValues.natural_product (barnes i) (fact i)).eqTrans
    (GaussianGammaFactorialValues.natural_congr (BarnesInteger.barnes_succ i).eqSymm)

private theorem error_base (p : PTm n) : Γ ⊢[PRAAx] errorLaw p zero := by
  have hn := (center_norm (Γ := Γ) (zero : PTm n)).eqTrans (zero_mul zero)
  have normal := GaussianBarnesCanonicalNormalization.normalization (center zero) zero one (le_refl _) hn
  have near := GaussianNameEquivalence.cross_at _ _ _ _ p p normal
  have right : Γ ⊢[PRAAx] ap2 constantF p qone ≐ integerValue zero :=
    (constant_at p qone).eqTrans
      ((GaussianGammaFactorialValues.natural_congr BarnesInteger.barnes_zero).eqTrans
        GaussianGammaFactorialValues.natural_one).eqSymm
  have hu := unit_positive (Γ := Γ) p
  have same : Γ ⊢[PRAAx] distanceBounded (value p zero) (integerValue zero) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu
      (le_of_eq_add (d := zero) (by ipra_ring))
      (distance_congr (.eqRefl _) right (.eqRefl _) (.eqRefl _) near)
  exact distance_congr (.eqRefl _) (.eqRefl _) error_zero.eqSymm (.eqRefl _) same

private theorem error_step (p i : PTm n) (ih : Γ ⊢[PRAAx] errorLaw p i) :
    Γ ⊢[PRAAx] errorLaw p (succ i) := by
  have hu := unit_positive (Γ := Γ) p
  have product := GaussianNameRingLaws.product_left_error (value p i) (integerValue i)
    (GaussianGammaFactorialValues.factorialValue i) (error i) (unit p) (fact i) (barnes i) hu ih
    (GaussianGammaFactorialValues.factorial_bound i) (GaussianNamedNaturalScale.natural_point_bound _)
  have next := distance_congr (.eqRefl _) (integer_value_succ i) (.eqRefl _) (.eqRefl _) product
  have total := distance_triangle_same _ _ _ _ _ _ hu (successor_error p i) next
  exact distance_congr (.eqRefl _) (.eqRefl _) (error_succ i).eqSymm (.eqRefl _) total

theorem prefix_error (p i : PTm n) : Γ ⊢[PRAAx] errorLaw p i := by
  have hall : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift p) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using error_base (Γ := Γ) p
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        error_step (Syn.shift p) (var 0) Prf.hyp0
  simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i

theorem observation_envelope (i : PTm n) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal nameF constantF (data i) (integerValue i) (error i) := by
  refine .allI ?_
  have finite := prefix_error (Γ := Γ.map Fm.shift) (var 0) (Syn.shift i)
  have actual := distance_congr (.eqRefl _) (constant_at (var 0) (integerValue (Syn.shift i))).eqSymm
    (.eqRefl _) (.eqRefl _) finite
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,value,Syn.shift,
    GaussianBarnesCanonicalIntegerRecurrence.subst_data,subst_integerValue,subst_error] using actual

/-- The argument of the original canonical sampler is shifted by one, so
at integer center `i` this is the value `G(i+1)`. -/
theorem trajectory_superfactorial (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent nameF constantF (data i) (integerValue i) :=
  GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (error i) (value_regular i)
    (constant_regular _) (observation_envelope i)

theorem original_integer_value (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent nameF constantF
      (GaussianBarnesCanonicalValue.data (scale i oneCode) i one) (integerValue i) := by
  let z := scale i oneCode
  have native := center_native (Γ := Γ) i
  have src : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z i one :=
    .andI (le_refl _) (le_congr (GaussianRootAlgebra.normSq_equal native) (.eqRefl _) (integer_source i).andE₂)
  have same := GaussianGammaFiniteValueProperness.fraction_equal _ _ one (le_refl _) native
  have move := GaussianBarnesCanonicalProperness.proper z (center i) i i one one src (integer_source i) same.eqSymm
  exact cross_trans _ _ _ _ _ _ move (trajectory_superfactorial i)

theorem actual_original_Barnes_superfactorial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let i := var 0; crossEquivalent nameF constantF
      (GaussianBarnesCanonicalValue.data (scale i oneCode) i one) (integerValue i)) :=
  closeUniv 1 (original_integer_value _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerValues
