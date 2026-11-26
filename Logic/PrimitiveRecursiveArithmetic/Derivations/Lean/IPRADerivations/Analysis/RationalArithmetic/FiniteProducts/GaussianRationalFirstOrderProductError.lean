import IPRADerivations.Analysis.Polynomials.Taylor.GaussianRationalFirstOrderPolynomial

/-!
# Actual first-order product errors and their uniform quadratic bound

The original normalized qcode operations satisfy the exact three-term
product remainder identity on arbitrary raw Gaussian codes. All six
actual denominator representations are brought to one computed positive
denominator; genuine native complex algebra proves the equality.
The actual Euclidean triangle and product inequalities then give a
uniform quadratic error bound, without a Beta-specific output premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFirstOrderProductError

open_ipra
open GaussianRationalHorner (qadd qmul represents canonical positive_product qmul_represents qadd_represents represents_congr canonical_unique)
open GaussianRationalMetric (qsub qsub_represents bounded)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalPowerDifference (bounded_sum_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def error (x1 x0 a : PTm n) : PTm n := qsub (qsub x1 x0) a
def linearPart (x0 y0 a b : PTm n) : PTm n := qadd (qmul a y0) (qmul x0 b)
def productError (x1 x0 y1 y0 a b : PTm n) : PTm n :=
  qsub (qsub (qmul x1 y1) (qmul x0 y0)) (linearPart x0 y0 a b)
def decomposedError (x1 x0 y1 y0 a b : PTm n) : PTm n :=
  qadd (qadd (qmul (error x1 x0 a) y1) (qmul x0 (error y1 y0 b))) (qmul a (qsub y1 y0))
def commonDenominator (x1 x0 y1 y0 a b : PTm n) : PTm n := rawDen x1*rawDen x0*rawDen y1*rawDen y0*rawDen a*rawDen b

ipra_subst error
ipra_subst linearPart
ipra_subst productError
ipra_subst decomposedError

theorem common_denominator_positive (x1 x0 y1 y0 a b : PTm n) : Γ ⊢[PRAAx] le one (commonDenominator x1 x0 y1 y0 a b) :=
  positive_product _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ (raw_den_positive x1) (raw_den_positive x0)) (raw_den_positive y1)) (raw_den_positive y0)) (raw_den_positive a)) (raw_den_positive b)

private theorem identity_from_representations (x1 x0 y1 y0 a b X1 X0 Y1 Y0 A B E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hx1 : Γ ⊢[PRAAx] represents x1 X1 E) (hx0 : Γ ⊢[PRAAx] represents x0 X0 E)
    (hy1 : Γ ⊢[PRAAx] represents y1 Y1 E) (hy0 : Γ ⊢[PRAAx] represents y0 Y0 E)
    (ha : Γ ⊢[PRAAx] represents a A E) (hb : Γ ⊢[PRAAx] represents b B E) : Γ ⊢[PRAAx]
    productError x1 x0 y1 y0 a b ≐ decomposedError x1 x0 y1 y0 a b := by
  have hE2 := positive_product E E hE hE
  have lhs := qsub_represents _ _ _ _ _ hE2
    (qsub_represents _ _ _ _ _ hE2 (qmul_represents _ _ _ _ _ _ hE hE hx1 hy1) (qmul_represents _ _ _ _ _ _ hE hE hx0 hy0))
    (qadd_represents _ _ _ _ _ hE2 (qmul_represents _ _ _ _ _ _ hE hE ha hy0) (qmul_represents _ _ _ _ _ _ hE hE hx0 hb))
  have rhs := qadd_represents _ _ _ _ _ hE2
    (qadd_represents _ _ _ _ _ hE2
      (qmul_represents _ _ _ _ _ _ hE hE (qsub_represents _ _ _ _ _ hE (qsub_represents _ _ _ _ _ hE hx1 hx0) ha) hy1)
      (qmul_represents _ _ _ _ _ _ hE hE hx0 (qsub_represents _ _ _ _ _ hE (qsub_represents _ _ _ _ _ hE hy1 hy0) hb)))
    (qmul_represents _ _ _ _ _ _ hE hE ha (qsub_represents _ _ _ _ _ hE hy1 hy0))
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalHorner.qadd_canonical _ _) hE2 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_mul,
      GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring

/-- Literal normalized qcode identity, for arbitrary raw inputs. -/
theorem product_error_identity (x1 x0 y1 y0 a b : PTm n) : Γ ⊢[PRAAx]
    productError x1 x0 y1 y0 a b ≐ decomposedError x1 x0 y1 y0 a b := by
  let E := commonDenominator x1 x0 y1 y0 a b
  have hx1 := rescale_to x1 (rawGaussian x1) (rawDen x1) (rawDen x0*rawDen y1*rawDen y0*rawDen a*rawDen b) E
    (raw_represents (Γ := Γ) x1) (by unfold E commonDenominator; ipra_ring)
  have hx0 := rescale_to x0 (rawGaussian x0) (rawDen x0) (rawDen x1*rawDen y1*rawDen y0*rawDen a*rawDen b) E
    (raw_represents (Γ := Γ) x0) (by unfold E commonDenominator; ipra_ring)
  have hy1 := rescale_to y1 (rawGaussian y1) (rawDen y1) (rawDen x1*rawDen x0*rawDen y0*rawDen a*rawDen b) E
    (raw_represents (Γ := Γ) y1) (by unfold E commonDenominator; ipra_ring)
  have hy0 := rescale_to y0 (rawGaussian y0) (rawDen y0) (rawDen x1*rawDen x0*rawDen y1*rawDen a*rawDen b) E
    (raw_represents (Γ := Γ) y0) (by unfold E commonDenominator; ipra_ring)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen x1*rawDen x0*rawDen y1*rawDen y0*rawDen b) E
    (raw_represents (Γ := Γ) a) (by unfold E commonDenominator; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen x1*rawDen x0*rawDen y1*rawDen y0*rawDen a) E
    (raw_represents (Γ := Γ) b) (by unfold E commonDenominator; ipra_ring)
  exact identity_from_representations _ _ _ _ _ _ _ _ _ _ _ _ E (common_denominator_positive x1 x0 y1 y0 a b) hx1 hx0 hy1 hy0 ha hb

/-- All three actual error terms are kept. The two old/new value bounds
are integer radii; both linear increments use the same requested D. -/
theorem quadratic_error_bound (x1 x0 y1 y0 a b X Y Ex Ey A V D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hx0 : Γ ⊢[PRAAx] bounded x0 X one) (hy1 : Γ ⊢[PRAAx] bounded y1 Y one)
    (hex : Γ ⊢[PRAAx] bounded (error x1 x0 a) Ex (D*D)) (hey : Γ ⊢[PRAAx] bounded (error y1 y0 b) Ey (D*D))
    (ha : Γ ⊢[PRAAx] bounded a A D) (hdy : Γ ⊢[PRAAx] bounded (qsub y1 y0) V D) : Γ ⊢[PRAAx]
    bounded (productError x1 x0 y1 y0 a b) (Ex*Y+X*Ey+A*V) (D*D) := by
  have hD2 := positive_product D D hD hD
  have first : Γ ⊢[PRAAx] bounded (qmul (error x1 x0 a) y1) (Ex*Y) (D*D) :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product _ _ _ _ _ _ hD2 (le_refl one) hex hy1)
  have second : Γ ⊢[PRAAx] bounded (qmul x0 (error y1 y0 b)) (X*Ey) (D*D) :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product _ _ _ _ _ _ (le_refl one) hD2 hx0 hey)
  have third := bounded_product a (qsub y1 y0) A D V D hD hD ha hdy
  exact bound_congr (product_error_identity x1 x0 y1 y0 a b).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_sum_same _ _ _ _ _ hD2 (bounded_sum_same _ _ _ _ _ hD2 first second) third)

/-- Explicit h-sized increments and h²-sized residuals give the genuine
uniform first-order product remainder, with no division by h. -/
theorem scaled_quadratic_error_bound (x1 x0 y1 y0 a b X Y Ex Ey A V S D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hx0 : Γ ⊢[PRAAx] bounded x0 X one) (hy1 : Γ ⊢[PRAAx] bounded y1 Y one)
    (hex : Γ ⊢[PRAAx] bounded (error x1 x0 a) (Ex*S*S) (D*D)) (hey : Γ ⊢[PRAAx] bounded (error y1 y0 b) (Ey*S*S) (D*D))
    (ha : Γ ⊢[PRAAx] bounded a (A*S) D) (hdy : Γ ⊢[PRAAx] bounded (qsub y1 y0) (V*S) D) : Γ ⊢[PRAAx]
    bounded (productError x1 x0 y1 y0 a b) ((Ex*Y+X*Ey+A*V)*S*S) (D*D) :=
  bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) (quadratic_error_bound _ _ _ _ _ _ _ _ _ _ _ _ _ hD hx0 hy1 hex hey ha hdy)

/-- Actual normalized output: residual, exact decomposition, linear term. -/
def output (x1 x0 y1 y0 a b : PTm n) : PTm n :=
  pairT (productError x1 x0 y1 y0 a b) (pairT (decomposedError x1 x0 y1 y0 a b) (linearPart x0 y0 a b))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (x1 x0 y1 y0 a b : PTm n) : PTm n := PTm.app outputF ![x1,x0,y1,y0,a,b]
theorem program_at (x1 x0 y1 y0 a b : PTm n) : Γ ⊢[PRAAx] run x1 x0 y1 y0 a b ≐ output x1 x0 y1 y0 a b := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![x1,x0,y1,y0,a,b]

theorem actual_first_order_product_error_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (productError (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ decomposedError (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (product_error_identity _ _ _ _ _ _)
theorem actual_first_order_product_quadratic_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((le one (var 12) ⋏ bounded (var 1) (var 6) one ⋏ bounded (var 2) (var 7) one ⋏
      bounded (error (var 0) (var 1) (var 4)) (var 8) (var 12*var 12) ⋏ bounded (error (var 2) (var 3) (var 5)) (var 9) (var 12*var 12) ⋏
      bounded (var 4) (var 10) (var 12) ⋏ bounded (qsub (var 2) (var 3)) (var 11) (var 12)) ⟶
      bounded (productError (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 8*var 7+var 6*var 9+var 10*var 11) (var 12*var 12)) :=
  closeUniv 13 (.impI (quadratic_error_bound _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))
theorem actual_scaled_first_order_product_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    ((le one (var 13) ⋏ bounded (var 1) (var 6) one ⋏ bounded (var 2) (var 7) one ⋏
      bounded (error (var 0) (var 1) (var 4)) (var 8*var 12*var 12) (var 13*var 13) ⋏
      bounded (error (var 2) (var 3) (var 5)) (var 9*var 12*var 12) (var 13*var 13) ⋏
      bounded (var 4) (var 10*var 12) (var 13) ⋏ bounded (qsub (var 2) (var 3)) (var 11*var 12) (var 13)) ⟶
      bounded (productError (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ((var 8*var 7+var 6*var 9+var 10*var 11)*var 12*var 12) (var 13*var 13)) :=
  closeUniv 14 (.impI (scaled_quadratic_error_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))
theorem actual_first_order_product_error_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalFirstOrderProductError
