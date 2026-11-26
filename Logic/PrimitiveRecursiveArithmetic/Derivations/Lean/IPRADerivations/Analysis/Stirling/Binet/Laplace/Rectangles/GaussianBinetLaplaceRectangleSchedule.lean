import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceDifferenceGrid
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Rectangles.GaussianBinetLaplaceRectangleRowBudget
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialRectangleEvaluation

/-!
# A common primitive-recursive schedule for the first Binet identity

The horizon pays for both tails. The observation clock pays for the
difference and both orders of the rectangular sum. The time mesh is
a common refinement and the unit mesh satisfies the bounds for the
weighted exponential and the weighted resolvent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRectangleSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetExponentialRectangleEvaluation (observationCost tailCost)
open GaussianBinetLaplaceDifferenceGrid (gridCount)
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianBinetLaplaceOrderedPrefixes (width)
open GaussianBinetLaplaceRectangleRowBudget (clockCost meshCost)
open GaussianBinetLogCellGrid (requiredMesh)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh mesh_positive precision)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero succ)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cutoff (p D : PTm n) : PTm n := succ (tailCost D*unit p+D*unit p)

def horizon (p D : PTm n) : PTm n := width D (cutoff p D)

def clock (p A B D : PTm n) : PTm n :=
  let L := cutoff p D
  let T := horizon p D
  L+(precision p T+(observationCost (radius A B) D (D*L)*unit p+clockCost T*unit p))

def unitMesh (p A B D : PTm n) : PTm n :=
  unit p+(requiredMesh A B D zero+meshCost (horizon p D)*unit p)

def extra (p A B D : PTm n) : PTm n :=
  (radius A B+one)*(D*cutoff p D)+unit (clock p A B D)

def timeMesh (p A B D : PTm n) : PTm n := gridCount p A B D (cutoff p D) (extra p A B D)

private theorem le_unit (p : PTm n) : Γ ⊢[PRAAx] le p (unit p) :=
  le_trans (le_succ_self p) (RationalClosure.succ_le_two_pow p)

theorem cutoff_bounds (p D : PTm n) : Γ ⊢[PRAAx]
    le one (cutoff p D) ⋏
      (le (D*unit p) (unit (cutoff p D)) ⋏ le (tailCost D*unit p) (unit (cutoff p D))) := by
  let t := tailCost D*unit p
  let d := D*unit p
  have grow : Γ ⊢[PRAAx] le (t+d) (unit (cutoff p D)) :=
    le_trans (le_succ_self (t+d)) (le_unit (cutoff p D))
  exact .andI (zero_lt_succ _) (.andI
    (le_trans (le_add_left d t) grow) (le_trans (le_add_right t d) grow))

theorem horizon_eq (p D : PTm n) : Γ ⊢[PRAAx] horizon p D ≐ D*cutoff p D :=
  (mul_comm (D*cutoff p D) one).eqTrans (one_mul _)

theorem horizon_positive (p D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (horizon p D) :=
  le_congr (.eqRefl _) (horizon_eq p D).eqSymm
    (positive_product _ _ hD (cutoff_bounds p D).andE₁)

theorem reciprocal_margin (A D : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le D (D*A) :=
  le_congr (one_mul D) (mul_comm A D) (mul_le_mul_right D hA)

theorem clock_bounds (p A B D : PTm n) : Γ ⊢[PRAAx]
    le (cutoff p D) (clock p A B D) ⋏
    (le (precision p (horizon p D)) (clock p A B D) ⋏
      (le (observationCost (radius A B) D (D*cutoff p D)*unit p) (unit (clock p A B D)) ⋏
        le (clockCost (horizon p D)*unit p) (unit (clock p A B D)))) := by
  let L := cutoff p D
  let P := precision p (horizon p D)
  let X := observationCost (radius A B) D (D*L)*unit p
  let Y := clockCost (horizon p D)*unit p
  let r := clock p A B D
  have hp : Γ ⊢[PRAAx] le (P+(X+Y)) r := le_add_left _ L
  have hb : Γ ⊢[PRAAx] le (X+Y) (unit r) :=
    le_trans (le_add_left _ P) (le_trans hp (le_unit r))
  exact .andI (le_add_right L _) (.andI (le_trans (le_add_right P (X+Y)) hp)
    (.andI (le_trans (le_add_right X Y) hb) (le_trans (le_add_left Y X) hb)))

theorem unit_mesh_bounds (p A B D : PTm n) : Γ ⊢[PRAAx]
    le (unit p) (unitMesh p A B D) ⋏
      (le (requiredMesh A B D zero) (unitMesh p A B D) ⋏
        le (meshCost (horizon p D)*unit p) (unitMesh p A B D)) := by
  let a := requiredMesh A B D zero
  let b := meshCost (horizon p D)*unit p
  have bridge : Γ ⊢[PRAAx] le (a+b) (unitMesh p A B D) := le_add_left _ _
  exact .andI (le_add_right _ _) (.andI
    (le_trans (le_add_right a b) bridge) (le_trans (le_add_left b a) bridge))

theorem time_mesh_bounds (p A B D : PTm n) : Γ ⊢[PRAAx]
    le one (extra p A B D) ⋏
    (le one (timeMesh p A B D) ⋏
      (le ((radius A B+one)*(D*cutoff p D)) (timeMesh p A B D) ⋏
        le (unit (clock p A B D)) (timeMesh p A B D))) := by
  let T := horizon p D
  let a := (radius A B+one)*(D*cutoff p D)
  let b := unit (clock p A B D)
  let x := mesh p (meshGain (radius A B) T) T
  let y := mesh p (meshGain (radius (A+D) B) T) T
  let e := extra p A B D
  have ha : Γ ⊢[PRAAx] le a e := le_add_right a b
  have hb : Γ ⊢[PRAAx] le b e := le_add_left b a
  have hx : Γ ⊢[PRAAx] le one x := mesh_positive p _ T
  have hy : Γ ⊢[PRAAx] le one y := mesh_positive p _ T
  have he := le_trans (unit_positive (clock p A B D)) hb
  have hn : Γ ⊢[PRAAx] le e (timeMesh p A B D) :=
    le_congr (one_mul e) (.eqRefl _) (mul_le_mul_right e (positive_product x y hx hy))
  exact .andI he (.andI (le_trans he hn) (.andI (le_trans ha hn) (le_trans hb hn)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRectangleSchedule
