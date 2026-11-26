import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingDifferenceBrackets
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingNamedTelescopeBounds
import IPRADerivations.Analysis.Inequalities.GaussianRationalNonnegativeFractions

/-!
# The sharp bounds on the original named Stirling difference

The finite harmonic logarithm bracket is compared with the exact
upper telescoper and its positive correction. The first odd term
supplies the lower Robbins correction. Each comparison keeps the
error of the actual observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDifferenceBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianRationalHorner (qadd qzero positive_product qadd_canonical)
open GaussianStirlingDifferenceBrackets (observation_brackets)
open GaussianStirlingFiniteBounds (first_term_bound sharp_upper geometricTail)
open GaussianStirlingFiniteTelescopeBounds (localBounds)
open GaussianStirlingNames (source)
open GaussianStirlingNamedTelescopeBounds (allRows endpointBounds named_telescope_bounds)
open GaussianStirlingOddSeries (partialSum tail)
open GaussianStirlingRationalTelescopers (firstTerm geometricMain upperMargin lowerDifference lowerMargin
  lower_cell_margin small_numeral_positive square_positive)
open GaussianStirlingTailComparison (point_add_order point_order_refl tail_le_geometric sharp_partial_order sharpUpperValue)
open GaussianStirlingTelescope (shifted shifted_source)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalValueBounds (upper upper_congr upper_order_left upper_order_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianStirlingDifference.nameF
local notation "DD" => GaussianStirlingDifference.data

theorem first_sample_lower (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (firstTerm a b)) (fstT (ap2 D p (DD a b))) one (unit p) := by
  let L := succ (two*succ (zero : PTm n))
  have low := (observation_brackets a b one p hs.andE₁ hs.andE₂).andE₁
  exact upper_order_left _ _ _ _ _ (first_term_bound a b L zero hs.andE₂ (le_refl L)) low

theorem sharp_sample_upper (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 D p (DD a b))) (fstT (sharpUpperValue a b)) one (unit p) := by
  let L := succ (two*succ (succ (zero : PTm n)))
  have hi := (observation_brackets a b two p hs.andE₁ hs.andE₂).andE₂
  exact upper_order_right _ _ _ _ _ hi (sharp_partial_order a b L zero hs.andE₁ hs.andE₂ (le_refl L))

theorem robbins_sample_lower (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    upper (fstT (qadd (lowerDifference a b one) (lowerMargin a b))) (fstT (ap2 D p (DD a b))) one (unit p) :=
  upper_congr (congrFst (lower_cell_margin a b hs.andE₁ hs.andE₂ hba).eqSymm)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (first_sample_lower p a b hs)

private theorem zero_to_fraction (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE (fstT qzero) (fstT (GaussianPositiveRationalLogarithm.fraction A B)) :=
  rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _)
    (GaussianRationalNonnegativeFractions.fraction_nonnegative A B hB).andE₁

private theorem weak_sample_upper (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 D p (DD a b))) (fstT (geometricMain a b)) one (unit p) := by
  let S := partialSum a b two
  let T := tail a b two
  let G := geometricTail a b two
  let X := qadd S G
  let K := GaussianStirlingRationalTelescopers.denominatorSquare a b
  let L := succ (two*succ (succ (zero : PTm n)))
  have hK := square_positive a b hs.andE₂
  have nonneg : Γ ⊢[PRAAx] rationalLE (fstT qzero) (fstT (upperMargin a b)) :=
    zero_to_fraction _ (num 15*K*K) (positive_product _ _ (positive_product _ _ (small_numeral_positive 14) hK) hK)
  have withMargin := point_add_order X X qzero (upperMargin a b) (point_order_refl X) nonneg
  have without := rationalLE_congr (congrFst (GaussianReciprocalHorner.qadd_zero_right X (qadd_canonical S G)))
    (.eqRefl _) withMargin
  have trueTail := point_add_order S S T G (point_order_refl S) (tail_le_geometric a b two hs.andE₁ hs.andE₂)
  have bound := transitive trueTail (transitive without (sharp_upper a b L zero hs.andE₁ hs.andE₂ (le_refl L)))
  exact upper_order_right _ _ _ _ _ (observation_brackets a b two p hs.andE₁ hs.andE₂).andE₂ bound

theorem weak_local_bounds (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] localBounds p a b := by
  have h := positive_product _ _ (small_numeral_positive 2) (square_positive a b hs.andE₂)
  exact .andI (upper_order_left _ _ _ _ _ (zero_to_fraction _ _ h) (first_sample_lower p a b hs))
    (weak_sample_upper p a b hs)

theorem all_rows (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] allRows a b := by
  refine .allI (.allI ?_)
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs' : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift.shift
  simpa [allRows,GaussianStirlingFiniteTelescopeBounds.rows,Syn.shift,sh,Δ] using
    weak_local_bounds (var 1) (shifted (sh a) (sh b) (var 0)) (sh b) (shifted_source _ _ _ hs')

theorem endpoint_bounds (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] endpointBounds N a b :=
  named_telescope_bounds N a b hs (all_rows a b hs)

theorem actual_positive_rational_Stirling_endpoint_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ endpointBounds (var 2) (var 0) (var 1)) :=
  closeUniv 3 (.impI (endpoint_bounds _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingDifferenceBounds
