import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentInverseForward
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport

/-!
# Imaginary-coordinate order under equivalent names

At a common auxiliary precision the two cross-equivalences connect the
new observations to the ordered original observations. Finite integer-gap
removal eliminates the auxiliary contribution.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentImaginaryOrderTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentInverseForward (imaginaryOrder subst_imaginaryOrder imaginary_order_at)
open GaussianArctangentInverseSampler (ordinate)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem imaginary_order_slack (f f' g' g : PR 2) (x x' y' y p q t : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent f f' x x')
    (hg : Γ ⊢[PRAAx] crossEquivalent g' g y' y)
    (hOrder : Γ ⊢[PRAAx] imaginaryOrder f' g' x' y') :
    Γ ⊢[PRAAx] upperSlack (ordinate f p x) (ordinate g q y)
      (unit p+unit q) (unit p*unit q) (num 4) t := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have hpt := positive_product _ _ hp ht
  have htt := positive_product _ _ ht ht
  have htq := positive_product _ _ ht hq
  have left := upper_of_radius _ _ _ _
    (imaginary_coordinate_radius _ _ _ _ hpt (cross_at f f' x x' p t hf))
  have right := upper_of_radius _ _ _ _
    (imaginary_coordinate_radius _ _ _ _ htq (cross_at g' g y' y t q hg))
  have middle := imaginary_order_at f' g' x' y' t t hOrder
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left middle) right
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hpt htt) htq) joined
  exact le_of_eq_add (d := zero) (by ipra_ring)

theorem imaginary_order_congr_at (f f' g' g : PR 2) (x x' y' y p q : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent f f' x x')
    (hg : Γ ⊢[PRAAx] crossEquivalent g' g y' y)
    (hOrder : Γ ⊢[PRAAx] imaginaryOrder f' g' x' y') :
    Γ ⊢[PRAAx] upper (ordinate f p x) (ordinate g q y) (unit p+unit q) (unit p*unit q) :=
  remove_upper_slack _ _ _ _ (num 4) (imaginary_order_slack f f' g' g x x' y' y p q
    (precision (ordinate f p x) (ordinate g q y) (unit p*unit q) (num 4)) hf hg hOrder)

theorem imaginary_order_congr (f f' g' g : PR 2) (x x' y' y : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent f f' x x')
    (hg : Γ ⊢[PRAAx] crossEquivalent g' g y' y)
    (hOrder : Γ ⊢[PRAAx] imaginaryOrder f' g' x' y') :
    Γ ⊢[PRAAx] imaginaryOrder f g x y := by
  refine .allI (.allI ?_)
  let X := Syn.shift (Syn.shift x)
  let X' := Syn.shift (Syn.shift x')
  let Y' := Syn.shift (Syn.shift y')
  let Y := Syn.shift (Syn.shift y)
  have left : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent f f' X X' := by
    simpa [Fm.shift,Syn.shift,X,X'] using hf.shift.shift
  have right : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent g' g Y' Y := by
    simpa [Fm.shift,Syn.shift,Y',Y] using hg.shift.shift
  have order : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] imaginaryOrder f' g' X' Y' := by
    simpa only [Fm.shift,subst_imaginaryOrder,Syn.shift,X',Y'] using hOrder.shift.shift
  exact imaginary_order_congr_at f f' g' g X X' Y' Y (var 1) (var 0) left right order

theorem actual_named_arctangent_imaginary_order_transport_closed (f f' g' g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((crossEquivalent f f' (var 0) (var 1) ⋏ crossEquivalent g' g (var 2) (var 3)) ⟶
        imaginaryOrder f' g' (var 1) (var 2) ⟶ imaginaryOrder f g (var 0) (var 3)) :=
  closeUniv 4 (.impI (.impI (imaginary_order_congr f f' g' g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentImaginaryOrderTransport
