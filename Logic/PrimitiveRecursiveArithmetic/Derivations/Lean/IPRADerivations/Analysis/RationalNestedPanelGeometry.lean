import IPRADerivations.Analysis.GaussianRationalHorner

/-!
# Exact rational splitting after positive denominator rescaling

Containment expressed by native cross products determines the three
actual widths on a common denominator. The two outside widths use
natural subtraction. Coincident endpoints give zero-width splits.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalNestedPanelGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (a C E b D H : PTm n) : Fm PTm n :=
  le (H*a) (E*b) ⋏ le (E*(b+D)) (H*(a+C))
def leftWidth (a E b H : PTm n) : PTm n := monus (E*b) (H*a)
def rightWidth (a C E b D H : PTm n) : PTm n := monus (H*(a+C)) (E*(b+D))

theorem left_cut (a C E b D H : PTm n) (h : Γ ⊢[PRAAx] source a C E b D H) :
    Γ ⊢[PRAAx] H*a+leftWidth a E b H ≐ E*b :=
  (eq_add_of_le h.andE₁).eqSymm

theorem right_cut (a C E b D H : PTm n) (h : Γ ⊢[PRAAx] source a C E b D H) :
    Γ ⊢[PRAAx] (H*a+leftWidth a E b H)+E*D ≐ E*(b+D) :=
  (congrAdd (left_cut a C E b D H h) (.eqRefl _)).eqTrans (by ipra_ring)

theorem total_width (a C E b D H : PTm n) (h : Γ ⊢[PRAAx] source a C E b D H) :
    Γ ⊢[PRAAx] leftWidth a E b H+E*D+rightWidth a C E b D H ≐ H*C := by
  let L := leftWidth a E b H
  let U := rightWidth a C E b D H
  have lower := natEq (left_cut a C E b D H h)
  have above : Γ ⊢[PRAAx] H*(a+C) ≐ E*(b+D)+U := eq_add_of_le h.andE₂
  have upper := natEq above
  apply deriveNat
  change 𝔞 (L+E*D+U) = 𝔞 (H*C)
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at lower upper ⊢
  linear_combination lower-upper

theorem actual_native_rational_nested_panel_widths_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      ((var 5*var 0+leftWidth (var 0) (var 2) (var 3) (var 5) ≐ var 2*var 3) ⋏
        (((var 5*var 0+leftWidth (var 0) (var 2) (var 3) (var 5))+var 2*var 4 ≐ var 2*(var 3+var 4)) ⋏
          (leftWidth (var 0) (var 2) (var 3) (var 5)+var 2*var 4+
            rightWidth (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ var 5*var 1)))) :=
  closeUniv 6 (.impI (.andI (left_cut _ _ _ _ _ _ Prf.hyp0)
    (.andI (right_cut _ _ _ _ _ _ Prf.hyp0) (total_width _ _ _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalNestedPanelGeometry
