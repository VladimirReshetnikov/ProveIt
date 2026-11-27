import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentations
import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.PolynomialBisection
import IPRADerivations.Analysis.RationalArithmetic.RationalAlgebra

/-!
# One-sided rational error with signed representatives

An observation inequality is exactly its signed cross multiplication at
any proved positive-denominator representations. The error numerator
and denominator remain explicit in both directions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalRepresentedUpper

open_ipra
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper crossLeft positive_cancel)
open RationalArithmetic (represents)
open PolynomialBisection (slack zle_scale_cancel)
open RationalAlgebra (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def left (x : ZT n) (F B : PTm n) : ZT n := x*ZT.ofNat (F*B)
def right (y : ZT n) (E F A B : PTm n) : ZT n :=
  y*ZT.ofNat (E*B)+ZT.ofNat (A*E*F)

theorem to_signed (a b : PTm n) (x y : ZT n) (E F A B : PTm n)
    (hx : Γ ⊢[PRAAx] represents a x E) (hy : Γ ⊢[PRAAx] represents b y F)
    (h : Γ ⊢[PRAAx] upper a b A B) : Γ ⊢[PRAAx] zle (left x F B) (right y E F A B) := by
  let U := denominatorOf a
  let V := denominatorOf b
  let L := B*crossLeft a b
  let R := B*crossLeft b a+A*U*V
  have ea := ZT.toZ_eq hx
  have eb := ZT.toZ_eq hy
  have order := natEq (eq_add_of_le h)
  apply zle_scale_cancel (c := U*V)
    (positive_product (RationalArgmin.denominator_positive a) (RationalArgmin.denominator_positive b))
  apply zle_of_toZ (E*F*monus R L)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at ea eb
  simp only [left,right,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  dsimp only [U,V,L,R]
  simp only [crossLeft,ZT.toZ,Q.mk_add,Q.mk_mul,map_add,map_mul] at ea eb order ⊢
  linear_combination -(𝔞(E)*𝔞(F))*order
    +(𝔞(B)*𝔞(F)*𝔞(denominatorOf b))*ea
    -(𝔞(B)*𝔞(E)*𝔞(denominatorOf a))*eb

theorem from_signed (a b : PTm n) (x y : ZT n) (E F A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hF : Γ ⊢[PRAAx] le one F)
    (hx : Γ ⊢[PRAAx] represents a x E) (hy : Γ ⊢[PRAAx] represents b y F)
    (h : Γ ⊢[PRAAx] zle (left x F B) (right y E F A B)) : Γ ⊢[PRAAx] upper a b A B := by
  let U := denominatorOf a
  let V := denominatorOf b
  have ea := ZT.toZ_eq hx
  have eb := ZT.toZ_eq hy
  have order := zle_toZ h
  unfold upper
  apply positive_cancel (c := E*F) (positive_product hE hF)
  apply le_of_eq_add (d := U*V*slack (left x F B) (right y E F A B))
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at ea eb
  simp only [left,right,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at order
  dsimp only [U,V,slack,left,right]
  simp only [crossLeft,ZT.toZ,Q.mk_add,Q.mk_mul,map_add,map_mul] at ea eb order ⊢
  linear_combination -(𝔞(denominatorOf a)*𝔞(denominatorOf b))*order
    +(𝔞(B)*𝔞(F)*𝔞(denominatorOf b))*ea
    -(𝔞(B)*𝔞(E)*𝔞(denominatorOf a))*eb

end LeanProofs.IPRA.Analysis.RationalRepresentedUpper
