import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Addition of signed one-sided rational bounds

The bound on an actual sum keeps both input error budgets at their
independent denominators. The proof uses the signed, represented
inequalities and the actual normalization law of rational addition.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalUpperAddition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper)
open RationalArithmetic (add add_value addNumerator productDenominator product_denominator_positive)
open RationalRepresentedUpper (left right to_signed from_signed)
open PolynomialBisection (slack)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem add_upper (a b c d A B C D : PTm n)
    (h : Γ ⊢[PRAAx] upper a b A B) (k : Γ ⊢[PRAAx] upper c d C D) :
    Γ ⊢[PRAAx] upper (add a c) (add b d) (A*D+C*B) (B*D) := by
  let P := denominatorOf a
  let Qr := denominatorOf b
  let S := denominatorOf c
  let T := denominatorOf d
  let x := numeratorOf a
  let y := numeratorOf b
  let u := numeratorOf c
  let v := numeratorOf d
  have leftBound := to_signed a b x y P Qr A B
    (RationalRepresentations.represents_self a) (RationalRepresentations.represents_self b) h
  have rightBound := to_signed c d u v S T C D
    (RationalRepresentations.represents_self c) (RationalRepresentations.represents_self d) k
  have l := zle_toZ leftBound
  have r := zle_toZ rightBound
  apply from_signed (add a c) (add b d) (addNumerator a c) (addNumerator b d)
    (productDenominator a c) (productDenominator b d) (A*D+C*B) (B*D)
    (product_denominator_positive a c) (product_denominator_positive b d)
    (add_value a c) (add_value b d)
  apply zle_of_toZ (S*T*D*slack (left x Qr B) (right y P Qr A B) +
    P*Qr*B*slack (left u T D) (right v S T C D))
  dsimp only [P,Qr,S,T,x,y,u,v] at l r ⊢
  simp only [left,right,slack,addNumerator,productDenominator,ZT.toZ_add,ZT.toZ_mul,
    ZT.toZ_ofNat,Q.mk_mul,map_mul,Q.mk_add,map_add] at l r ⊢
  linear_combination (𝔞(denominatorOf c)*𝔞(denominatorOf d)*𝔞(D))*l+
    (𝔞(denominatorOf a)*𝔞(denominatorOf b)*𝔞(B))*r

end LeanProofs.IPRA.Analysis.RationalUpperAddition
