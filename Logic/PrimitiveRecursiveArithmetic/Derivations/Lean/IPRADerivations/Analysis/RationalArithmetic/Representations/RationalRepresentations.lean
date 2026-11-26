import IPRADerivations.Analysis.RationalArithmetic.RationalArithmetic
import IPRADerivations.DiophantineNumberTheory.MinkowskiCenters

/-!
# Composition of rational cross-value representations

Actual canonical scalar operations preserve arbitrary supplied raw fraction
representatives. The input codes keep their own decoded positive denominators;
only their product is canceled in the object theory. The alternative raw
numerators and denominators are internal inputs, and no output value law is
a premise. These lemmas support rational Horner evaluation and slab linearity.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalRepresentations

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArithmetic

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem represents_self (c : PTm n) : Γ ⊢[PRAAx]
    represents c (numeratorOf c) (denominatorOf c) := by
  exact .eqRefl _

theorem represents_add (c d : PTm n) (a b : ZT n) (A B : PTm n)
    (hc : Γ ⊢[PRAAx] represents c a A) (hd : Γ ⊢[PRAAx] represents d b B) :
    Γ ⊢[PRAAx] represents (add c d) (a*ZT.ofNat B+b*ZT.ofNat A) (A*B) := by
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (productDenominator c d) _ _
    (product_denominator_positive c d)
  ipra_lc [represents, productDenominator, addNumerator] 𝔞(B)*𝔞(denominatorOf d)*𝔞(denominatorOf (add c d))*ZT.toZ_eq hc+ 𝔞(A)*𝔞(denominatorOf c)*𝔞(denominatorOf (add c d))*ZT.toZ_eq hd+ 𝔞(A)*𝔞(B)*ZT.toZ_eq (add_value (Γ := Γ) c d)

theorem represents_multiply (c d : PTm n) (a b : ZT n) (A B : PTm n)
    (hc : Γ ⊢[PRAAx] represents c a A) (hd : Γ ⊢[PRAAx] represents d b B) :
    Γ ⊢[PRAAx] represents (multiply c d) (a*b) (A*B) := by
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (productDenominator c d) _ _
    (product_denominator_positive c d)
  ipra_lc [represents, productDenominator] ZT.toZ Γ b*𝔞(denominatorOf d)*𝔞(denominatorOf (multiply c d))*ZT.toZ_eq hc+ ZT.toZ Γ (numeratorOf c)*𝔞(A)*𝔞(denominatorOf (multiply c d))*ZT.toZ_eq hd+ 𝔞(A)*𝔞(B)*ZT.toZ_eq (multiply_value (Γ := Γ) c d)

theorem represents_negative (c : PTm n) (a : ZT n) (A : PTm n)
    (hc : Γ ⊢[PRAAx] represents c a A) :
    Γ ⊢[PRAAx] represents (negative c) (-a) A := by
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (denominatorOf c) _ _
    (RationalArgmin.denominator_positive c)
  ipra_lc [represents] -𝔞(denominatorOf (negative c))*ZT.toZ_eq hc+𝔞(A)*ZT.toZ_eq (negative_value (Γ := Γ) c)

theorem representation_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (represents (var 0) (⟨var 2,var 3⟩ : ZT 8) (var 6) ⟶
      represents (var 1) (⟨var 4,var 5⟩ : ZT 8) (var 7) ⟶
        (represents (add (var 0) (var 1))
          ((⟨var 2,var 3⟩ : ZT 8)*ZT.ofNat (var 7)+(⟨var 4,var 5⟩ : ZT 8)*ZT.ofNat (var 6)) (var 6*var 7) ⋏
          (represents (multiply (var 0) (var 1)) ((⟨var 2,var 3⟩ : ZT 8)*(⟨var 4,var 5⟩ : ZT 8)) (var 6*var 7) ⋏
            represents (negative (var 0)) (-(⟨var 2,var 3⟩ : ZT 8)) (var 6)))) :=
  closeUniv 8 (.impI (.impI (.andI (represents_add _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)
    (.andI (represents_multiply _ _ _ _ _ _ Prf.hyp1 Prf.hyp0) (represents_negative _ _ _ Prf.hyp1)))))

end LeanProofs.IPRA.Analysis.RationalRepresentations
