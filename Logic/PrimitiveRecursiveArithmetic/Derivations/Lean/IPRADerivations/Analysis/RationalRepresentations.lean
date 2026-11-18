import IPRADerivations.Analysis.RationalArithmetic
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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArithmetic
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

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
  apply ZT.derive
  have ec := ZT.toZ_eq hc
  have ed := ZT.toZ_eq hd
  have ea := ZT.toZ_eq (add_value (Γ := Γ) c d)
  simp only [represents,productDenominator,addNumerator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at ec ed ea ⊢
  ipra_simps
  linear_combination
    𝔞(B)*𝔞(denominatorOf d)*𝔞(denominatorOf (add c d))*ec+
    𝔞(A)*𝔞(denominatorOf c)*𝔞(denominatorOf (add c d))*ed+
    𝔞(A)*𝔞(B)*ea

theorem represents_multiply (c d : PTm n) (a b : ZT n) (A B : PTm n)
    (hc : Γ ⊢[PRAAx] represents c a A) (hd : Γ ⊢[PRAAx] represents d b B) :
    Γ ⊢[PRAAx] represents (multiply c d) (a*b) (A*B) := by
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (productDenominator c d) _ _
    (product_denominator_positive c d)
  apply ZT.derive
  have ec := ZT.toZ_eq hc
  have ed := ZT.toZ_eq hd
  have em := ZT.toZ_eq (multiply_value (Γ := Γ) c d)
  simp only [represents,productDenominator,ZT.toZ_mul,ZT.toZ_ofNat] at ec ed em ⊢
  ipra_simps
  linear_combination
    ZT.toZ Γ b*𝔞(denominatorOf d)*𝔞(denominatorOf (multiply c d))*ec+
    ZT.toZ Γ (numeratorOf c)*𝔞(A)*𝔞(denominatorOf (multiply c d))*ed+
    𝔞(A)*𝔞(B)*em

theorem represents_negative (c : PTm n) (a : ZT n) (A : PTm n)
    (hc : Γ ⊢[PRAAx] represents c a A) :
    Γ ⊢[PRAAx] represents (negative c) (-a) A := by
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (denominatorOf c) _ _
    (RationalArgmin.denominator_positive c)
  apply ZT.derive
  have ec := ZT.toZ_eq hc
  have en := ZT.toZ_eq (negative_value (Γ := Γ) c)
  simp only [represents,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat] at ec en ⊢
  linear_combination -𝔞(denominatorOf (negative c))*ec+𝔞(A)*en

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
