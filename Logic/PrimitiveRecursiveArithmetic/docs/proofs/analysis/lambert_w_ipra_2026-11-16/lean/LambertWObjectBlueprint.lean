import ConciseIPRA.NativeBiInterpretation

/-!
# Lambert W: iPRA object-language blueprint

This file names the actual ProveIt interfaces inspected in
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA`:

* `PR`, `PTm`, and `PRAAx` from `PR.lean`;
* intuitionistic derivability `Prf` from `Deduction.lean`;
* quantifier-free induction `PRA.qfInd`;
* the native bridge `NFm.ofPRA` and `pra_iff_native`.

Every `sorry` below is a finite implementation/proof obligation, not an
additional axiom proposed for the object theory.
-/

namespace LeanProofs.ConciseIPRA
namespace LambertWIPRA

open Syn
open scoped Fm

/-! ## Primitive-recursive codes

The intended natural-number codes are:

* signed integers by sign and magnitude;
* reduced rationals by signed numerator and positive denominator;
* finite vectors by length plus a pairing code;
* rapid real names by an index of a primitive-recursive approximation function
  together with the code of a regularity derivation;
* truncated series by rational vectors.
-/

/-- Pairing and projection symbols. -/
def pairPR : PR 2 := by sorry

def leftPR : PR 1 := by sorry

def rightPR : PR 1 := by sorry

/-- Integer and rational arithmetic on the chosen codes. -/
def ratAddPR : PR 2 := by sorry

def ratMulPR : PR 2 := by sorry

def ratEqPR : PR 2 := by sorry

def ratLePR : PR 2 := by sorry

/-- Bounded folds used by every coefficient and interval algorithm. -/
def boundedSumPR : PR 2 := by sorry

def boundedAllPR : PR 2 := by sorry

/-- Factorial, signed powers, and the exact coefficient
`(-n)^(n-1)/n!` encoded as a rational. -/
def factorialPR : PR 1 := by sorry

def lambertCoeffPR : PR 1 := by sorry

/-- Cauchy multiplication, composition, derivative, and truncated exponential
on coded vectors. -/
def truncMulPR : PR 3 := by sorry

def truncCompPR : PR 3 := by sorry

def truncExpPR : PR 2 := by sorry

/-- One coefficient-stabilizing step `G ↦ X exp(-G)`. -/
def lambertStepPR : PR 2 := by sorry

/-- Iterate the preceding step a bounded number of times. -/
def lambertIterPR : PR 2 := by sorry

/-! ## Object-language formulas

The formula bodies are placeholders until the term notation for the selected
vector encoding is installed.  Their arities and intended meanings are fixed
here so that the proof graph is explicit.
-/

/-- `LambertInv(N,j)`: after `j` steps, all coefficients below `j` agree with
`(-n)^(n-1)/n!` and the defining equation holds below `j`. -/
def LambertInv : Fm PTm 2 := by sorry

/-- The invariant is quantifier-free because every equality is a bounded
Boolean fold over a coded finite vector. -/
theorem LambertInv_qf : LambertInv.QF := by sorry

/-- Base case for the coefficient stabilization induction. -/
theorem LambertInv_zero :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] LambertInv.subst (inst PTm.zero) := by sorry

/-- Successor step.  The context contains the induction hypothesis exactly as
required by `PRA.qfInd`. -/
theorem LambertInv_succ :
    LambertInv :: ([] : List (Fm PTm 1)).map Fm.shift ⊢[PRAAx]
      LambertInv.subst (repl (PTm.succ (Syn.var 0))) := by sorry

/-- Quantifier-free induction produces the universally quantified invariant.
This is the central object-theory proof shape. -/
theorem lambertInvariant_prf :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] Fm.all LambertInv := by
  exact PRA.qfInd LambertInv LambertInv_qf LambertInv_zero LambertInv_succ

/-- Closed formula expressing the coefficient theorem for a requested
truncation. -/
def LambertCoeffTheorem : Fm PTm 0 := by sorry

/-- Extract the closed coefficient theorem from the invariant using only
bounded arithmetic and intuitionistic natural-deduction rules. -/
theorem lambertCoeff_prf :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] LambertCoeffTheorem := by sorry

/-- Native-calculus image of the same proof.  This is a theorem obtained from
`pra_iff_native`, not a new assumption. -/
theorem lambertCoeff_native :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA LambertCoeffTheorem) := by
  simpa using (pra_iff_native.mp lambertCoeff_prf)

/-! ## Rapid-name branch search -/

/-- Formula saying a coded interval brackets the principal root at precision
`p`, lies in `[-1,∞)`, and has width at most `2^-p`. -/
def PrincipalBracket : Fm PTm 3 := by sorry

theorem PrincipalBracket_qf : PrincipalBracket.QF := by sorry

/-- Primitive-recursive bisection update. -/
def principalBisectPR : PR 3 := by sorry

/-- One-step preservation of the bracket invariant. -/
theorem principalBisect_preserves :
    ([] : List (Fm PTm 3)) ⊢[PRAAx]
      PrincipalBracket ⟶ PrincipalBracket.subst (fun i =>
        -- Replace by the term tuple containing `p+1`, the updated interval,
        -- and the unchanged input code.
        Syn.var i) := by sorry

/-- The universally quantified branch-search correctness theorem is again a
`PRA.qfInd` proof over the requested precision. -/
def PrincipalSearchCorrect : Fm PTm 1 := by sorry

theorem principalSearch_prf :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.all PrincipalSearchCorrect := by sorry

/-! ## Remaining modules

The same pattern is reused for:

* exponential/logarithm truncation and tail invariants;
* polynomial recurrence `P_{n+1}` for higher derivatives;
* finite Laurent-residue Lagrange inversion;
* Puiseux coefficient recursion;
* fixed-order asymptotic residual bounds;
* the finite inequalities proving every bound in Sections 11--12;
* Newton/Halley interval preservation and error bounds.

Only after an object-language derivation has been built should a native
statement be obtained via `pra_iff_native`; the bridge must never be used as a
substitute for the derivation.
-/

end LambertWIPRA
end LeanProofs.ConciseIPRA
