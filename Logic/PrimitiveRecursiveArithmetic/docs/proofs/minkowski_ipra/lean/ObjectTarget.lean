import ConciseIPRA.BiInterpretation

/-!
# Actual first-order iPRA target, using the inspected ProveIt API

STATUS: uncompiled interface outline. This file defines a target formula and
proves only a conditional transport statement. It does not instantiate the
three PR definitions or supply their correctness derivation.

Pinned source repository: VladimirReshetnikov/ProveIt
Pinned commit: 329161f8da0b319d51ba9f6246c4b19d243f7193
Toolchain recorded there: leanprover/lean4:v4.32.0

Add ConciseIPRA's source directory to the Lean module search path, or place the
new files under the appropriate library target in a ProveIt checkout. Merely
copying this file next to a Mathlib installation does not supply ConciseIPRA.
-/

namespace MinkowskiIPRA.ObjectLevel

open LeanProofs.ConciseIPRA
open scoped LeanProofs.ConciseIPRA.Fm

/-- The symbols must be concrete finite PR syntax trees, not abstract oracles. -/
structure CertificateSymbols where
  valid : PR 1
  extract : PR 1
  good : PR 2

def one {n : Nat} : PTm n := PTm.succ PTm.zero

def unary {n : Nat} (f : PR 1) (x : PTm n) : PTm n :=
  PTm.app f (fun _ => x)

def binary {n : Nat} (f : PR 2) (x y : PTm n) : PTm n :=
  PTm.app f (Fin.cases x (fun _ => y))

/-- The free variable 0 is the complete finite certificate code. -/
def correctness (s : CertificateSymbols) : Fm PTm 1 :=
  let x : PTm 1 := PTm.var 0
  (unary s.valid x ≐ one) ⟶
    (binary s.good x (unary s.extract x) ≐ one)

/-- Correctness is genuinely quantifier-free; free variables are parameters. -/
theorem correctness_qf (s : CertificateSymbols) : (correctness s).QF := by
  exact ⟨True.intro, True.intro⟩

/-- Once the object proof exists, the repository transports it to the concise
scalar presentation. This conditional statement is not the missing proof. -/
theorem transport_to_concise (s : CertificateSymbols)
    (h : Prf PRAAx [] (correctness s)) :
    Prf TeqAx [] ((correctness s).map (fun _ => FromPRA.sigma)) :=
  (pra_theorem_iff (correctness s)).mp h

/-!
FINAL REQUIRED DECLARATION, intentionally not asserted here:

  def meshSymbols : CertificateSymbols := <explicit PR syntax trees>
  theorem meshCorrect : Prf PRAAx [] (correctness meshSymbols) :=
    <a derivation built from Prf constructors and PRA.qfInd>

For the main closed arithmetic theorem, instantiate these symbols with the
FIXED checker for rational symmetric slab bodies plus rational interior boxes.
The concrete `good` checker verifies the output indices, nonzero quotient
vector, exact scaled-difference identity, and rational slab membership. Use a separate symbol tuple for the
pure mesh lemma if that makes the first milestone smaller.

For the geometric theorem with an arbitrary represented K, use a fixed
primitive-recursive certificate relation for that representation, plus the
arithmetized symmetry/midpoint rules. There is no one total primitive-recursive
evaluator for arbitrary user-supplied PR programs. Uniformity is either over
finite certificates checked by this fixed checker, or schematic in each fixed
body representation and its certified soundness theorem.

Do not replace meshCorrect by a proof of its semantic interpretation over
Lean Nat. The type must literally be `Prf PRAAx [] ...` (or a transported
ConciseIPRA derivability judgment). General host Lean induction or mathlib
pigeonhole lemmas do not by themselves prove this restricted derivability.
-/

end MinkowskiIPRA.ObjectLevel
