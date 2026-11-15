import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# The actual first-order iPRA proof obligation

STATUS: UNCOMPILED BLUEPRINT. API names below were read from ProveIt commit
329161f8da0b319d51ba9f6246c4b19d243f7193. The checker compilation and the
isoperimetric derivation have NOT been supplied by this file.

The argument `checkCode : PR 3` is required to be the explicit compilation of
`IsoperimetricIPRA.Codec.checkNat`, with all its defining equations proved.
An arbitrary or constantly-zero code is not a valid implementation of that
requirement. Keeping the parameter visible avoids disguising that missing
work as an axiom or a finished theorem.
-/

namespace LeanProofs.ConciseIPRA.Isoperimetric

/-- Under `forall p, forall u, forall k`, de Bruijn indices 2,1,0 denote
the polygon code, upper-length code, and precision respectively. -/
def checkerArguments : Fin 3 → PTm 3 :=
  Fin.cases (PTm.var 2)
    (Fin.cases (PTm.var 1) (fun _ => PTm.var 0))

def finiteMatrix (checkCode : PR 3) : Fm PTm 3 :=
  Fm.eq (PTm.app checkCode checkerArguments) PTm.zero

/-- Exact shape of the intended closed internal arithmetic theorem:
`forall p, forall u, forall k, checkNat(p,u,k) = 0`.
Invalid input is accepted by the total checker, so the usual hypotheses
are incorporated in this equation without changing its logical meaning. -/
def finiteFormula (checkCode : PR 3) : Fm PTm 0 :=
  Fm.all (Fm.all (Fm.all (finiteMatrix checkCode)))

/-- The main completion criterion. This is only a definition of a proposition;
no inhabitant of it is claimed or constructed in this blueprint. -/
def InternalProofTarget (checkCode : PR 3) : Prop :=
  Prf PRAAx [] (finiteFormula checkCode)

/-- Once the internal iPRA proof has been supplied, the existing repository
bridge transfers it to the concise native calculus. The premise is the entire
uncompleted mathematical task; this small bridge is not that proof. -/
theorem transferToNative (checkCode : PR 3)
    (h : InternalProofTarget checkCode) :
    NPrf [] (NFm.ofPRA (finiteFormula checkCode)) :=
  (pra_iff_native).mp h

/- Required construction of `InternalProofTarget checkCode`:

1. Compile rational codecs, bounded scans, sums/products, sqrtDown, piLower,
   and checkNat into fixed PR symbols, using the constructors of `PR`.
2. Prove their defining and order laws as derivations `Prf PRAAx ...`, using
   `PRA.qfInd` only on formulas whose `Fm.QF` witnesses have been constructed.
3. Prove finite ring identities and inequalities after clearing positive
   denominators. Replace each bounded universal condition by its PR Boolean
   conjunction before induction; do not use full first-order induction.
4. Formalize the finite ordered radical tower, root-of-unity orthogonality,
   finite DFT area/energy identity, and the signed mode bounds.
5. Formalize exact rational subdivision and the explicit error budget.
6. Obtain the matrix equation and apply the constructor `Prf.allI` three
   times to reach `finiteFormula checkCode`.

For a represented-curve corollary use a SCHEMA with fixed PR polygon,
upper-length, and modulus symbols. No uniform PR evaluator of arbitrary PR
programs is available. The proof of convergence is expressed as explicit
precision inequalities, not existence of an arbitrary real-number limit.
-/

end LeanProofs.ConciseIPRA.Isoperimetric
