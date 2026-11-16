import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language targets for Meijer G in ProveIt

This file is an integration blueprint for repository commit
`85afffc93b2abbc1972fdfc98244052cbfbda1b3`.  It deliberately contains no
analytic theorem declaration: the graph predicates and PR symbols first have
to be implemented in the target repository.

The endpoint for every main theorem is an explicit derivation

    [] ⊢[PRAAx] phi

inside `LeanProofs.ConciseIPRA`.  Only after such a derivation exists may
`pra_iff_native` be used to transfer it to the native scalar core.

Suggested target formulas (schematic names):

1. Hypergeometric term recurrence

    forall k, Den(spec,k) * Term(spec,k+1)
      = Num(spec,k) * Term(spec,k).

2. Ratio-tail soundness

    forall p, RatioCert(spec,p) ->
      BallEq(HyperEval(spec,p+guard), HyperLimit(spec), p).

3. Slater right/left

    forall z p, RightAdmissible(spec,z,p) ->
      BallEq(MeijerRight(spec,z,p+guard), SlaterRight(spec,z,p+guard), p).

4. Laurent-jet residue

    forall pole p, JetCert(spec,pole,p) ->
      BallEq(ResidueEval(spec,pole,p+guard), JetResidue(spec,pole,p+guard), p).

5. Contour/residue agreement

    forall z p, ContourSafe(spec,z,p) ->
      BallEq(MeijerContour(spec,z,p+guard), MeijerResidues(spec,z,p+guard), p).

6. Differential equation

    forall z p, ODESafe(spec,z,p) ->
      BallEq(MeijerODELeft(spec,z,p+guard),
             MeijerODERight(spec,z,p+guard), p).

7. Parameter identities

    PowerShift, Inversion, CancelTopBottom, IntegerBlockMove,
    ParameterMultiplication, FirstDerivative, HigherDerivative.

8. Integral identities

    MellinCert(C,u,p) -> BallEq(MellinEval(...), GammaRatio(...),p)
    FubiniCert(C,...) -> BallEq(Euler/Laplace/Convolution lhs,rhs,p)
    RationalPowerCert(C,A,B,...) -> BallEq(ProductIntegral(...), MeijerG(...),p).

9. Transform pairs

    KernelCert(T,k,h,p) -> BallEq(InverseWindow(ForwardWindow(f)), f, p)
    WhittakerCert(...) -> BallEq(WhittakerKernel(...), MeijerKernel(...), p).

10. Special cases

    SafeCos(x,p) -> BallEq(sqrtPi*MeijerCos(x*x/4), CosEval(x),p)
    SafeLog(z,p) -> BallEq(MeijerLog(z), Log1pEval(z),p)
    SafeBessel(...) -> ...
    SafeLerch(...) -> ...

Implementation notes:

* Define every evaluator and predicate by `PR.zero`, `PR.succ`, `PR.proj`,
  `PR.comp`, and `PR.prec`.
* Use `PRA.qfInd` for finite loops and error telescopes.
* Reuse checked bounded sums, products, division-with-remainder, pairing, and
  simultaneous recursion from `IPRADerivations`.
* Never make a quotient identity primary.  Prove a cross-multiplied equality,
  then use an apartness theorem.
* No `axiom`, `sorry`, `admit`, `Classical.choice`, or `native_decide` may occur
  in the trusted dependency graph.
* Host-level numerical checks are not substitutes for these derivations.
-/

namespace LeanProofs.ConciseIPRA

-- This namespace is intentionally empty until the PR graph predicates have
-- been integrated.  Keeping the exact imports here checks the intended bridge
-- names when the file is placed in the ProveIt workspace.

end LeanProofs.ConciseIPRA
