# Independent internal review of the projection certificates

Prepared with AI assistance on 25 October 2026. This is an internal mathematical
and code review, not outside peer review or a proof-assistant certificate.

Reviewed file: `direct/code/verify_projection.py` in the integrating submission
(working path `work/direct_reduction/code/verify_projection.py`). The companion
replay receipt records the exact equation identities checked.

## Finding

The checker correctly verifies the finite algebra needed for its acyclic monic
substitutions, exact degree claims, coefficient-height upper bounds, and the
claim that every declared variable occurs in the final polynomial. A fresh
normal-mode replay accepted all eight supplied profiles and rejected the five
deliberately altered records for each profile.

The following mathematical points are sound.

1. Each pivot row is an authenticated source polynomial of the form
   epsilon*x+R, with epsilon=+1 or -1 and x absent from R. Recursive dependency
   resolution explicitly rejects cycles. The resulting definitions are integer
   polynomials, so both projection and restoration preserve integer zero sets.

2. The exact structural comparison imports the complete retained source graph,
   replaces the pivot coordinates by those integer polynomials, retains every
   unselected residual, and checks the final sum of squares. It does not infer
   an identity from numerical samples. The separate source-pooling construction
   and its semantic calibration remain dependencies of this verification.

3. Propagated circuit degrees are upper bounds even when some intermediate
   leading terms cancel. The propagated `top` value is the evaluation of the
   homogeneous component at that upper bound. A nonzero modular evaluation of
   one residual at the largest bound therefore proves that this residual has
   that exact degree. The modulus need not be prime for this implication.

4. The final sum of squares has twice the largest residual degree. This last
   inference uses the ordered field of real numbers: a nonzero sum of squares
   of real homogeneous polynomials cannot vanish identically. It does not rely
   on noncancellation modulo the chosen modulus. Thus the principal residual's
   degree 8482 proves exact final degree 16964.

5. The coefficient-height exponent is a conservative coefficient-l1 bound.
   For constants it bounds their absolute value by a power of two; multiplication
   adds exponents and addition/subtraction adds one to their maximum. Summing
   the squared residuals yields H <= 2^B. This is an upper bound, not the
   computed exact height of the fully expanded polynomial.

6. Reverse-mode differentiation of the exact arithmetic graph modulo an integer
   computes the actual partial derivatives at the supplied integer point. A
   nonzero residue for each partial derivative proves that every declared
   variable occurs nontrivially in the collected polynomial. Graph liveness
   alone would not establish this stronger assertion.

During review, strict integer type checks for the certificate points and an
explicit unrestricted-integer domain check were recommended. The author added
them, together with gradient type validation. The recorded replay uses the
hardened checker.

## Provenance and logical boundary

Artifact hashes identify bytes; a hash copied from a mutable input does not by
itself authenticate that input's origin. The integrating release must retain
its independent pinned-source ledger and check the parent/joint-source hashes
against that ledger. This was communicated to the author, who reports that
the release verifier includes fixed source bindings.

The finite checks do not establish the inherited Pell classification,
orientation/power-pooling theorem, C222-to-ZF calibration, or the internalized
ZF-to-ZFC refutation equivalence. Those remain the named ordinary and formal
mathematical inputs. In particular, these checks neither exhibit a refutation
nor prove Con(ZFC).
