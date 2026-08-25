import FabiusFunction.Paper06487Supplement

/-!
# *Arithmetic of the Fabius function* (arXiv:1702.06487v3)

This is the public import for Juan Arias de Reyna's
*Arithmetic of the Fabius function*.

`FabiusFunction.PaperStatements` contains proved Lean statements for every
numbered proposition, theorem, and lemma in the paper, together with its
numbered question, definition, and conjecture.  The supplement imported here
also exposes the mathematical assertions made in the surrounding prose and
inside proofs.

In particular, the public import provides:

* analytic facts about the support, sign, derivatives, fold identities, and
  exact power-of-two flat points of Rvachev's and Fabius's functions;
* the exact integrality, oddness, divisibility, and two-adic assertions used in
  the arithmetic arguments;
* both orders of summation in the finite dyadic-value formula; and
* the denominator formulas implied by Conjecture 16.

The formalization documents and corrects the few statements that are not
literally valid as printed, most notably the missing order condition in
Lemma 1, the removable singularity in Proposition 2, and the missing factor of
two in a proof-internal sentence in Theorem 20.
-/
