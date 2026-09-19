# Proof audit

This records the checks made while preparing the note. It is not an
independent referee report or a proof-assistant certificate.

## Main chain of obligations

1. **Exact density accounting.** The column counts are differences of counts
   of multiples of successive powers of two. The tail has prefix count
   `floor(N/2^K)`. This is a bound for every prefix, not just selected endpoints.

2. **Description decoding.** Within each fixed positive-density column, a
   density-zero global error set occupies relative density zero. The column
   majority therefore converges to the coded bit. Extracting its limit uses
   the description's jump, not the description alone.

3. **Description production.** A pointwise-convergent oracle-computable array
   gives finitely many errors in each fixed column. The errors in the first
   K columns have finite total M_K. Remaining errors have prefix density
   at most 2^-K. No unjustified countable-union inference is used.

4. **Exact representative spectrum.** Computing a description gives only an
   upper bound on its degree. Encoding the desired oracle at powers of two
   preserves density agreement and realizes precisely that oracle's degree.

5. **Condition semantics.** Frozen values apply only AFTER the current stem.
   Newly freezing a column never overwrites or rejects old stem errors.
   Compatible stem extension followed by further freezing gives inclusion
   of allowed infinite-output classes.

6. **Product dichotomy.** Existence of a cross disagreement is an ordinary
   c.e. question in finite conditions. In the no-disagreement case, if the
   final common function is total, searching for a left finite computation
   gives an ordinary total program for it. The matching right computation
   certifies the answer. Totality is used in the verification, not decided
   during the construction.

7. **Oracle accounting.** Frozen words contain finitely many bits of A.
   Once recorded, these are ordinary finite parameters. The construction
   decides the corresponding c.e. searches with 0', not A'. It never asks
   whether a string satisfies all future A-dependent restraints.

8. **Jump control.** Each diagonal halting question is decided at a stage.
   A positive answer is forced by a finite initial segment; a negative one
   persists under shrinking the allowed class. Thus the records compute
   the output jump in A join 0'. The reverse reduction comes from the
   description criterion together with 0' below every jump.

9. **No least degree.** The class has no computable member but contains the
   two constructed representatives with trivial common Turing lower cone.
   A least member would have to be computable. The distinction between a
   least degree and a minimal degree is preserved.

10. **Uniform order classification.** The intermediate jump decoder is
    compiled via the uniform relative limit lemma into an approximation
    computable from the input description itself. The final coarse
    reduction is not mistakenly granted a jump oracle.

11. **Effective-dense boundary.** A non-erased answer on each column recovers
    the coded bit without taking a limit. For sparse replacement, explicit
    erasure of the computable support gives both translations. Arbitrary
    density-zero replacements are not asserted to preserve effective-dense
    equivalence.

## Quantifier and scope checks

- Turing minimal pair, not a minimal pair of coarse degrees: the two outputs
  have the SAME nonzero coarse degree.
- The least-representative obstruction covers total numerical functions via
  their graph degrees, not only binary functions.
- The high spectrum is unrestricted: no bound by 0' is imposed on its members.
- Noncomputability of the constructed pair is asserted when A is not <= 0'.
- The countable schedule meets each pair requirement and every individual
  jump requirement, while freezing all columns for every output.
- No assertion that the spectrum has no minimal element is made.
- C2 and the metric questions remain outside this result.

## Finite checks versus proof

The executable checks cover finite combinatorics and a finite-query oracle
model. They do not decide actual halting, construct the infinite oracles,
prove the limit lemma, or establish the infinite minimal-pair conclusion.
The conventional proofs in the article carry those obligations. No Lean
formalization or independent expert review is claimed.
