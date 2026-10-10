# Integral distribution coordinates and primitive-grid torsion

This research package supplements the ProveIt polylogarithm manuscript at
commit `cc34f73596336f2466d9754cb0f3635bd2bedade`.

## Main results

1. An explicit actual-grid basis for the weighted distribution quotient over
   every commutative coefficient ring, including nonreduced rings and finite
   characteristics. A finite filtered Anderson-type complex proves freeness
   and resolves all relations. The broad freeness/resolution principle is
   attributed to Kubert, Anderson, and Ouyang; no global novelty is asserted.
2. The integral primitive-grid determinant is exactly the manuscript's
   character determinant up to sign, so it gives the actual lattice index.
3. At a product of two distinct primes, a complete presentation of the
   primitive-grid cokernel over an arbitrary coefficient ring: direct cyclic
   summands plus a triangular three-generator core.
4. Explicit Smith factors, ordinary-weight torsion, modular primitive ranks,
   and the sharp least common denominator of all primitive reduction
   coefficients. These are the principal concrete additional results here.
5. Explicit nonsingular level-fifteen Hurwitz identities at spectral order
   two. The exact common denominator is 511680, versus the preceding product
   bound 4093440, and the nontrivial Smith factors are 2, 4, 511680.

## Files

- `../../sections/05-integral-distribution.tex`: publication-ready proof section, without
  preamble, including all definitions, full proofs, examples, attribution,
  further questions, and suggested bibliography entries.
- `integral_distribution.py`: exact integral polynomial normal form and
  presentation matrices; no character arithmetic is used.
- `verify_integral_distribution.py`: reproducible exact certificate checks and
  an independent numerical Hurwitz check.
- `verification_report.json`: detailed successful verification record.
- `verification_summary.json`: concise verification counts and explicit examples.

Run with Python 3.10+ and installed `sympy` and `mpmath`:

```sh
python verify_integral_distribution.py
```

The verified environment used Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0;
exact installed versions are also recorded in the detailed JSON. Checks cover
59 complete symbolic grid normal forms, 19 symbolic integral determinants,
112 finite-characteristic resolutions, and 504 complete two-prime Smith
specializations, including vanishing weights and singular ordinary weights.
All three displayed level-fifteen coefficient tuples are checked exactly.

## Integration cautions

- The whole formal distribution quotient remains free; the torsion results
  concern the quotient by the *primitive-grid image*, not torsion in the full
  module.
- Ordinary weights `t_p=1` correspond to Hurwitz spectral order zero or
  polylogarithm spectral order one. They do **not** mean Hurwitz spectral
  order one, whose weights are `t_p=p`.
- The parameter `h_p` in the two-prime section means `ord_p(ell)`, with `p`
  identifying the residual layer. This differs from the manuscript's
  determinant-section indexing `ord_(q/p^e)(p)`. Definitions are explicit;
  rename if integrating alongside that section.
- At a spectral pole, polynomial coefficients and zeta values must be
  combined meromorphically before specialization. The main order-two example
  avoids this issue entirely.
- The theorems concern formal integral lattices and finite presentation
  modules. They do not establish arithmetic independence of evaluated
  special-function values.
- The basis proof and two-prime core were independently reviewed by another
  research agent. Full algebraic proofs, not the finite checks, justify the
  all-level/all-ring statements.
