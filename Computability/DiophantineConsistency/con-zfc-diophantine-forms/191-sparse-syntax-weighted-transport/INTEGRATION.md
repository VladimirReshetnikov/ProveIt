# Suggested ProveIt integration

This is an additive proposal against snapshot
`d123610bc98fef2006bff1c9466bc3f1221003e7`. No repository changes were pushed.

The archive can first be placed in `docs/incoming`. After review, extract it
to a newly assigned numbered package under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms`.
Do not assume a next number: the current snapshot already contains packages
through 178 and seven incoming proposals.

Suggested package label: **sparse-syntax-weighted-transport**.

## Proposed comparison entries

1. **Direct sparse C222:** unrestricted integers, 208 variables, 148 quadratic
   rows, exact degree 4, 5,987 collected monomials, height 2^44, row height
   2^22. Parent comparison: incoming Pell Growth 210, 210 variables, 150
   rows, 5,282 monomials, height 2^40.
2. **Positive weighted free chart:** ten strictly positive variables, exact
   degree 190, 120 binary operations (75 multiplications, 24 additions,
   21 subtractions). Parent comparisons: incoming 10/206/90 and package
   178's 10/208/116. Preserve the whole BFS943/radix67 coefficient tuple.
3. **Isolated affine-horizon companion:** 209 integer variables, 149 rows,
   degree 4. The minimum-2 profile has 5,486 monomials and height 2^44.
   The minimum-8 and minimum-16 variants are included for exact comparison.

The first and second entries belong to different domain and objective
columns. A lower integer dimension is not a smaller positive-variable count;
an operation count is not a bit-complexity bound. Avoid claims of global
minimality, a worldwide record, or completed formal-kernel verification.

## Review priorities

- The sparse recoding theorem uses a substitution tailored to each finite
  proof. It does not assert a global injection of all sparse numerals into
  the old zero-generated algebra.
- The sparse constructor bound is 16-based, and the growth Pell center is
  8t+1. The new local CRT exponent bound is proved independently.
- The affine horizon t=2+4z is initially signed. The power interfaces recover
  positivity before the standalone growth norm is classified.
- The compact soundness argument allows auxiliary Pell index three. Its new
  weight b^2 U E is justified before the sign of B is recovered.
- The logical calibrations remain the named inherited interfaces. The new
  source and algebra checks do not by themselves verify those unbounded
  logical theorems.

## Reproduction

Run both documented modes of `verify_all.py` before accepting an edit. The
PDF and residual appendix must correspond to the same literal equation as
the machine-readable data. If any coefficient or graph row changes, update
the proof, degree/profile claims, exact certificates, receipts, and release
manifest together.

The immediate Pell Growth parent is retained byte for byte for review
convenience. It may be deduplicated during repository integration if all
source paths and hash bindings are updated coherently and its exact input
bytes remain available.
