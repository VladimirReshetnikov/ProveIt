# Adding the single fixed axiom code 16 remains open

The three-value obstruction rejects native `I(F,F)=16`. This follow-up adds
only the constraint that this one formula is designated to the same exact
K + RAB + rho1–6/G/full-bundle matrix search. It does not assume all identities,
S, composition, EFQ, substitution, or quantified stability.

Three bounded stochastic runs tested carrier/designation counts 3/1, 4/1 and
5/2 for 12, 10 and 10 seconds. Their 16,553,000 proposal iterations found no
model. Every saved best table passes the original rows and fails only the new
fixed-identity condition. The independent finite [review](review.json) checks
that statement from the literal ASTs, without importing or invoking search code.

This is a bounded negative diagnostic, not an exhaustive search, a calibration,
or a consistency/inconsistency proof of the extension. Repeated proposals are
counted; the iteration total is not a count of distinct algebras. Both logical
strength and machine-source cost of the extra fixed axiom remain open.

`fixed-identity.diff` is the exact one-constraint change from the earlier search.
Compile the source with `g++ -O3 -std=c++17 search.cpp -o SEARCH`; the three
invocations are `SEARCH 12 3 1 101`, `SEARCH 10 4 1 102`, and
`SEARCH 10 5 2 103`. Keep stdout/stderr in fresh files. The saved best tables can
be independently checked by copying this directory to a fresh location and
running `python3 -B review_results.py` there.
