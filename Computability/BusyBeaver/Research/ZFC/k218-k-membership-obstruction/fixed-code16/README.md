# Historical fixed-code16 search, now settled without QS

The three-value obstruction rejects native `I(F,F)=16`. This follow-up adds
only the constraint that this one formula is designated to the same exact
K + RAB + rho1–6/G/full-bundle matrix search. It does not assume all identities,
S, composition, EFQ, substitution, or quantified stability.

Three bounded stochastic runs tested carrier/designation counts 3/1, 4/1 and
5/2 for 12, 10 and 10 seconds. Their 16,553,000 proposal iterations found no
model. Every saved best table passes the original rows and fails only the new
fixed-identity condition. The independent finite [review](review.json) checks
that statement from the literal ASTs, without importing or invoking search code.

The search itself is a bounded negative diagnostic, not an exhaustive search
or a consistency proof. Repeated proposals are counted; the iteration total is
not a count of distinct algebras. The subsequent independently reviewed
[syntactic invariant](../identities/README.md) proves consistency even with
all identities, ruling out the intended calibration without QS. The search
records remain unchanged. No source-pricing run was needed; the further
extension with QS is outside this new invariant.

`fixed-identity.diff` is the exact one-constraint change from the earlier search.
Compile the source with `g++ -O3 -std=c++17 search.cpp -o SEARCH`; the three
invocations are `SEARCH 12 3 1 101`, `SEARCH 10 4 1 102`, and
`SEARCH 10 5 2 103`. Keep stdout/stderr in fresh files. The saved best tables can
be independently checked by copying this directory to a fresh location and
running `python3 -B review_results.py` there.
