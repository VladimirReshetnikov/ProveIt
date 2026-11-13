# Independent review of reverse shear nonzero order draft

The stated nonzero argument is mathematically correct under its ordered-ring
hypotheses, and the cited auxiliary and output factors match the literal
72-row candidate. No concrete source-level defect was found. The proposed Lean
source is unelaborated; the zero equation and bounds have not been extracted
from the candidate in an arbitrary model.

There is a useful strengthening: **the hypothesis `0 <= A` is unnecessary**.
Suppose `I>=2`, `y>=1`, `rest>=0`, and the displayed sum equals 2. If
`V+y=0`, then the auxiliary factor is `A*y²`. We have `I²>=4` and
`y²>=1`. Split on `2<=A`:

- If `2<=A`, then `A>=0`, so `A*y²>=A>=2`. Its square is at
  least 4, impossible when the other two summands are nonnegative.
- If `A<2`, then `I²−A>2`; its square exceeds 4, giving the same
  contradiction independently of the sign of A.

This works in every linearly ordered commutative ring, without division or a
discreteness premise. The current source uses the stronger `0<=A` explicitly;
it was not changed by this review. The reduction would avoid a separate
positivity proof for Delta and `f²−1` at this step, while retaining `I>=2`,
`y>=1`, `rest>=0` and exact graph evaluation. For instance, weakening `I>=2`
to `I>=1` fails for the abstract lemma: `A=I=y=1`, `V=−1`, `rest=1`
satisfies the displayed equation and has `V+y=0`.

The review checks the candidate's exact I, A, auxiliary, strong residual and
sum/output rows, and independently expands the auxiliary identity over the
polynomial ring `Z[A,V,y]`. The checker also exercises 4,433 bounded integer
triples including negative A; finite tests are diagnostic, not a proof of the
ordered-ring statement or of Lean elaboration. The pinned earlier shear
identity is itself a source-only draft, so it is not an independently checked
Lean theorem.

In the intended model, positive `i`, `eta`, `zeta`, `s` and positive beta
provide `i>=1`, `Y>=1` and `c=(eta+zeta)Y+eta>=3`, hence `I=i*c²>=2`;
the actual signed/natural casts and this derivation must be supplied in the
same valuation as the graph zero. The rest is `P²+(QW−1)²`. A model-natural
positive representative of `|V+y|`, parent-coordinate replacement, source
and candidate evaluator identities, the forward map, and the final iPRA
bridge are all still required. This review proves no model or consistency
endpoint and does not authenticate Lean provider closure.

Reproduce both bounded receipts from `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear-ordinate-nonzero-order-draft/check.py | cmp - research/current2011-shear-ordinate-nonzero-order-draft/result.json
    timeout 30s python3 -I -S -B reviews/current2011-shear-ordinate-nonzero-order-independent/check.py | cmp - reviews/current2011-shear-ordinate-nonzero-order-independent/receipt.json

No Lean, build, staging, or modification of the reviewed draft was performed.
