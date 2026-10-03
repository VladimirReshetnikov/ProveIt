# Independent review of the local three-query beta batch

**PASS, no requested author change.** I read the complete frozen
[source](eager_tree_beta_three_query_sharing.py),
[receipt](eager_tree_beta_three_query_sharing.json), and
[proof](eager_tree_beta_three_query_sharing.md). The independent
[checker](review_eager_tree_beta_three_query_sharing.py) and
[receipt](review_eager_tree_beta_three_query_sharing.json) authenticate:

| Author artifact | SHA-256 |
|---|---|
| Python | `498a9924f743905033be5e93a492ddf58b4cbbcf0c541f17a174690657fbf8b0` |
| JSON | `e5af329a782aab92b31da1ea2023e6e6965dc7ebd8ccb4ff71a78a6062ac7dc7` |
| Markdown | `8ad5dfc4c20ca4116da16dd6136a61133af7e8088f77dbb6e03a10a9fa9026dd` |

The frozen single-query parent trio is separately pinned. The reviewer
loads the current helper directly from authenticated source bytes only to
exercise its public API. It does not invoke author `verify` or execute any
historical compiler. Independent code constructs both literal baselines
from the saved parent sources, reconstructs both shared schedules, expands
all coefficients using exponent vectors, and checks closure, liveness,
full ledgers and metadata. The coefficient engine is reused from my own
single-query review; no external review helper is imported at runtime.

This review concerns the complete local batch source, not a full Tree
certificate or fixed-arity universal compiler. The targets and active
expressions are supplied scalar ports except for the explicitly charged
`t3+t4` operation in computed-active mode. Both modes retain twelve natural
witnesses, four per suffix query.

For slot `j`, let `S_j` be the frozen parent's ungated sum of three squared
residuals. The naive batch is

\[
aS_0+aS_1+t_3S_2.
\]

The successor computes `I=i+2` once, uses `I+h_j` in each atom, and returns

\[
a(S_0+S_1)+t_3S_2.
\]

Associativity of addition gives the same queried index in each slot.
Distributivity gives the exact complete all-value polynomial identity; no
tag, range, zero, or positivity equation is used to justify sharing.
Replacing the two independent guards by one saves one multiplication.
Sharing the common `i+2` saves two additions. The sum of three parent gated
atoms includes two accumulator additions and costs `53=18M+35A`; the child
costs `50=17M+33A`. Computing `a=t3+t4` costs one further addition in both
schedules, making `54` and `51` respectively. All fixed numeral operations
and the complete local finalizer are charged.

The supplied-active leader is

\[
b^2\bigl(aq_0^2(i+h_0)^2+aq_1^2(i+h_1)^2
+t_3q_2^2(i+h_2)^2\bigr).
\]

Computed-active mode substitutes `t3+t4` for `a`. Both are nonzero of degree
seven; setting every supplied coordinate and witness to one indeterminate
gives leading coefficients twelve and twenty respectively. These are local
degrees in independent scalar ports. Substitution of computed Tree targets
requires separate degree propagation.

Each `S_j` is nonnegative on natural assignments. Thus the shared batch
vanishes exactly when each query with a positive active coefficient has a
natural suffix-membership witness. Inactive slots admit arbitrary natural
local witnesses. The complete polynomial identity is valid on signed and
rational assignments too; the remainder-membership theorem remains a
natural-integer statement. Neither sign freedom nor a fractional quotient
may be imported into that interpretation.

The frozen parent's missing-coherence obstruction remains relevant:
consistent decoding of every row and its code, the bounded-universal row
compilation, all target circuits, and ordinary input loading must still be
paid. This local sharing result does not claim those obligations are met.


The two source-specific fifteen-gate counterexamples are accurate. Replacing
`i+h` by an independent `H` admits the reported empty-suffix zero with
`H-i=-1`. Replacing `D+s` by independent `S` admits a noncanonical remainder
with `S-D=-1`. I reconstructed both complete altered local sources from the
parent, checked their natural assignments and complete polynomial zeros,
and independently checked that no suffix member exists. These failures
establish neither a local arithmetic lower bound nor impossibility of
another coordinate change.

Current canonical APIs reject inexact Boolean options, malformed complete
packets, changed source or metadata, wrong coordinate containers, missing
or surplus fields, Boolean/floating/rational coordinates, and negative
coordinates in natural mode. Signed integer mode remains available. All
three parent pins are rechecked on warmed calls, including the parent
accessor and current evaluator. Returned source and metadata containers are
independent. The public `authenticate` helper itself reads and checks each
pin; its extra warm rejection was also tested. Optimized Python is rejected
at module entry.

The independent receipt passes four entire literal source reconstructions
(two baselines and two children), two complete polynomial identities,
eighteen query-residual identities, both exact highest homogeneous forms,
and all 208 paid live gates across these four forms. It records 48 complete
numeric identities including eight rational assignments, 24 natural zero
identity maps, six inactive empty-suffix zeros, both fifteen-gate false
zeros, 58 malformed-call rejections including 15 warm-pin rejections,
nine defensive-copy checks, and optimized-Python rejection. Finite tests
supplement the full symbolic identities and natural-domain proof.

Standard-library replay from any working directory:

```sh
python /path/review_eager_tree_beta_three_query_sharing.py \
  --root /path/to/single-query-parent-trio \
  --artifacts /path/to/batch-author-trio \
  --expect /path/review_eager_tree_beta_three_query_sharing.json
```

Both directories default to the review helper's directory and may be the
same installed research directory. `--output FILE` writes a deterministic
receipt; `--expect` compares the complete JSON data recursively with exact
types. No broader Tree source, historical suite or Lean build is replayed.
