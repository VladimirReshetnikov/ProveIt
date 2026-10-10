# Targeted corrections and status changes

This is a targeted audit of the inspected source, not an audit of all 228
pages or all historical reports. Source references are pinned in PROVENANCE.json.

## 1. Resolve the S4 conjecture

Source: `chapters/04-shuffle-parity.tex`, label `gaussian:conj:S4`.
The conjecture and its equivalent original-coordinate version are proved by
this continuation's exact certificate. Upgrade the environment and replace
the nearby statement that a functional-equation proof is absent. Update the
summary in `chapters/10-discovery.tex` accordingly.

This is a status upgrade, not a criticism of the earlier decision to mark a
numerically supported formula as conjectural.

## 2. Restrict the higher-weight non-reducibility wording

Source: `chapters/04-depth.tex`, Family 2 subsection following
`double:eq:fam2-example`, approximately source lines 410-415 at the pin.

The source's statement that at higher weight the antisymmetric parts do not
reduce against the `(i,1)` basis alone is too strong if read as mathematical
nonmembership rather than a report of unsuccessful searches. The present
weight-five mixed antisymmetric identity is a concrete qualification.

Proposed wording:

> The stated searches did not recover all higher-weight antisymmetric
> reductions in the restricted basket. This is a limitation of those
> searches, not a proof of nonmembership. In particular, the Cayley
> certificate gives the weight-five mixed reduction displayed below.

The new proved formula is

Im(Li_(4,1)(i,-1) - Li_(1,4)(-1,i))
= (102 g_(4,1) + 48 g_(3,2))/7 + 79 pi^5/10752 - 3 beta(4) log(2).

## 3. Preserve remaining cautions

The certificate does not prove minimal depth, period independence, or an
all-weight classification. The S6 formula has a certified tiny residual but
remains conjectural. The S8 numerical near-relation tested in this continuation
is false; it was generated here, not found as an erroneous identity in the
inspected repository.
