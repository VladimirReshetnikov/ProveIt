# Conditional 87-to-88 gamma model transfer

These are **unelaborated source-only drafts**, not checked all-model maps or
an iPRA endpoint. `GammaShifted88Graph` is generated from the exact 88
forced-J parent JSON; the separately generated 87 literal is its child with
the gamma increment removed. Both use the same compact natural port tuple.

`GammaNoExtraFacts` isolates gamma forcing from explicit natural first and
main norms, positive eta/zeta/X/U, q/Y and rank bounds, plus the **actual
no-E*q** main pair norm at gamma zero. Its separate `GammaDirectRankGap` uses explicit model order arithmetic to
derive `R+1<k` and `X<c` directly, with no abstract-model `omega`; it applies
`GammaZeroNarrowDraft.gamma_zero_impossible` with **R itself**, not
`R+X*Y*q`. The graph bridge must supply its rank, norms and signs.

`GammaPrototypePositiveEta` proposes those facts from an 85 prototype zero
with eta explicitly positive: it uses the proposed exact prototype J, X,
gap, compact window, natural norms, and actual main-pair sources. Its
`v12=0` norm is precisely the no-extra-term carrier. All these sources and
their model casts, factor-unit/positivity theorems and providers remain
unelaborated.

`Gamma87To88Transport` maps an 87 zero forward to 86 by increasing w, then
forward to 85 by increasing eta. The resulting eta is positive and the
original gamma coordinate is unchanged. The prototype gamma lemma then
proposes gamma>0 in the 87 zero, **without using either reverse eta map or
`ForcedEta`**. It constructs the 88-to-87 forward gamma increment and the
reverse predecessor map, and proposes a compact `SameNoZero`. The 87 bridge
still explicitly assumes `PolynomialBridge` for this exact 88 parent. The
85 native client additionally assumes all-model `ForcedEta`.

The arithmetic lemmas, generated literal evaluation, individual graph-zero
transfers, fixed-port model casts, compatible provider/axiom provenance,
earlier 88-to-endpoint bridge, file/PDF semantics and mapped ZFC endpoint
are not established by these drafts. The old residue-adjusted gamma client
has an extra `X*Y*q` term and is **not** used as the actual carrier theorem.

Run `python3 -I -S -B research/ordinary13-gamma87-to88-model-draft/check.py`
from `Computability/DiophantineConsistency` and compare with `receipt.json`.
The checker regenerates the literal in a temporary tree, checks graph edits,
source signatures and bounded valuation/rank inequalities; it does not run
Lean or prove arbitrary-model statements.
