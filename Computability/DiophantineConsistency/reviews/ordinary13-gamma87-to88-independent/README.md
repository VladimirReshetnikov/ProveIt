# Independent review: gamma 87-to-88 source transfer

The pinned packet `research/ordinary13-gamma87-to88-model-draft/` is an
unelaborated source proposal. Its own checker reproduces. This review adds a
separate pinned source receipt, exact 88→87→86→85 row substitutions, the
no-extra-term main carrier as a free-ring identity, and 1,008 bounded direct-rank
controls (including eta=0). Reproduce with `python3 -I -S -B check.py | cmp - receipt.json`
from this directory. These are not Lean or arbitrary-model proof checks.

For the eta-natural 85 prototype, its literal main shift has
`r0=kbase−R`, `k=kbase+1`, so its signed main root is exactly

```
U*(X+a*c)+H*(U*gamma+R+1) − H*k.
```

At gamma zero, `GammaNoExtraFactsDraft` supplies this **actual R** to
`GammaZeroNarrowDraft.gamma_zero_impossible`. Its signed-pair norm is the
same no-extra-term carrier; it does not apply the old residue-90
`gamma_pos_of_fact_cut`, which would use `R+X*Y*q` inside the carrier. The
prototype client sources its pair norm from the separate actual graph
main-pair draft and supplies its own positive-eta premise explicitly.

The revised packet replaces the old imported `enlarged_rank_gap` with its
own `GammaDirectRankGapDraft.direct_rank_gap`. With `q≥2`, `X≥1`, `Y≥q³`,
`k≥8XY²+4` and the stated rank window, it derives `q≤Y` and
`q⁴≤XY²`. Therefore `R+1≤q⁴≤XY²<k`. Independently,
`X≤XY²<k≤Yk≤eta+Yk`, with eta merely model natural. These are exactly the
two premises of the narrower gamma contradiction, which also requires
positive U/Y/k and the exact natural signed-pair norm. The direct rank lemma
does not assume eta>0; the larger gamma client still explicitly assumes it,
and uses eta/zeta positivity and first/main norms in its own hypotheses.
The former, stronger `R+XYq+1<k` inference is no longer used.

For an 87 zero, the transport applies the w-increment map at coordinate 6 to
reach an 86 zero and then the eta-increment map at coordinate 9 to reach an
85 prototype zero. The latter has positive eta, while both maps preserve
coordinate 12; this is sufficient to apply the prototype gamma-positive
client. Only those **forward** maps are used: no `ForcedEta` premise or
reverse eta map enters `gamma_positive`.

The gamma map compares the exact 88 parent at v with the 87 child at v with
coordinate 12 raised. The reverse no-zero direction lowers gamma only after
the derived `gamma_positive` statement. `compact_sameNoZero` has 87 child
first and 88 parent second at the same `ports K`. `bridge87` still explicitly
requires `PolynomialBridge` for that exact 88 parent and tuple; the further
`native85` also explicitly requires `ForcedEta K`. A separate composition
may supply the latter, but it is not supplied inside this packet.

No mathematical graph, inequality, map-direction or bridge-interface
mismatch was found in the inspected cuts. The new direct-rank source uses explicit order lemmas and `ring`, with no
`omega` or `nlinarith` in its proof body. This avoids the earlier imported
`enlarged_rank_gap` source's abstract-model `omega` use; it is still
unelaborated. The separately imported `GammaZeroNarrow` uses `nlinarith`,
and exact source casts, literal evaluation proofs, imported
positivity/zero-map theorems, provider compatibility and `#print axioms`
remain unverified by Lean. This
audit does not bind a selected concrete K or external bytes/PDF, prove an
88-parent endpoint, or establish the requested iPRA equivalence.

The initial review pinned the earlier enlarged-rank formulation. Following
the author's source repair, this review repins the revised direct-rank and
no-extra-facts sources and checks the revised interfaces and inequalities;
the transport source itself was unchanged. The updated receipt supersedes
the earlier review receipt for these bytes.
