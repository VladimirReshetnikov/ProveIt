# Positive 81 to 83: exact carrier and model calibration gap

This is a bounded, source-pinned mathematical audit. It does not supply a
Lean-elaborated model zero map, provider closure, or an iPRA endpoint. The
81/83 graphs have the same 13 positive-coordinate order, the same compact
port positions, and the same three non-first residuals. They differ in the
first carrier only:

```
b = J*beta, q = 1+b, C = q-F-alpha, D = C*K0-F
Bprime = C*(X+K0)-F,    B = C*(X+K0*q)-F*q
B = Bprime + b*D
Z(P,r) = b*(ell+k+r-k*P)-P
Z(B, r+(k*b+1)*D) = Z(Bprime,r).
```

These identities hold in the difference ring, but the displayed signed
coordinate change need not produce a positive model-natural witness. As in
the prior 82/84 audit, use the first norm to construct a *positive* root
branch instead: if the target carrier `P=b*tP` with `P>0`, and its common
norm has a natural `tau>ell`, then

```
r_target = k*(P-1)+tP+(tau-ell) > 0,
Z(P,r_target) = b*tau.
```

The source graph determines the first norm, but positivity and divisibility
of each *companion* carrier must be supplied in the correct direction. If
`B>0`, `Bprime>0` follows from `B=C*X+q*D`, `Bprime=C*X+D`, `q≥1`, and
`C*X>0`; this direction needs no `X≥q²` calibration. If instead only
`Bprime>0` is known, the sufficient bound `X≥q²`, together with `C≥1`,
`F≤q−2`, and `K0≥0`, yields `B≥2q>0`. Divisibility transfers since
`B−Bprime=b*D`. The bound is sufficient, not claimed necessary.

The receipt's scalar control `beta=46, J=1, q=47, F=1, alpha=45, K0=0,
X=47, MC=MF=1` has `Bprime=46`, `b∣Bprime`, `B=0`, `X=q<q²` and the
rank window `R+q³+q+1≤q⁴`. It even has `R≥q³`. It is a *partial scalar
assignment*, not a full 81/83 graph zero, and does not satisfy the actual
fixed compact beta merely by meeting its lower bound. It shows why those
listed scalar and rank facts alone do not prove positive B or `X≥q²`.

## Connection to the actual no-extra-term prototype

The first/main/strong/auxiliary graph rows through `Fa` are identical in
positive 81 and positive unit-product 80. At a zero of the 81 sum of four
squares, each signed residual is zero, so the 80 product is zero. This
forward argument does not require the converse product-factor exclusions.
For positive 81 witnesses, lower the ten coordinates of the 80→89 mixed map,
then apply the forward J/gamma/w/eta maps 89→85. The resulting 85 tuple is

```
(J, F-1, alpha-1, f, i-1, T-1, w, s-1, r, eta, zeta-1, y, gamma).
```

Every predecessor exists because the original coordinate is positive. The
checker proves, via symbolic commutative-ring additive normalization rather
than sampling, that the four 85 residual fields and `q,X,Y,R,k,c,Delta,Z`
match the positive-81 fields under this exact tuple. The 85 main carrier is
therefore the actual **no-`E*q`** carrier. This is a source-and-ring identity;
a Lean all-model adapter from the 81 sum zero to the 85 product zero remains
to be written and checked. This one direction needs neither `ForcedEta` nor
an existential r replacement.

The following existing source statements can then be instantiated only after
the adapter and their shared providers are checked:

* `EtaNaturalGraphEarlyIndexDraft.compact_early_index` proposes the same
  first `tau,n,w`, first ordinate and `2*n mod q⁴ = R+1`, with the compact
  rank window. This is a congruence, **not** yet `2*n=R+1`.
* `EtaNaturalGraphStrongAuxDraft.ordinary_strong` and `direct_auxiliary`
  propose the actual 85 signed strong and auxiliary bindings; the latter
  needs the graph gap `F≤q`. The strong/auxiliary, geometry and positive
  offset adapters supply candidate premises for `P72Exact.indices_ordinary`.
  Since the mapped eta equals the original positive eta, the existing
  positive-eta theorem can be used if all its other exact hypotheses are
  proved with the same witnesses. Its `i'` must be the mapped graph's
  `i=(i-1)+1`, and its `m` is the index of the actual natural main ordinate.
* `EtaZeroGrowthDraft.power` and `EtaZeroDirectProjectionDraft.power_of_direct_carrier`
  are fact-level proposals for the exact no-`E*q` carrier. They require the
  *same* first index and quotient, the exact equality `2*n=R+1`, main x/y
  coordinates for the same oriented root, and its actual oriented balance.
  The early-index theorem alone supplies none of those exact bindings.
  `X=q*w` and positive w with compact `q≥47` can provide its `X≥16` input.

A useful final arithmetic reduction is available once the missing graph-level
power result is obtained. From `F,alpha≥1` and `F+alpha<q`, the displayed
rank formula has coefficient `(q-F)*(q-1)+alpha ≥ 2q-1 ≥ q+1` for `q≥2`;
with natural nonnegative port terms, `R≥(q+1)*(q²−1)≥q³≥q²`. Thus
`X=2^R` and model exponential growth `R<2^R` imply `X≥q²`. The available
`rank_at_least_26` and rank-window source statements are weaker than this
specific lower bound; an exact compact graph client for the displayed rank
inequality and a coherent model proof of power recovery remain to be supplied.

In particular, the existing residue-90 graph-level `graph_power` is for a
**different** main carrier with an extra `X*Y*q`; neither it nor an original
free-J literal-zero wrapper may be substituted for the no-extra-term graph.
The source's eta-zero parity contradiction is also not itself the requested
positive-eta calibration. All source drafts, arithmetic tactics, cast and
port bindings, fixed K, endpoint ancestry, and physical PDF linkage still
require independent Lean/provider verification.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-positive81-to83-model-gap-audit/check.py
```
