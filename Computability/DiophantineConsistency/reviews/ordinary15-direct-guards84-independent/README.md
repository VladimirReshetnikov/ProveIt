# Independent review: direct Pell root with two quotient guards

**PASS, external standard-integer comparison.** The frozen author packet
`../../research/ordinary15-direct-guards84/` has positive-zero existence
exactly when the reviewed 13-input 87/36 parent does, for arbitrary integer
ports with beta>0. It has 15 positive inputs, 84 live operations and exact
specialized degree 36 at the authenticated compact44 ports. This review does
not establish a Lean/iPRA theorem, PDF/JSON interpretation, provider replay,
or a global minimum; the parent's endpoint qualifications are inherited.

We independently reconstructed the whole literal delta: eleven scaled-root
gates are removed, the first square/subtraction are retargeted, and eight
gates add the two squared guards. The graph has 84 unique topologically
ordered, live gates; all 15 inputs and four fixed leaves are live. The
remaining three parent residuals are unchanged.

For an old positive zero, `M=q³b>0` and its first norm gives `M|Z`. Modulo
q³ and b, using their coprimality, gives `q³|Y` and `b|Bt`. The literal
first expression makes Bt>0: otherwise Z exceeds `M*(ell+k)`, while the
norm implies `|Z|<M*(ell+k)`. Thus the positive inputs
`s=Y/q³`, `t=Bt/b` and `tau=|Z|/M` satisfy both new guards and the direct
first Pell norm.

For a new positive zero, the guards give `Y=q³s`, `Bt=bt>0`. The main norm
excludes k=2 by the reviewed consecutive-square argument, and the reviewed
first-Pell descent gives `tau−ell>k/4>2s`. Hence

```
r_old=k*(Bt−1)+t−s+(tau−ell)>0.
```

Substitution into the parent expression gives `Z=M*tau`, so every old
residual vanishes. Both directions use only beta>0, positive inputs and
integer arithmetic; no sign of K0 or compact44 decoder is needed locally.

The first, main, auxiliary, strong and two guard residual degrees are at most
8, 13, 18, 10, 4 and 2, so the total degree is at most 36. Independently,
using input weights `1,2,...,15` and the authenticated P72/P115 port integers
modulo 1000000009, the complete graph has degree 36 and nonzero leader
**168665932**, establishing the specialized lower bound.

The checker pins the frozen author graph and README, independently checks
source topology and 160 signed guard-error identities, reauthenticates both
port bindings and runs the distinct weighted ray. The author checker was
rerun and matched its receipt. The finite controls do not replace the
unbounded root proof above.

```
python3 -I -S -B reviews/ordinary15-direct-guards84-independent/check.py > /tmp/direct-guards84-independent.json
cmp /tmp/direct-guards84-independent.json reviews/ordinary15-direct-guards84-independent/result.json
```
