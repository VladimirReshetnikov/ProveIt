# Conditional orientation of the main root

`main_positive` is a Lean theorem for a linearly ordered commutative ring.
It assumes the explicit hypotheses in its source, notably

```
0 < E,W,a,H;  0 ≤ X,eta,d;  W*Y−7−W ≥ 0;
8E ≤ k; H ≤ 7a; QP=WE; −QP ≤ rank.
```

Under these hypotheses it proves

```
W*(X+a*(eta+Y*k))+H*(W*d-k+rank+1) > 0.
```

This is the intended form of the 88 graph's signed main root under an
appropriate substitution. The proof rewrites it as a sum of nonnegative
terms plus the positive term `a*W*E`. The source also assumes `0≤Y`, which
Lean warns was not explicitly referenced. The theorem does **not** derive
any premise from an actual graph zero. In particular, the intended negative
branch's signed rank bound and the other graph-to-ring substitutions remain
to be checked. No transport normalization, 88/89 reverse implication, or
iPRA endpoint is claimed here.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0, reporting axioms `[propext,
Classical.choice, Quot.sound]` and the single unused-`hY` warning; no
`sorryAx` was reported. From the repository root:

```sh
LEAN_PATH=/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-main-orientation-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-main-orientation-draft/Absorb88NegativeMainOrientation.lean \
  -o /tmp/Absorb88NegativeMainOrientation.olean
```

Source SHA-256:
`1899f09347f49ccd0416a325b1593100a208d4d5c68ccd4f37b6322350c424bb`;
output SHA-256:
`ff5b89e1efc90814dc95297166bedf1f19b15cba32022a042acb71cec6debb59`.
The imported `ModelDifferenceRing.olean` SHA-256 was
`d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74`.
The check inherits prebuilt providers; complete project, package, dynamic and
search-path ancestry was not audited.
