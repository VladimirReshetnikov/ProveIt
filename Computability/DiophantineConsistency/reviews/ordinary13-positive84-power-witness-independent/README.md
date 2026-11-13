# Independent source review: direct positive-84 power recovery

This reviews `research/ordinary13-positive84-power-model-draft/` and its
source interfaces; no Lean, builds, staging or provider replay was performed.
The receipt pins the exact 84 graph and author sources and reproduces the
author's checker.

`ExactPowerFacts p v` explicitly asks for one R, n, main and w for the same
positive 84 valuation. The first ordinate uses n, the index decomposition
uses the same n and w, and both main Pell coordinates use the same R and
main. Its carrier balance includes the literal graph's extra `X*Y*q` term;
the exact graph rows are pinned. The rank is required to equal the stated
natural rank expression. These are **hypotheses** of the fact client: the
actual graph-zero-to-witness construction remains `ExactPowerGraphCut`.

The receipt proves the following identities in a free integer polynomial
ring, for `Y=q³*s`, `U=Y*q²` and `W=4*X*q*s*w`:

```
4*X*Y²*w=U*W,
carrier_balance_defect
  = q*Y*(q*(main+H*W)-q*(X+a*c+H*gamma)-H*X).
```

Thus the cited q-balance source is for the **extra-term** carrier, and its
positive q/Y cancellation is an explicit model hypothesis. The copied
`power_of_oriented_balance` declaration and body match the pinned prior
source verbatim; it takes the same main x/y coordinates and growth bound.
The local `growth` proposes the latter using the same n and R, the first and
main ordinates, and `q∣3X`. Its `X≥16` step follows from `q≥46`, `X>0` and
`q∣3X`, without requiring `q∣X`.

The inspected fact-premise and power proof do not assume `q∣X` or use the
84→83 zero map. They propose the sequence exact graph facts → `q∣3X` and
`2^R<Y` → `X=2^R`; only the later conditional divisibility client uses
Mersenne cancellation. No claim is made here that the graph actually supplies
the exact facts. The Lean tactics, same-root extraction, signed rank binding,
all model/source providers, axiom reports, parent bridge and physical
PDF/ZFC endpoint remain unverified.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive84-power-witness-independent/check.py
```
