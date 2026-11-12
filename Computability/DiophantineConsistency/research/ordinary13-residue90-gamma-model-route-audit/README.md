# IΣ₁ route for residue-90 gamma: source-level audit

The exact Pell-descent bound needed by the [13/90 compact-port gamma argument](../ordinary13-natural-residue-forced90-degree56/)
already appears as a **source-only proposal**:
[`AuxRootBoundsModelDraft.first_ordinate_large`](../ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean).
It states, in the displayed ordered IΣ₁ model context,

```
0<m → 2<k → tau²=1+m*(m+1)*k² → 8*m+4≤k.
```

Its source uses the existing [`ArithmeticPellFirstNorm.descent`](../../Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean)
and `two_le_ordinate`. The latter file's descent is the precise unit
`(2m+1,2)`, after setting its parameter to `m-1`. The proposed proof gets
natural u,v with `u²=1+m(m+1)v²` and `k=2u+(2m+1)v`; if v were zero, u=1
and k=2, so v>0. The existing `two_le_ordinate` yields v>=2. The norm gives
u>m*v, so u>=2m+1 and k>=8m+4. No unbounded external Pell classification is
needed for this one step. However, the cited `first_ordinate_large` source is
not an elaboration receipt or an authenticated object provider.

## Existing fact-level interfaces

- [`FirstMainLargeKDraft.first_main_large_k`](../ordinary14-first-main-large-k-draft/FirstMainLargeK.lean)
  proposes k>=8XY²+4 from positive X,Y,eta,zeta and the explicit natural
  first/main norms. Its source combines the Pell bound with a separate
  consecutive-square exclusion for k=2. Its own record calls it unelaborated.
- [`GammaZeroNarrowDraft.gamma_zero_impossible`](../ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean)
  proposes an IΣ₁ fact-level contradiction from U>0, Y>=8, k>0,
  `Rprime+1<k`, `X<eta+Y*k`, and an **explicit signed-magnitude main norm**.
  It has no gamma-positivity premise, graph binding or Lean receipt.
- [`ArithmeticAdaptiveRankWindow2011.scalar_rank_window`](../../Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean)
  takes natural beta, MC and MF with `MC<beta`, `MF<2*beta`, positive
  J,F,alpha and `F+alpha<q`. It concludes the required rank bound for its
  explicit natural R expression. [`CompactFixedBeta.bounds`](../../Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean)
  is a source-level model interface for the compact beta and mask bounds,
  conditional on J>0. Source/provider compatibility and current elaboration
  are separate from the statements' text.
- [`DirectMainNorm.direct_main_orientation`](../../Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean)
  takes a signed-pair magnitude norm as a hypothesis; it does not derive it
  from the residue-90 graph. Its quotient uses
  [`ArithmeticSquareDivisibility.dvd_of_square_dvd`](../../Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean).

## Exact composition still required

For this 90-row residue graph, `Bt=C*(X+K0)-F`, and at gamma=0 the main
expression is

```
Dstar = U*(X+a*c) + H*(R + X*Y*q + 1 - k).
```

The narrow gamma theorem can therefore be instantiated with
`Rprime=R+X*Y*q`, **not** simply R. It needs all of the following clients:

1. A graph-zero extraction for the mixed-shift literal, and the previously
   documented forcing of J,X,f,y. Port values must be represented by model
   naturals with beta>0, K0>=0, MC<beta and MF<2beta. The exact compact tuple
   cast equalities and bounds must be supplied, with their own provider chain.
2. The residue carrier's own `C>0` argument and signed first/main norm
   reflection, including natural magnitudes and positive scale quotients tau,d.
   This supplies the precise hypotheses of `first_main_large_k` and
   `scalar_rank_window`, and requires reconciling their natural subtraction
   with the actual signed graph expressions.
3. A growth client using only the facts available here. With q>=2, X>=1,
   Y=q³*s>=q³, k>=8XY²+4 and `R+q³+q+1<=q⁴`, one has `q⁴<=X*Y²` and
   `X*Y*q<=X*Y²`. Hence `R+X*Y*q+1<=2*X*Y²<k`; also `X<eta+Y*k` and
   Y>=8. The existing `GammaPremises.narrow_inequalities` assumes the stronger
   `q<=X`; it cannot simply be invoked on this graph without another proof.
4. An exact pair/evaluation identity showing that the graph's main residual
   gives the narrow theorem's magnitude norm with the above Rprime. Then the
   theorem excludes gamma=0, yielding the positive predecessor needed for the
   90/91 model zero-map. The reverse coordinate map, a compatible compiled
   provider, model-to-iPRA client, compact port binding and parent endpoint
   provenance remain separate work.

No claimed Lean theorem follows merely from these source matches. In particular,
the 90 packet's gamma step remains standard-integer mathematics until the
model client and its dependency closure are elaborated and checked.

Run `python3 -I -S -B research/ordinary13-residue90-gamma-model-route-audit/check.py`
from `Computability/DiophantineConsistency` to reproduce the bounded
source-signature/graph-wiring receipt in [result.json](result.json). The
checker does not execute Lean or prove the listed obligations.
