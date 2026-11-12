# Model-transfer audit: residue-adjusted 13/82 carrier

The [13/82 graph](../ordinary13-residue-first82/) has an independently
reviewed **standard-integer** positive-zero equivalence to its
[13/84 parent](../ordinary13-qcube-unscale84/) at the stated compact44 port
bounds. The local graph-to-graph transfer has not been elaborated for all
IΣ₁ models, and that standard review does not supply an iPRA endpoint.
This audit isolates the missing directional and source obligations.

## Exact change and directional asymmetry

For model-natural beta,J,F,alpha,X,K0 with beta,J,F,alpha,X positive and
K0 nonnegative, let

```
b=J*beta, q=1+b, C=q-F-alpha, ell=X*Y²*k,
B = C*(X+K0*q)-F*q,   Bprime = C*(X+K0)-F,
D = C*K0-F.
```

All subtractions here are in the associated signed difference ring. The
82/84 source delta and exact free-ring identities are checked:

```
B = Bprime + b*D,
Z84(r+(k*b+1)*D) = Z82(r),
ZP(r) = b*(ell+k+r-k*P)-P.
```

The second identity by itself supplies a **signed** coordinate update; it does
not ensure either updated coordinate is positive. At a positive zero of either
graph, its own P in `{B,Bprime}` is positive and divisible by b. For the
model proof, reflect the first squared residual into a positive natural tau:
`ZP²=b²*(1+ell*(ell+k))`, `|ZP|=b*tau`, and `tau<ell+k`. The graph identity
also gives `b | P`. Write `P=b*t` with signed t. If `P<=0`, then `t<=0`, and
both root orientations imply
`r=k*P+t-ell-k±tau<0`, contradicting the positive root coordinate.
Consequently `P>0`, and K0>=0 forces C>0. These steps need signed-magnitude
reflection, square divisibility, and the order-to-natural quotient bridges;
they are not yet an 82-specific Lean theorem.

There is a useful asymmetry in finding a positive **companion** carrier. Put
`A=C*X>0` and `D=C*K0-F`. Then `B=A+q*D`, `Bprime=A+D`, q>=1.
If B>0, Bprime>0: for D>=0 this is immediate, and for D<0,
`Bprime>=B`. Thus **84→82** can orient the target transport without a
rank or calibration bound. Since `B-Bprime=b*D`, divisibility by b also
transfers. If `Ptarget=b*tP>0`, `tP>=1`, and a positive tau satisfies the
same Pell norm, define

```
r_target = k*(Ptarget-1) + tP + (tau-ell).
```

The norm gives `tau>ell`, so this is a positive model natural and the target
carrier is `b*tau`. The remaining residuals do not use r. Formal clients
still have to prove these graph, reflection and natural-coordinate facts.

For **82→84**, positivity of Bprime and its b-divisibility do not alone imply
B>0. The exact scalar assignment

```
beta=46, J=1, q=47, F=1, alpha=45, K0=0, X=47, MC=MF=1
C=1, Bprime=46, b | Bprime, B=0, R=4771536
```

also satisfies `MC<beta`, `MF<2*beta` and the scalar rank window
`24<=R`, `R+q³+q+1<=q⁴`. This is **not** a full graph zero and does
not refute zero equivalence or any possible other witness map. It rules out
deducing B>0 from just those listed scalar facts, even with that rank window. The reviewed standard proof
uses the stronger property `X>=q²`; with C>=1 and F<=q-2 it gives
`B>=q²-(q-2)q=2q>0`. A model client needs this bound or another independently
proved positive-companion construction; X>=q² is sufficient, not asserted
necessary.

## What remains for model-level X>=q²

The source path below is an **inventory of usable interfaces**, not an already
composed proof for 82:

1. Reflect all four actual 82 residuals and compact natural port casts; extract
   the first and main quotient norms in the model. Prove P>0, C>0,
   `F+alpha<q`, and natural `Y=q³*s` directly from this graph.
2. Orient the **actual** main signed root. The source-level conditional
   [`DirectMainNorm.direct_main_orientation`](../../Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean)
   accepts a signed magnitude norm and natural positive part; instantiate its
   parameters with the actual `X*Y*q` term and bind them to 82's main residual.
   Derive the additive `FreeJMainCongruence` facts and then
   [`FreeJMainOrientation.rank_congruence_from_main`](../../Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean),
   obtaining the signed q⁴ rank congruence. The theorem that directly extracts
   these facts from an original free-J literal zero cannot simply be invoked
   on a residue-82 zero.
3. Obtain first and main Pell indices from the extracted norms, then the
   q⁴ index residue. The existing
   [`FreeJEarlyIndex.early_index_of_facts`](../../Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean)
   assumes `FreeJIndices`, which includes a magnitude identity for the
   **original** `core.z`; it is not automatically a fact-level interface for
   the residue-adjusted first root. Either establish its exact original-root
   premise without circularity or reproduce the short recurrence/residue step
   from the actual tau and the q⁴ congruence.
4. The direct auxiliary input y must yield a positive old offset u=y-V in
   the model. The unelaborated
   [`AuxRootBridge.positive_aux_coordinate_iff`](../ordinary14-aux-root-model-draft/AuxRootBridge.lean)
   requires `1<Q` and `1<V²`; the unelaborated
   [`aux_bounds_of_natural_norms`](../ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean)
   proposes those bounds from explicit first/main/strong norms and signed
   bindings. None is already attached to the 82 graph.
5. Supply all explicit fact hypotheses of
   [`P72Exact.indices_ordinary`](../../Lean/DiophantineConsistency/Compact44/P72Exact.lean):
   first/main coordinates and residue, rank window, positive q³ quotient,
   natural strong equation and the absolute-square auxiliary equation. Its
   i-prime input must be the graph's i. The source's fact-level result does
   not assume an original literal zero, but it must be instantiated correctly.
6. Replay the main-balance arithmetic yielding `q | 3X`, X>=16, and the
   hypotheses of [`ArithmeticPellPowerRecovery.power_bound`](../../Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean)
   and `projection_quotient`; then conclude `X=Exp.exp R` and X>=q². The
   existing [`FreeJPowerFinish.graph_power`](../../Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean)
   instead **assumes an original free-J literal zero**; treating it as directly
   applicable here would be circular. The standard fact-level replay is
   documented in the [sign-free calibration](../ordinary14-shifted-guard87-calibration/README.md).

The arithmetic source interfaces are statements in the displayed IΣ₁ context;
the source-only auxiliary drafts, their tactic behavior and compatible
providers remain unelaborated. Compact port representations/bounds, source
and object ancestry, and the actual graph clients must be checked separately.

## Route to the documented endpoint

The reviewed positive-zero chain is 82 ↔ 84 ↔ 87/36 ↔ 88/30 ↔ 88/46 ↔
87/51. Each arrow needs its **own** all-model graph-and-witness transfer;
standard-integer reviews are not those transfers. The 88/30 and 88/46 model
clients exist as [uncompiled drafts](../ordinary13-freej88-four-square-lean-draft/),
not as a replay of the new chain. The documented existing endpoint is
[`FreeJ13Halt.positive_model_iff`](../../Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean)
and [`IPRAOrdinary13.native_equivalence`](../../Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean)
for its **87/51 Lean expression** at `CompactSymbolicModelIff.p`; its native
right side is `¬mappedNativeRefutation embedding`. Its recorded build is
author-side with inherited provider/byte-binding limits. Composing a coherent,
compiled sequence and the appropriate proof-theory adapters remains work.
No current-2011 PDF equivalence follows from these compact-port source names.

Run `python3 -I -S -B research/ordinary13-residue82-model-transfer-audit/check.py`
from `Computability/DiophantineConsistency` to reproduce [result.json](result.json).
It pins graph/source files, checks the two free-ring identities, and verifies
the exact scalar counterexample. It does not check Lean, prove any model
transfer, or certify that the scalar control is a full graph zero.
