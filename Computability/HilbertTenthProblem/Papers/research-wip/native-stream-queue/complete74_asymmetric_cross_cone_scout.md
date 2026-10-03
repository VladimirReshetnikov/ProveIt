# Bounded cross-cone sharing scout after X=wq

**No operation saving was found in the stated local family.** Starting from each of the three actual saved [complete74 sources](complete74_factored_first_norm.json), replace only `wn2=w*n2` by `wn2=w*q`. Eighteen complete emitted schedules then test two multiplicative scale layouts and three packing layouts. The minimum remains **74=40M+34A**, with complete SOS costs130,106,100. This is an arithmetic scout, not a new positive-domain transfer theorem or a general circuit lower bound.

The [helper](complete74_asymmetric_cross_cone_scout.py) pins the immediate complete74 PY/JSON/MD trio, imports no historical builder and saves every full source, every comparison and every complete SOS finalizer in its [receipt](complete74_asymmetric_cross_cone_scout.json). No supplied input, fixed numeral, witness or comparison is removed. The one-operand asymmetric cut is a different polynomial from its symmetric parent; the exact identities below compare reassociations only with that explicit asymmetric cut. Its positive-zero transfer is a separate proof obligation handled by the asymmetric transfer work.

## The product scale interface cannot become cheaper by multiplication-only reassociation

The retained cross-cone outputs are

\[
 q^2,\quad X=wq,\quad Y=sq^3,\quad E=XY=wsq^4.
\]

The first output is needed by packing. The last three feed transport, the index equation and the first/main norm cones. All remain live after the asymmetric cut.

With supplied q,w,s and multiplication gates only, at least five gates are needed for these four distinct monomials. If four gates sufficed, every gate output would have to be one of those four targets. But `sq³` cannot be the product of two available supplied/target monomials: it requires an intermediate such as q³, sq or sq². Outputs containing w cannot help because there is no cancellation or division in this restricted model. The helper checks all24 possible target production orders as a finite supplement to this argument.

Five multiplications suffice in either tested schedule:

- Compute q²,q³,wq,sq³, then E=X*Y.
- Compute q²,wq,sq, then Y=(sq)q² and E=X*Y.

This lower bound is limited to the stated monomial interface and multiplication-only model. It does not exclude using additions/subtractions, changing source comparisons, new supplied coordinates, or a different semantic representation.

## Reusing q³ in packing adds work

Let `mask=(MC+q*MF)*Jrep`. The original packing result is

\[
 r_{\rm lhs}=(q^2-Z-qF)(q^2-1)+\mathrm{mask}.
\]

Here MF is the actual supplied fixed numeral port of the source; no native/shifted mask substitution is made. Three exact forms were emitted:

1. Literal: `(q²-(Z+qF))*(q²-1)+mask`.
2. Horner: `(q*(q-F)-Z)*(q²-1)+mask`.
3. Cubic factor: `(q-F)*(q³-q)-Z*(q²-1)+mask`.

The first two each cost2M+3A before the unchanged mask cone and final addition. The third costs2M+4A even when q³ is already paid. In the alternate sq scale layout it additionally requires computing q³. Therefore the tempting reuse of the existing cube does not save a gate.

| Scale layout | Packing layout | Complete certificate | Raw SOS | Positive22 SOS | Signed20 SOS |
|---|---|---:|---:|---:|---:|
| cube or sq | literal or Horner | 40M+34A=74 | 130 | 106 | 100 |
| cube | cubic factor | 40M+35A=75 | 131 | 107 | 101 |
| sq | cubic factor | 41M+35A=76 | 132 | 108 | 102 |

These are the entire six-layout family for each of the three saved modes, not selected samples from a broader optimizer. All eighteen schedules are closed and live, and none has a duplicate literal gate even after commutative operand canonicalization. Witness counts30,22,20 and comparison counts19,11,9 are retained. Every SOS pays all residual subtractions, squares and final additions.

The helper proves the five crossing outputs `q²,X,Y,E,r_lhs` by exact sparse polynomial coefficients in independent formal ports. It checks that every external consumer of each changed local cone crosses only those proved outputs, and that all other source rows and all comparisons are unchanged. Thus each entire finalized polynomial equals its corresponding asymmetric baseline on all tuples over every commutative ring. This is an exact source identity; no zero-set equation is used during the rewrite.

The receipt contains30 local output identities,18 complete graph identities,234 retained comparisons and2,025 live full-source gates. Naive complete degree upper bounds are44 for raw30 and76 for the two projected forms. Those deliberately loose projected bounds do not replace the separate cancellation-aware asymmetric degree proof.

## Unshifted quotient shear is not a positive-coordinate saving

For completeness, the actual transport comparison is

\[
 (K+wq)C=F+z_{\rm quot}(q-1).
\]

The algebraic substitution `t=zquot-w*C` changes it to `(K+w)C=F+t(q-1)` with the same number of gates. X=wq remains needed by the other cones, so its multiplication cannot be deleted. This observation is algebraic only: the new t may be zero, and the source expects strictly positive supplied witnesses. The earlier complete86 proof concerns a shifted quotient, not this literal unshifted source port.

Using `t_plus=zquot+1-w*C` instead adds the correction `+(q-1)` to the transport residual. An extra addition must be paid unless a separately proved whole-source rewrite absorbs it. Neither quotient change is used in the eighteen emitted schedules, and no positive inverse theorem is claimed for it here.

The useful boundary is concrete: preserving the four scale ports and merely reassociating these three packing formulas cannot lower74. A further improvement must use an interaction outside this tested family. There is no claim that the untouched main/input/index cones are optimally implemented.

## Replay

```sh
python3 complete74_asymmetric_cross_cone_scout.py \
  --root /path/to/native-stream-queue \
  --expect complete74_asymmetric_cross_cone_scout.json
```

Only Python's standard library is required. The writer and fresh replay from `/` pass exact recursive type/value comparison. The receipt authenticates its helper source and immediate parent bytes. No historical suite, repository mutation, numerical universal promotion or enormous Pell witness computation is part of this scout.
