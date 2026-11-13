# Conditional fresh private witnesses in an IΣ₁ model

This packet is **not** a proof of the 69-operation equation's converse or an
object-level iPRA derivation. It treats the retained transport `G` as a supplied
model-natural input; obtaining its positivity and divisibility from an actual
14-coordinate zero remains open. Exact literal binding and either 2011 or
phase-split2471 fixed-port calibration are separate obligations.

[`ModelBPositiveCarrier.lean`](ModelBPositiveCarrier.lean) proves the following
conditional model lemma. For `I≥2`, positive model elements `u,y,b,G`, a
supplied `b∣G`, a supplied `4*b∣y+1` and the additive auxiliary norm

```
I²u²+y² = 1+I²y²,
```

it constructs a positive model-natural `m` satisfying in the model's ring of
differences

```
−ι y = 1+4*(ι b*(ι m−(ι u)²*ι G)−ι G).
```

Its proof first obtains `|−ι y|<2*|ι u|` from the supplied norm, constructs
the signed quotient using the two supplied divisibility witnesses, proves it
is positive, and then recovers a model-natural representative. This does not
claim that `G`, `b`, `I` or the displayed carrier are literal nodes of any
particular expression.

[`ModelBFreshPrivate.lean`](ModelBFreshPrivate.lean) composes that conditional
carrier lemma with the multiplied strong/auxiliary seed and odd-ordinate
residue. Given arbitrary model elements `a,R,b,G` with `b>0`, `R%4=3`, `G>0`
and `b∣G`, it constructs positive `f,i,T,u,y,m` with the strong norm, the
auxiliary norm, the two quotient residues, the T equation and the signed
carrier equation. The theorem uses `c=ycoord R a` and
`I=delta a*(b*i*c*c)`. It has no port or graph assumption because those
connections are not yet proved.

## Exploratory compilation

The positive-carrier source compiled against one coherent author overlay in
session 21354, with observed exit 0 and the three `push_neg` deprecation
warnings retained in the transcript. The fresh-private source first failed in
session 87465 on a missing-space parser error and printed `sorryAx` for the
incomplete theorem; after correcting the spacing, session 37672 actually
exited 0 and reported `[propext, Classical.choice, Quot.sound]` without a
warning or `sorryAx`. Lean's metatheory axioms are not asserted as axioms of
object-level iPRA.

## Paired replay

[`replay.py`](replay.py) checks the independently audited model auxiliary
seed and negative-ordinate residue parents before and after compiling these
two modules sequentially on each side. It creates a fresh overlay with 69
auxiliary-parent object links and five additional negative-residue links per
side, checks the targets and hashes of all 74 links, and records direct
dependencies, compiled source and object hashes, warnings and axioms. The
compilers use `-M4000 -j1` and per-module timeouts.

Session 72170 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_FRESH_PRIVATE 08fba9296d09639e614ce5716a4e02b35ee4235134a9e63234fd719762db3958`.
The [receipt](replay-receipt.json) records the four compiler and four
direct-dependency-check exits, the corresponding matching object hashes and
both parent audits. The [terminal observation](terminal-observation.json)
records the actual outer exit. Both carrier compiles emit the same three
`push_neg` deprecation warnings; both assembly compiles have no warnings or
`sorryAx`. A subsequent [independent artifact audit](../../reviews/thirteen-model-fresh-private-independent-audit/README.md)
passed for the combined suffix and its two parent branches.

The audited parent branches share the same 70-source project parent. Their
package-transitive and dynamic ancestry and the original Foundation wrapper's
unobserved exit remain inherited. This paired replay establishes only the
conditional model lemmas, not the still-missing graph, checker calibration,
or iPRA equivalence.
