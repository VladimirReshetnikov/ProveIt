# Negative ordinate residue for a multiple of the Pell base

[`ModelBNegativeResidue.lean`](ModelBNegativeResidue.lean) proves in every
`IΣ₁` model that, when `I≥2`, `b∣I` and `R%4=3`, there is a model-natural
`h` satisfying

```
ycoord R (I-2)+1 = 4*b*h.
```

The proof uses the model-level odd-ordinate pair for modulus `4*I²` and
weakens the modulus using `b∣I`. The intended signed ordinate is the
negative of the displayed positive ordinate; that sign interpretation is not
a separate theorem in this packet. The theorem does not explicitly assume
`b>0`; its other hypotheses preclude `b=0` in the intended models.

This is a model-level residue, **not** a positive carrier coordinate,
13-variable completeness theorem, exact literal/port binding, or iPRA proof.
To complete the fresh-private construction one must still relate this
ordinate to the separately constructed auxiliary norm, choose and prove
positive the literal `m` coordinate, and derive the rank and positive
transport from an actual parent zero. The potential 2011-port instance is a
separate candidate from the existing phase-split2471 tuple; neither
fixed-port checker calibration nor graph transport is proved here.

## Paired replay

[`replay.py`](replay.py) starts from the independently audited matched
70-source parent and sequentially compiles the exact pinned sources
`DiscreteOrderedRingFacts`, `ArithmeticNegativeNorms`, `ModelArithmetic`,
`ArithmeticOddOrdinateResidue`, and this lemma on each side. The later
`ArithmeticOddOrdinateResidue` file is newly rebuilt as a suffix and is not
pretended to be part of the 70-source parent. Each module's source, output,
actual compiler exit and direct dependencies are recorded; parent inputs and
comparisons are rechecked before and after, and all corresponding outputs
match. The sibling compiles use `-M4000 -j1` and 240-second per-module
timeouts. The parent’s package-transitive and dynamic ancestry and the
unobserved original Foundation-wrapper exit remain inherited.

Session 66854 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_NEGATIVE_RESIDUE a7ce2e650644acd4ea0a875c86fd04d2dcbf98f2950394822f32092e4c20fcab`.
The [receipt](replay-receipt.json) records ten successful compiler exits and
direct-dependency checks; the [terminal observation](terminal-observation.json)
records the outer exit. The new residue lemma reports
`[propext, Classical.choice, Quot.sound]` with no `sorryAx` or warnings.
The rebuilt older dependencies emit pre-existing deprecation warnings,
retained verbatim in the receipt. These Lean metatheory dependencies are not
asserted as axioms of object-level iPRA. An [independent artifact audit](../../reviews/thirteen-model-negative-residue-independent-audit/README.md)
passed; it checks the recorded paired results without rerunning Lean.

An earlier exploratory chain (session 83530) exited 1: its final theorem used
an ambiguous name `pair` and reported `sorryAx`. Qualifying the intended
`ArithmeticOddOrdinateResidue.pair` fixed that elaboration error; the next
exploratory seed command (session 57386) actually exited 0. The later paired
replay uses an equivalent source with an unnecessary auxiliary-seed import
removed, and is the accepted result recorded above. Neither failed attempt is
presented as proof evidence.
