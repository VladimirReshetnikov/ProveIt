# Fresh strong Pell seed with an additional multiplier

[`ModelBSeed.lean`](ModelBSeed.lean) proves in every `IΣ₁` model: given
natural model elements `a,b,c` with `b>0` and `c>0`, there are positive
`t,f,i` such that

```
f = xcoord t a,
ycoord t a = b*i*c*c,
f*f = 1 + delta a * (b*i*c*c) * (b*i*c*c).
```

The theorem applies the internal pigeonhole theorem
`ArithmeticPellPigeonhole.ordinate_dvd` to the actual modulus `b*c*c`, and
uses the Pell norm at its positive index. It is the strong-seed ingredient
needed by the 69-operation thirteen-coordinate construction; taking
`c=ycoord R a` with positive `R` is a possible application. It does not assume
any ports, a rank phase, or the ordinary strong norm in advance.

This is **not** the 13-variable converse or an iPRA derivation. The private
auxiliary seed, rank phase, signed ordinate and carrier quotients still need
model-level construction and transport. The model expression-to-literal
binding, both zero directions, and the exact four-port phase-split2471
calibration to the ZFC checker are separate obligations. The standard-ℤ
`ThirteenFreshSeed` and `ThirteenCarrierComplete` theorems cannot simply be
applied to nonstandard model elements.

## Replay

[`replay.py`](replay.py) sequentially compiles the pinned source of
`ArithmeticPellPigeonhole` and then `ModelBSeed` against each side of the
independently audited, matched 70-module coherent parent. Before and after the
suffix builds it checks the pinned inputs and reruns the parent's comparator;
it checks the copied source and direct dependencies and rehashes the 70 parent
object links. Each Lean invocation uses `-M4000 -j1` and a 240-second timeout.
It requires a fresh `/tmp/ipra-thirteen-strong-seed-pair-*` output directory.

Session 50440 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_STRONG_SEED 9faa32f1c6715ffd6fd5a84330d46c545ad8c8aea3261c64c009144e841501f7`.
The [terminal observation](terminal-observation.json) and
[receipt](replay-receipt.json) record both Lean exits, direct dependency
queries, object hashes, pinned parent comparison, and axiom output. Both
suffix object hashes match across siblings. The seed theorem reports
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`. The rebuilt
pigeonhole source emits three pre-existing deprecation warnings (`push_neg`
twice and `mul_le_mul_left'` once); these are preserved in the receipt. Those
Lean metatheory axioms are not axioms asserted for object-level iPRA.

This paired suffix has passed an [independent artifact audit](../../reviews/thirteen-model-strong-seed-independent-audit/README.md).
Its 70-module parent is source-frozen; the two Lean files added by the subsequent
upstream merge are not in that parent. The original Foundation provider's outer
wrapper exit and package-transitive/dynamic dependency ancestry retain the
[parent audit's](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md)
qualifications.

## Exploratory failures

The first isolated pigeonhole command exited 1 because the temporary project
lib did not contain the parent project objects; the next exited 1 because its
parent `BusyBeaver` namespace was absent. Both were path-setup failures and
were corrected by a fresh symlink overlay before the successful exploratory
compile. Two exploratory seed proof attempts exited 1 on the same positivity
step (once by an unmatched simplification and once by reversed multiplication
order); both printed `sorryAx` for the incomplete theorem and are failures,
not accepted results. The final exploratory seed command in session 46090
actually exited 0 without warnings or `sorryAx`; the subsequent two-sibling
replay is the result recorded above.
