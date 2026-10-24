# Wave10 native-related proposals: arithmetic and proof boundaries

This review covers the four original archives placed as68,69,74,75 from
arrival commit `9513bd88ce`. Inspection and replays used untouched extracted
originals in `/tmp/proofs62ff-wave10-native-review`; delivered artifacts were
not modified. The comparison here concerns formulas, domains, coefficient
bindings and ordinary proof arguments, not a new Lean certificate.

| Package | Domain | Variables | Exact degree | Live operations |
|---|---|---:|---:|---:|
|68 joint positivity, octic|integers|28|8|residual packet|
|68 nested positivity|integers|26|16|residual packet|
|68 free Lucas finalizer|integers|10|1,576,864|481|
|69 cone quartic|integers|38|4|residual packet|
|69 cone sextic|integers|32|6|residual packet|
|69 cone octic|integers|27|8|residual packet|
|69 rational Pell merger|positive integers|12|82|102|
|74 centered product|positive integers|12|110|100|
|74 centered SOS|positive integers|12|164|99|
|74 adaptive carrier|positive integers|13|30|93|
|75 signed bootstrap|integers|34|6|residual packet|
|75 adaptive carrier|positive integers|13|30|94|
|75 product merger|positive integers|12|114|105|

These do not improve the nine-variable443/450 presentation. Under a fixed
positive-variable count and the same compact44 tuple,74's13-variable point
beats75's by one operation, and its12-variable110/100 point beats75's114/105
in both degree and operations. The12-variable82/102,110/100 and164/99 points
are distinct degree/cost tradeoffs. The cone sextic/octic reduce integer
variable count but require two additional fixed weights, so they should not
be described as improvements in every size measure.

## Coefficient and domain bindings

The68 integer systems and free-Lucas source retain the whole original31
source34 tuple: `beta=2^1064921−1`, with `K0=K` and `MF=MF_source` already
shifted. The free-Lucas source is its explicitly supplied `gapN86` positive
coordinate transformation, with31 distinct weights, maximum116 and packing
height1873. Its ten-integer finalizer has12 fixed leaves; its threshold
`2^34159017` is supplied as a fixed numeral, not built during evaluation.
Charging its five legacy construction gates would change481 to486.

The69 cone family retains the same complete source34 tuple and derives
`Walpha=2*T*rho^3296` and `WC=T*beta`, where
`T=K0−beta*rho+1`, `rho=2^121`. The six fixed payloads require881,696 raw
bytes versus532,479 for its four-port parent. Its12-positive companion
instead uses the whole compact44 tuple, `beta=2^590069−1`.

Both74 constructions and75's12/13-positive constructions also use compact44,
with295,388 raw bytes. The75 signed sextic uses source34, not compact44.
No family licenses splicing its ports with compact54. In every family the
MF payload is already shifted once. Positive, natural and unrestricted
integer domains must remain distinct.

## Ordinary proof assessment

**68.** The simultaneous-positivity lemma
`x,y>0 iff exists t: xy−(t^2−x−y+1)^2>0` has a valid nearest-square proof.
Combining it with the three-variable representation of a positive integer
saves two integer witnesses; nesting it gives the26-variable degree16
tradeoff. The proof preserves existential solvability, not every guard
witness bijectively.

The free-Lucas finalizer removes an index carrier using an additional
fixed-residue orientation argument. Its necessary slice is explicit:
`6|A`, `B=3(mod4)`, `1<B<|A|/2−1`, `C=5(mod6)` and nonzero xi. The paired
recurrence modulo `A^2` excludes ranks±1; the residue modulo3 fixes the
remaining sign. The removed `A−2` congruence is recovered afterward. This
is a new argument alongside the inherited inputs from
[Sun's cited v1 paper](https://arxiv.org/html/2609.01594v1), not an unrestricted
version of its certificate theorem. The packet itself supplies a negative
control showing that the slice conditions cannot simply be deleted.

The commutative single-conclusion flow theorem is mathematically sound:
summing nonderivable coordinates separates a proposed positive flow from
the target. Its single-conclusion and nonnegative-coefficient hypotheses
are essential. The17-witness local branch relations and23-witness local
affine accumulator are not completed global consistency polynomials. The
global constructor remains uncompiled, unmaterialized and uncounted;
unbounded aggregation and two bounded-forall blocks still require a compiler.

**69.** The cone forces three strict signs to agree, and is positive on a
factor-two box. Completeness uses canonical native anchors to place weighted
F,alpha,C into that box. It is an existence reduction, not a bijection of
arbitrary old zeros. The subsequent sextic/octic polynomial eliminations
are bijective on their integer zero sets. Canonical bounds require the
actual source34 anchor geometry and actual rank-controlled rotation.

The positive merger's rational-integrality lemma is valid for adjacent
coefficients: `Q>1`, integer V and rational y satisfying
`Q*V^2−(Q−1)*y^2=1` force integral y. Its norm-one inverse step preserves
the reduced denominator and decreases nonzero integer `abs(V)`. This
closes the denominator gap that a resultant identity alone would leave.
The proof derives `V>1` from the first two carrier equations before using
the positive recovery. The shift `f=t+1` excludes rho=0. Its mod-four
unit argument needs even q, supplied by `J=6j+1` and the odd beta. Canonical
compact44 J is1 modulo6, so the restriction preserves completeness.

**74.** The adaptive modulus is `q^2*Y` after recovering `q^3|Y`.
The possible common divisor3 is removed from Y's already divisible
cofactor, giving modulus at least `q^4`; replacing this by a loose bound
`q^4/3` would not justify the index argument. The centered root merger
handles its zero-denominator branch algebraically, obtains integrality by
a monic rational-square argument and proves positivity only for the needed
canonical family. It restores the old transport as `z_old=z_new+1` with
`z_new>0`; this is a proved witness restoration, not an assumption about
every arbitrary old-z tuple.

**75.** The signed-power bootstrap removes a genuine scale coordinate before
monic projection. Its negative-X branch is excluded only after signed Pell
rank recovery; it does not assume positive X at the start. The relation
`q=−2^t` is incompatible with its fixed Mersenne congruence. The cleared
transport restores its old integer quotient by proving `q|Z`. Canonical
odd exponents justify the converse square coordinate. Its sextic projection
then has an integer-polynomial inverse. These arguments retain the stated
ordinary strong-rank and signed auxiliary-index lemmas.

No additional local mathematical flaw was identified in these arguments.
All four endpoint claims still rely on the ordinary native/compiler and
K215/refutation calibration. None supplies that complete Lean composition
or a derivation of the biconditional in the encoded object-language ZFC
calculus. Their copied formal-status notes are historical snapshots.

## Reproduction and independent checks

From each untouched original root, the supported command is `python verify.py`.
Packages68 and75 require SymPy; the existing review environment has1.14.0:

```
/tmp/proofs62ff-wave7-review-venv/bin/python verify.py
```

The75 default replay authenticates and extracts all eight retained originals
but does not execute their root verifiers. `--replay-originals` is the separate
optional command and was not needed for this review. Root75 rejects `-O`
deliberately and runs its selected optimized checks internally. The68 driver
also includes its selected `-O` checks. The69 driver supports full `-O` replay
as a separate command; this review ran the normal root replay, which already
includes its exact component audits. Package74 uses only the standard library.

Independent readers written during this review checked topology, complete
liveness, live witness use and charged operation counts of all six positive
candidate graphs above. A separate indexed-DAG reader checked all ten free
Lucas inputs and the exact481-operation breakdown301 multiplications,
155 additions and25 subtractions. Exact degree and universal correctness
are not inferred from those topology checks.

Normal root replays of69 and74 pass, including actual native numeral
reconstruction and source pins. The75 replay passes24 stages,194 sealed
files and11 byte-identical rebuilt artifacts. The68 root replay passes26
suites,233 sealed hashes,77 retained-member bindings and36 regenerated-byte
checks, including its complete ten-integer finalizer. The initial system
Python attempts for68/75 stopped only because SymPy was unavailable; both
complete replays pass in the existing SymPy environment. Finite replay results
establish the stated data/algebra checks, not consistency or an internal ZFC
derivation.

`WAVE10_NATIVE_REPLAY.json` records the four original archive hashes, exact
commands, replay counts and stdout hashes, alongside the independent topology
audit scope.
