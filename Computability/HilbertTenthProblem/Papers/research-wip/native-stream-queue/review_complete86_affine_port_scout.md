# Independent review of the complete86 affine-port scout

**PASS; no requested source or proof correction.** The frozen
[author report](complete86_affine_port_scout.md) establishes a bounded negative
result: all 874 distinct complete DAGs in its specified family cost at least
86 operations. Its 127 best sources all cost 48 multiplications and 38
additions/subtractions. This is not a general circuit lower bound. The
separate 85-operation complement-coordinate expression remains an unproved
positive-domain lead in this frozen report; later obstruction work is outside
this review.

The [independent checker](review_complete86_affine_port_scout.py) and
[receipt](review_complete86_affine_port_scout.json) authenticate the author
Python/JSON/proof trio and all twelve recorded dependency blobs. They import
and execute no author code or historical compiler, and invoke no historical
suite. The entire author source and note were read. The independent checker
parses the actual complete86 source from its authenticated parent receipt.

## Actual source, coordinates, and finite family

The selected parent is the normalized first form in
`complete86_factored_first_root.json`, not a different ordinary-strong
87-operation source. Independent constant/unit folding and commutative CSE
leave its complete source at 48M+38A. All nineteen witness coordinates, the
ordinary input `x`, and the six fixed compiler-numeral ports remain live.
The meanings and admissible fixed-numeral slices are inherited unchanged.
No input equation, norm factor, strong condition, or finalizer is omitted.

I independently reconstructed all six specified joint-root schedules at the
actual ports `D1`, `a4m5`, and `exponent_partial`, proving their twelve root
identities by exact coefficient arithmetic. Their two output ports are the
unchanged main and input roots. The first three schedules cost 86 and the
last three cost 87, exactly as reported.

I then independently enumerated the declared one-step grammar: signed
addition reassociation/permutation, product reassociation, distribution,
immediate common-factor extraction, difference of squares, and its conjugate
product reverse. The generator does not perform recursive optimization or
assume zero equations. Every complete emitted source is independently
recounted and checked for all-gate and all-free-port liveness. The census is:

| Seed | Complete sources | 86 | 87 | 88 | 89 |
|---|---:|---:|---:|---:|---:|
| original | 142 | 43 | 77 | 22 | 0 |
| distributed left | 143 | 44 | 77 | 22 | 0 |
| distributed right | 144 | 45 | 77 | 22 | 0 |
| through input, left | 153 | 0 | 48 | 83 | 22 |
| through input, right | 153 | 0 | 48 | 83 | 22 |
| recover rho product | 147 | 0 | 48 | 77 | 22 |

Thus 882 within-seed sources collapse to 874 across seeds, from 1,300 raw
local-move instances. The independent minimum and all 127 attaining ledgers
match the author. The 882 source recounts charge 77,043 gates in aggregate.
These repeated counts include shared sources in different seeds and are not
a claim of 882 globally distinct circuits.

The independent engine uses its own commutative canonical ordering and
register names. It compares normalized complete DAG membership, counts, and
per-seed histograms rather than claiming byte equality of its differently
named outputs with the author's ordered census hashes. All six saved complete
seed sources and the saved best source parse to members of the independently
reconstructed family. The two additional saved full sources are reviewed
separately below. The authenticated author receipt supplies its literal
source-hash list.

## Why the cut proofs establish complete polynomial equality

Every generated local replacement is independently checked as an exact
polynomial identity at its proposed computed-port cuts: 1,300 occurrence
proofs, in addition to the twelve seed-root identities. First, the checker
tries the stronger identity with cut values independent. If a cut contains
another proposed cut and that stronger identity fails, it expands the
dependent cut and retries at the remaining boundary. This is ordinary
polynomial substitution, not an assumption that dependent source values are
independent.

A proved equal expression can replace its old node at every shared consumer.
DAG substitution therefore preserves every downstream output; the emitter's
only additional transformations are constant identities, zero/unit folding,
commutative ordering, and shared-expression reuse. This proves the entire
final eight-factor product-minus-one identity for each complete candidate,
not just agreement of selected ports on the parent's zero set. No positive
coordinate is redefined by these 874 rewrites. The parent's positive zero set
and uniform exact degree 179 transfer by polynomial identity. No independent
new degree theorem or universal zero is claimed.

As supplementary evidence, the independent checker makes 2,646 complete
output comparisons: one positive integer, one signed integer, and one rational
assignment for each of the 882 within-seed sources. These tests support the
source proof; they do not replace it or construct a universal halting witness.

## Two separate transformations and the 85 boundary

The paid gap rewrite uses `q=repunit+1` to identify

```
repunit*u + (u-Z) = q*u-Z.
```

I checked the exact overlapping-cut identity and the entire emitted source.
It still costs 86. The shared `u-Z` expression has other consumers, so a local
algebra simplification alone does not remove a complete gate here.

The original supplied `F` has exactly one literal consumer, `q_minus_F=q-F`.
The author's 85-operation expression replaces that private result by a new
supplied `complement_u`. I independently checked its complete source, exact
cost, and the full signed polynomial pullback obtained from
`F=q-complement_u`. At the cut, `q-(q-complement_u)=complement_u`; after this
proved cancellation, the whole substituted DAG is exactly the saved85 DAG.

This does not prove a positive-coordinate inverse. The recorded tuple has
all new supplied values positive, restores `F=-1`, and has a nonzero complete
polynomial value. I verified each of these facts. It demonstrates failure of
unconditional positive restoration only, and is **not** a full-zero
counterexample. The author clearly states the unresolved obligation
`complement_u<q` at every new positive full zero and does not invoke the parent
positive theorem before proving it. The report consequently certifies neither
85 operations nor a new input language. This review does not import or settle
any later complement-85 investigation.

## Reproduction and limits

The reviewer source and receipt are deterministic. Three private subject-byte
mutations and execution under `-O` are rejected. Dependency hashes are checked
before parsing their source/JSON contents; no stale module or bytecode loader
is involved. The author exposes a research CLI rather than a maintained
hostile-packet API, and the review makes no stronger API claim.

```sh
python review_complete86_affine_port_scout.py \
  --root /path/to/native-stream-queue \
  --subject-root /path/to/author-trio \
  --expect review_complete86_affine_port_scout.json
```

`--subject-root` defaults to the reviewer's sibling directory; `--output FILE`
writes a fresh receipt. No repository file or Git state was changed. Earlier
large arithmetic families were authenticated as provenance, not replayed.
