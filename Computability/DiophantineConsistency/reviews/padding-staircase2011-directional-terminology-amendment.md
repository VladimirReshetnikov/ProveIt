# Actual directional calibration of the accepted length2011 proof

Reviewer: `/root/complemented47_review`. This is a separate terminology and
interface amendment. It leaves every frozen proof, equation, coefficient,
program and prior review byte unchanged. It records the semantic audit
prompted by the failed marker996 proposal; it does not accept that proposal.

## Exact sources and review scope

The accepted ordinary proof is
`research/padding-staircase-independent/PROOF.md`, SHA256
`69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.
Its final finite verifier, certificate and README respectively have hashes
`56b3865237699c486bbd940a88e94387d26092ac2cf89cd7f9097206dd8fb975`,
`fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f`, and
`3b55360ad2782409984b7c993a93519449c4ba6dc2eaf76a5b8aa18c871f45b4`.
The entire doubled coefficient-array hash is
`43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93`.

I re-read all directional, language-transfer, label-decoding, phase,
occupation, canonical-word and safe-subset passages of the2011 proof,
searched its entire text and final verifier/README/page for directional
terms, and inspected the actual coefficient and copy formulas. The full
ordinary proof and final verifier had already received my separate complete
review. For this amendment I also read the complete language, soundness,
helical completeness and matching-interface sections of the inert sources
under `con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/`:

| Source | SHA256 |
| --- | --- |
|`WANG943_COEFFICIENTS.md`|`1d0f5a5b77a91070617bacdd63c87de312770e680612115ba2828a112969001d`|
|`package27_complete_transfer.md`|`d4071b7edf9fb6cf9560b1abcadb88c854c80dd9aca752516bfbd26f7ea2172a`|
|`BLANK_HELICAL_PROOF.md`|`b0595216f23b84b786660aa07e6b0550de68187604a18c14ac1d1a4667cd25e7`|

No incoming program was executed. The directly relevant directed-signal
language is the Wang943 source, rather than an inferred symmetry of its
machine computation.

## The actual34-bit map and the two wording corrections

The tile coordinates are `(w,n,p,s)=(West,North,East,South)`. The doubled
selector coefficient is exactly

```
2 + 2048*(1+w+2^8*n+2^17*p+2^25*s).
```

The clause lemma recovers the complementary34-bit value. Hence the
displayed physical control coefficients determine the following full map:

| Physical field | Coefficient divided by2048 | Recovered label |
| --- | --- | --- |
|`942+j`, `0<=j<=8`|`2^(25+j)`|bit j of `511-s` (South)|
|`960+j`, `0<=j<=8`|`2^(8+j)`|bit j of `511-n` (North)|
|`969+j`, `0<=j<=7`|`2^(17+j)`|bit j of `255-p` (East)|
|`978+j`, `0<=j<=7`|`2^j`|bit j of `255-w` (West)|

This accounts for every34 label coefficient, not just the two disputed
bits. Dummy977 and marker1004 have coefficient zero and are not labels.
Start is `(2,435,3,1)`, so its recovered `(West,North,East,South)` tuple is
`(253,76,252,510)`.

Two phrases in the frozen2011 proof require correction:

1. At line169, position978 is called the weighted **east-bit0** label.
   It is the weighted **West-bit0** label.
2. At line343, the bare18 source for targets987..994 is called the
   intended **west** label. Its source969..976 is the **East** label.

The explicit formulas immediately surrounding these phrases are correct.
The final verifier's `SPEC` dictionary retains the historical names
`west:969`, `east:978`, and `west_copy:18`. These are misleading names for
numeric locations; they do not identify the decoded coordinates. The
actual coefficient formulas, the whole array and the tested physical
source lists determine their meaning. The2011 final verifier adds no
East/West-coordinate-specific tile predicate using these names. Its
README and equation page contain no corresponding incorrect directional
assertion. The same two phrases also occur in the retained phase-split2471
parent, at lines164 and330; this amendment does not rewrite that parent.

## Exact packed source/target orientation

Write the cyclic packed word as `C=sum_i C_i B^i`, with indices modulo N.
Multiplication by B takes its contribution at target cell i from source
cell `i-1`. Once the temporal field alignment is established, multiplication
by `B^a` takes the temporal contribution from `i-a`. A predecessor here is
an arithmetic source index; it is not a claim that it lies west or earlier
in machine time.

At target960+j, the parity equation has exactly

```
current(942+j) + temporal(960+j) + even reflection = 0 mod2.
```

Zero incoming carry and Boolean inputs therefore give
`South_i=North_(i-a)` in full9-bit complemented labels. At target987+j,
the bare18 and B*rho^9 contributions give exactly

```
current(969+j) + spatial(978+j) + even reflection = 0 mod2,
```

hence `East_i=West_(i-1)` in full8-bit complemented labels. Inverse
complementation preserves each equality and gives the same two equations
for the original tile colors. Neither equation swaps a tile's coordinates.

These are precisely the original directed Wang matching relations. In
`WANG943_COEFFICIENTS.md` section2.4, the canonical cyclic coordinate is

```
i = -(x-x_Start) - width*(t-1) mod N.
```

The right/east neighbor has index `i-1`; the next computation row, on the
South side of a tile, has index `i-width`. Thus the current packed spatial
and temporal sources have exactly the inherited orientations. Equivalently,
for soundness a decoded word with arbitrary temporal stride a pulls back
along `i=-x-a*t` to a periodic plane. The two equations above become East
matched to the right neighbor's West and South matched to the next row's
North. This works without `a|N` or any coprimality assumption. The cyclic
ordering increases westward and opposite forward computation time; no
reflection of an individual tile or reversal of the machine transitions
is performed. A differently ordered list could be completely reindexed,
but that optional reindexing is unnecessary here.

For completeness the same source constructs
`tile(x,t)=G(x mod width,(t+floor(x/width)) mod height)`. Its nine seam
types accept the independent pairs of horizontal seam colors, and its
periods are `(width,-1)` and `(0,height)`. The displayed cyclic coordinate
therefore supplies both exact packed equalities, with one Start at0,
arbitrarily independently padded dimensions and temporal multiplier
`B^width`. The coefficient permutation and complement bijections preserve
this entire tile assignment and all seams. No assumption of a symmetric
tile language is needed in either direction.

## Audit of stronger local premises in2011

The2011 fractional-phase argument uses `1+E_1004` at the forced Start
marker. The only odd non-temporal marker source is selector0: the other
bare source986 and spatial source995 are absent. Its even background and
incoming-carry reset are proved without decoded colors. Thus it uses no
particular East or West bit. After alignment its canonical marker is the
shifted Start indicator alone, `a_(i-a)=x_(0,i)`, and remains Boolean.

The offset19 and20 arguments use all9 **South** bits at942..950 and the
North-copy targets960..968. Their physical coefficients and StartSouth510
are correctly calibrated. The terminal-tile conditions likewise concern
South, not either horizontal coordinate. The temporal nonzero-stride
test uses StartNorth76 differing from StartSouth510. None of these
premises is changed by the horizontal wording correction.

Occupation propagation uses full `East_i=West_(i-1)`, with both genuine
horizontal colors positive and empty colors zero. It consequently
propagates through the entire one-cell rotation cycle in the required
direction. The directed-signal soundness proof then applies to the plane
with the exact orientation just established, including its initialization
chain and literal left/right machine signals. This is stronger than
merely observing that two colors are equal.

All clause, predecessor, padding, top-field and safe-subset bounds depend
on the explicit coefficient values and Boolean support, or on the whole
decoded label sum. The dummy977-to978 contribution is explicitly
`c'_978`, regardless of its name. No2011 step asserts that this West bit
vanishes at Start or adds it to Start to form a Boolean marker. The
changed dummy outputs lie above the padding band and leave all physical
label copies and the Start-marker identity intact. Canonical dummy tuning
and the exact rank/controller formulas therefore retain their proved
interfaces.

The accepted2011 source thus needs the two terminology corrections and
this explicit orientation clarification, but its stated numeric tuple,
native copy equalities and complete language transfer remain valid under
the same retained ordinary contracts. This finding does **not** repair
marker996: there the newly added local premise really required the bit
at978 to vanish at Start, whereas its actual West bit is1. The separate
marker996 correction receipt records my missed preliminary calibration
and the failed candidate. Any997 successor still requires a new complete
review from its actual coefficient map.
