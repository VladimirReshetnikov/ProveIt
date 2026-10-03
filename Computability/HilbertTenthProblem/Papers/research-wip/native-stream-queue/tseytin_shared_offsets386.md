# A shared selector prefix gives386 universal polynomial operations

The [source](tseytin_shared_offsets386.py) removes one multiplication
from the complete [387 compiler](tseytin_permuted_digits387.md), giving
**386=178M+208A**,372 certificate gates, five comparisons,62 positive
witnesses, one fixed positive program parameter A and ordinary positive
input x. Its propagated degree bound remains4712. The
[receipt](tseytin_shared_offsets386.json) records all four full schedules:

|Power products|Finalizer|Operations|M|A|Certificate|Comparisons|Degree bound|
|---|---|---:|---:|---:|---:|---:|---:|
|merged|anchor|386|178|208|372|5|4712|
|merged|SOS|386|178|208|372|5|9396|
|separate|anchor|388|178|210|371|6|4752|
|separate|SOS|388|178|210|371|6|9288|

These are **exact complete polynomial identities with the corresponding
387-parent forms on the same supplied integer coordinates**. Positive
domains, literal tiles, program numerals and ordinary-input interpretation
are identical. No new Pell sign, height or recoding theorem is required.
The established75-certificate/87-polynomial bounds remain separate.

The saving uses an additional common-offset decomposition outside the
architecture of the [120-permutation search](tseytin_zero_a_permutation_search.md).
That search's387 minimum remains an exact minimum for its stated
minimum-offset schedules. It was not a lower bound over this larger
class of linear expressions.

## 1. Two exact linear identities

Let h_i=Shat_i, define the already-paid copy prefixes

    S1=h0+h1, S2=h0+h1+h2, S3=h0+h1+h2+h3,
    S4=h0+h1+h2+h3+h4, C=h0+h1+h2+h3+h4+h5,

and the four commutation-pair sums

    A=h6+h7, B=h8+h9, E=h10+h11, F=h12+h13.

The source already computes

    P=C+A+B+E+F

as `c2_shared_selector_sum_3`. This definition depends only on the hats
and their paid selector prefixes; it does not depend on an affine-update
prefix or any value changed below.

The copy-offset form is

    W=5h0+4h1+3h2+2h3+h4=h0+S1+S2+S3+S4.

Subtracting C has a form with the same four-operation cost:

    W−C=h0+S1+S2+S3−h5.                            (1)

The shared offset portion for copies and the first four relations is

    W+A+2B+11E+19F
       =(W−C)+P+B+10E+18F.                        (2)

Both equations hold over all integers. They use no one-hot, positive,
Boolean, dyadic or chronology hypothesis. In(2), substituting
P=C+A+B+E+F gives the left side term by term.

The old left side requires four additions for W, three fixed-numeral
multiplications for2B,11E,19F, and four further additions. The new right
side requires three additions and one subtraction for W−C, two
multiplications for10E,18F, and four further additions. P and B were
already paid and remain live. This saves exactly one multiplication.
The remaining shared minima12,20,648 and the hat-offset subtraction45194
are unchanged, as are both oriented correction forms.

## 2. Literal guarded rewrite and private values

The source changes the following rows:

- `linear_sum__384`: replace addition of S4 by subtraction of h5;
- `linear_sum__385`: add the paid P in place of A;
- `linear_sum__386`: add B directly instead of2B;
- `linear_coefficient__367`: replace11E by10E;
- `linear_coefficient__369`: replace19F by18F.

It deletes the now-unused multiplication
`linear_coefficient__365=2B`. The complete subtotal at
`linear_sum__388` is identical by(2), so both affine update outputs and
all their downstream consumers agree. No external definition receives
a changed private prefix.

The canonical wrapper requires equality with the entire selected parent
packet, including its parameters, witness list, program recipe and both
comparison lists. A local `rewrite_rows(rows, exported=...)` helper
checks all defining copy-prefix, pair-sum, P and old-offset rows. It also
checks unique source names, exact consumers for every changed or erased
private register, and recursively rejects private names appearing in
exported roots, including nested dict/list/tuple structures. The wrapper
passes every active parameter, comparison and interface to this export
guard, then topologically sorts and checks the rebuilt full source.

The local helper proves only its guarded row identity. A host caller must
supply all exported roots, guard that host's own canonical contract and
perform its topological ordering; it does not obtain a universal theorem
merely by calling the helper.

Every old private value has an explicit recovery formula from unchanged
selector hats: W, W+A, W+A+2B, W+A+2B+11E,2B,11E,19F. The checker
restores precisely these seven values and compares every old source
register. This is not a claim that the private registers bearing reused
names retain their old intermediate values.

## 3. Complete identities, domains and degree bounds

All rows outside the guarded private fragment agree, and the fragment's
exported result is identical. Thus all word and exponent factors and all
ordinary comparison residuals agree on every supplied integer assignment.
Their complete merged/separate and anchor/SOS finalizers consequently
agree as integer polynomials. In particular the identity map is a
bijection between their full supplied positive zero sets, even before
restricting A to a valid program recipe.

The same valid387 program numeral therefore gives the same universal
ordinary-input relation. Its letter codes remain(a,b,c,d,e,#)=
(0,3,1,2,4,5), its copies remain#,e,b,d,c,a, and all18 oriented relation
tiles remain fixed. The sparse ten-gate query, exponent52 source,
wrong-power sign filter, binary zero-run bound10 and positive native
extensions all transfer directly from the parent. No endpoint number or
history witness is recompiled.

Each retained changed register is still a nonzero linear form of degree
one in the supplied selector hats. Every unchanged register therefore
has the same propagated degree as before. The exact all-integer norm
cancellations used by the parent degree checker are unchanged. The
checker independently propagates the new source and compares every
retained degree-dictionary entry; the sole removed entry is the deleted
2B multiplication. It also compares the complete factor, residual and
final-output bound dictionaries. These remain propagated bounds, not
claims of exact expanded universal polynomial degrees.

## 4. Reproducible evidence

`build(merge_units=True|False)` emits the canonical certificate;
`polynomial_source(packet,sum_of_squares=True|False)` emits its complete
finalizer. Full packet equality guards the finalizer and degree APIs.
The receipt stores all four literal sources, opcode counts, comparisons,
domains and source digests. Running the source with no arguments compares
a fresh deterministic result with the receipt; `--write` regenerates it.

The two linear identities are checked by exact symbolic expansion. The
source audit verifies192 complete private-restoration register maps
(96 signed),384 parent/manual complete outputs(192 signed), and12
zero-decoded-selector cases across both merged and separate interfaces.
Every full schedule passes opcode and output-reachability checks, and
all retained degree entries agree. Bad literal rows, additional private
consumers, nested exports and altered canonical packets are rejected.
These are algebraic/source checks, not newly materialized complete Pell
zeros. The universal theorem is inherited by the exact identity above.

Author writer98723 and a separate fresh replay23761 passed. All49
malformed callers are rejected, and four local links and whitespace pass.
Independent review evidence follows.

Native's independent full proof/source/dependency review and fresh96458
passed with no findings:128 complete private/restored-register maps
(64 signed),256 parent/direct-finalizer outputs(128 signed),16 zero-selector
cases, all four degree/opcode/closure ledgers and38 independent malformed
caller checks. Root's separate fresh64616 replay also passed.
