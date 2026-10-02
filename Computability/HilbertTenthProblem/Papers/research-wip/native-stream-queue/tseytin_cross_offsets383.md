# Opposite-coordinate selector sums give383 universal operations

The [source](tseytin_cross_offsets383.py) removes two multiplications
from the complete [global-unit385 compiler](tseytin_global_bound_unit385.md).
The resulting polynomial has **383=176M+207A operations**,372 certificate
gates, four comparisons,62 positive witnesses, one fixed positive program
parameter and ordinary positive input. Its propagated degree bound remains
4714. Every supplied coordinate and the complete integer polynomial are
identical to the parent; no new semantic or sign theorem is needed.

The same local identity applies to the [equality386 parent](tseytin_shared_offsets386.md),
giving384=176M+208A and degree at most4712. The
[receipt](tseytin_cross_offsets383.json) includes eight full schedules:

|Global bound|Power products|Certificate|Comparisons|Polynomial operations|M|A|Anchor degree bound|SOS degree bound|
|---|---|---:|---:|---:|---:|---:|---:|---:|
|unit|merged|372|4|383|176|207|4714|9400|
|unit|separate|371|5|385|176|209|4754|9292|
|equality|merged|370|5|384|176|208|4712|9396|
|equality|separate|369|6|386|176|210|4752|9288|

Anchor and SOS have the same counts in each row. These bounds are
propagated upper bounds, not claims of exact expanded polynomial degree.
The established75-certificate/87-polynomial record remains separate.

## 1. Reuse the opposite side's paid slope-class sums

Write h_i=Shat_i. The actual24-tile source already computes

    U=h14+h16, V=h15+h17,
    CU=U+h21+h23, CV=V+h20+h22.                        (1)

Their literal registers are `group_sum__221`, `group_sum__228`,
`group_sum__223` and `group_sum__230`. They are paid by the slope-class
selection structure and remain live regardless of the offset rewrite.
The common affine offset also contains

    12(h14+h15)+20(h16+h17).                           (2)

The coordinate-specific portions considered here are

    old_U=255U−3h14+512h20+1024h22,
    old_V=255V−3h15+512h21+1024h23.                    (3)

All other common and coordinate-specific terms remain untouched.
Increase the two common coefficients in(2) from12,20 to267,275. This
adds exactly255(U+V) to the shared offset without adding any gate.
Then use

    new_U=−767V−3h14+512(CV+h22),
    new_V=−767U−3h15+512(CU+h23).                     (4)

By(1), over all integers,

    new_U+255(U+V)=old_U,
    new_V+255(U+V)=old_V.                             (5)

For example the coefficient of V in the first identity is
−767+512+255=0, while512(CV+h22) supplies512h20+1024h22.
The two identities use no positive, one-hot, native, chronology or valid
program assumption. Reusing sums from the opposite coordinate is crucial:
CV contains precisely the two U-side terminal corrections, and conversely.

Each side originally uses three multiplications for the255,512,1024
terms and two additions to combine them, besides its unchanged−3h term.
The replacement uses two multiplications, one addition inside CV+h22
or CU+h23, and one addition to combine that product with the−767 term.
Thus each side saves exactly one multiplication, with no net addition.
The two altered common coefficient multiplications remain fully charged.
Negative fixed numerals such as−767 count as fixed coefficients, just
as existing negative slope coefficients do.

## 2. Exact literal rewrite and private register restoration

The common coefficient rows `linear_coefficient__371` and `__373`
change to267 and275. The old255 multiplications `__398` and `__417`
become−767 times the opposite paid pair sum. The old512 multiplications
`__400` and `__419` become additions CV+h22 and CU+h23; the old1024
multiplications `__401` and `__420` become512 times those new sums.
Two now-unused accumulation rows, `linear_sum__408` and `__427`, are
deleted. The final coordinate accumulation rows read the preceding
unchanged subtotal directly.

The shared offset itself changes. Its later private accumulations and
the two private coordinate subtotals also change. Only their combined
outputs `linear_constant__411` and `linear_constant__430` are claimed
identical. Equations(5) prove those two exact boundary identities.
Consequently both chronological transport expressions and every complete
factor/comparison/finalizer remain identical.

The local `rewrite_rows(rows,exported=...)` helper checks the literal
paid sums, all affected old rows and the two boundary additions. It
checks every changed or deleted private register's complete consumer set
and recursively rejects any such name in exported metadata/comparisons.
It also requires unique source names. This prevents changed private
prefixes from leaking into another host calculation. All22 affected old
private values can be restored by replaying their old local definitions
from unchanged external values, including the two deleted accumulations.

A local row identity is not a theorem about an arbitrary host. The public
wrapper additionally requires equality with the complete selected385 or
386 canonical packet, including every witness, comparison, program recipe
and interface. It passes all active exports to the local guard, sorts
the resulting graph and checks every operand. The full finalizer and
degree APIs likewise require the complete canonical successor packet.

## 3. Complete identity, domains and universality

For either global-bound choice, either power-product choice, and either
finalizer, the corresponding old and new polynomials agree over every
supplied integer tuple. Their positive domains and program parameters
are identical. Therefore the identity map is a bijection of full supplied
positive zero sets even before restricting to valid program numerals.

The selected parent's universal theorem transfers immediately. In
particular the valid permuted-digit program recipe and ordinary input x
are unchanged. The native sign, exponent residue, input-height and
chronology arguments remain those of the frozen parent. This identity
does not recompile any history or rebuild any private Pell witness.

The distinction between the global unit and equality choices remains
as before: their mutual relation shifts the global-bound witness by1
on valid slices, while this offset rewrite itself is the identity on
supplied coordinates separately in either choice.

## 4. Degree and reproducible evidence

All changed private registers remain nonzero linear forms of the selector
hats. Every retained register therefore keeps its degree propagation;
only the two deleted degree-one entries disappear. The unchanged guarded
norm cancellations and factor/residual ledgers give exactly the same
propagated output bounds as the selected parents. No equation at zeros
is used for this degree accounting.

The checker symbolically evaluates the actual local fragment with all
external operands independent, proving both boundary identities and the
three opposite private shifts. Its complete execution checks restore
every old source register, compare both boundary values and compare every
parent/finalizer polynomial with a separately assembled factor formula.
Positive and signed assignments and zero-decoded-selector cases are
included. Every one of the eight sources passes literal count, degree
and full output-reachability checks. Malformed local rows, consumers,
exports and canonical host packets are rejected.

These algebraic checks prove the stated rewrite and corroborate its
explicit identity; they are not materialized complete compiled Pell zeros.
The universal theorem follows from the exact identity and the reviewed
parents. No optimum over other linear circuits is asserted.

Author writer41361 and fresh51766 passed:256 complete private-restoration
register maps(128 signed),512 parent/manual output identities(256 signed),
16 zero-decoded-selector cases, five exact symbolic fragment identities
and all eight source/degree/liveness ledgers.

Native's independent full proof/source/dependency review and fresh18620
passed with no findings. Its separate executor checked three symbolic
identities,192 manual private-register restorations(96 signed),384
complete parent/direct-finalizer outputs(192 signed),32 zero-selector
cases, all eight independent cancelled-norm degree/opcode/closure/domain
ledgers,81 malformed callers and four local links. These checks retain
the algebraic scope stated above.
