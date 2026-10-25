# Exact post-centered partial sums at the accepted signed-cap equation

This is a separate code-only checkpoint. Neither new program has been
imported, compiled or executed and no grouped artifact has been emitted.
The input is the COMPLETE centered equation in the immutable accepted packet
`research/signed-pell-cap-projections`, manifest
`8d8fdd07fece21e07bd309a36c36c5f3602618de8e723378da1b1bcf78d9f06f`.
The ordinary/static grouping packet is immutable at manifest
`703bc45994f8816012f2436c5488e728bc91ef1b8505825e22c6a752bc1ba848`.
Its PROPOSAL.md supplies the general extension theorem and STATIC.json binds
the full selected prospective coefficient vector. Manifest member values in
that packet contain both SHA256 and byte length; both must be authenticated.

## 1. Whole old chart and the specified errors

Write x0,...,x358 for the accepted unrestricted integer coordinates and
r0,...,r221 for its complete quadratic residuals. Its equation is

    Qold(x)=sum_(i=0..221) ri(x)^2=0.

The selected old pool is row130, with label index_cap.joint_residue. Its
complete polynomial is sum_(j=0..15) ej^2-x158*x247, where

    e0=x169-x0,
    e1=x174-2x0-2x1-2x2-2x3,
    e2=x181-x0-x4,
    e3=x188-x10, e4=x194-x11, e5=x198-x12,
    e6=x202-x13, e7=x206-x14, e8=x210-x2,
    e9=x214-x15, e10=x218-x16, e11=x222-x1,
    e12=x226-x17, e13=x230-x18, e14=x234-x105,
    e15=x239-x157.

These are centered-coordinate identities, not raw-source assumptions. The
independent checker must collect the whole old pool and whole old quartic
before using them. Every old equation header, variable attribute and residual
label is retained except the explicitly declared successor schema/variant
and exact parent-binding metadata. Every old coordinate keeps its index.

## 2. Four pool sums and one frame sum

Partition the sixteen errors exactly once, in the fixed order

    I0=[2,0,3], I1=[4,5,6,7], I2=[8,9,10,11],
    I3=[12,13,14,15], I4=[1].

Let Gi=sum_(j in Ii) ej^2. Introduce the unrestricted integers x359,...,x362,
replace only old row130 by

    P=x359+x360+x361+x362+G4-x158*x247,

and append the definitions Di=x_(359+i)-Gi, i=0,...,3.

For the frame take the COMPLETE47 nonzero monomials of actual old row186,
label shared.frame_definition. Sort their coordinate tuples lexicographically,
with the constant tuple first, rotate the list left by one position and cut
after24 entries. Let L be the sum of those first24 terms and R the sum of
the remaining23. Thus L+R=r186 coefficient-for-coefficient. L starts with
8*x0 and ends with -2*x16^2; the constant -16 belongs to R. Full coefficient
lists, not these endpoint descriptions, define the split.

Introduce unrestricted x363. Replace only row186 by U=x363+R and append
D4=x363-L. Retain the old222 residual positions, changing exactly130 and186;
append D0,...,D4 at222,...,226. Do not reorder or compact old coordinates,
change any old sign graph, alter a power request, or run elimination.

## 3. Universal reconstruction and zero-set bijection

For EVERY integer assignment to all old and new coordinates,

    P-D0-D1-D2-D3=r130,       U-D4=r186.

All other old residuals are literal unchanged rows. At a new SOS zero every
residual is zero, so these identities recover every old residual. Forgetting
the five new coordinates therefore gives a zero of the exact accepted old
equation at the same complete old tuple, including every old private witness.

Conversely, at any old zero append

    (x359,x360,x361,x362,x363)=(G0,G1,G2,G3,L).

All five definitions are zero, both consumers equal their old residuals and
the remaining residuals are unchanged. This is a new zero. Each definition
has unit coefficient1 on its own fresh coordinate and depends otherwise only
on old coordinates. Thus the extension is unique and is inverse to forgetting
the five coordinates on zero sets. No sign, boundedness, factorial, power,
Pell, native-calibration or coefficient-tuple premise is used in this step.

Each fresh coordinate occurs exactly twice: in its one definition and in
consumer130 (the first four) or186 (the fifth). It occurs linearly in both,
and nowhere in an old sign graph, power port, frame atom list or other row.
No positivity is silently imposed on the frame partial sum or any new sum.

## 4. The complete polynomial changes, with an exact identity

Let Qnew be the sum of squares of the complete new residual list and let
D=D0+D1+D2+D3. Universally,

    Qnew-Qold = 2P*D-2*sum_(0<=i<j<=3) Di*Dj +2U*D4.

Indeed r130=P-D, so P^2+sum_(i=0..3)Di^2-r130^2 is the first two terms.
Likewise r186=U-D4, giving U^2+D4^2-r186^2=2U*D4. Every other old square
cancels identically. Qnew=Qold is NOT claimed. Substituting the five unique
extension polynomials into the WHOLE Qnew does give Qold coefficientwise.

All Gi,L,R have integral coefficients and degree at most2. Every new residual
is therefore quadratic and its SOS has degree at most4. A full actual
coefficient collection must verify the final degree, support, height, all
headers and every declared/used coordinate. The earlier static calculation
is a pinned comparator, not a substitute for those actual artifact checks.
The checker uses triangular square collection, independently of the
materializer's full ordered multiplication, and binds the entire sparse
coefficient vector. No sampled evaluation establishes polynomial equality.

## 5. Inherited exact maps and arithmetic calibration

The complete new-to-old map first forgets five coordinates. The accepted old
chain then applies, in its existing order: inverse centered translation,
inverse initial T translation, all published monic restorations, and the
accepted Horn private-witness reconstruction. The new packet must retain in
full both translation certificates, the complete monic certificate, the
complete Horn witness map, old source TRANSFORM, factorization certificate
and domain metadata, each with its exact accepted whole-file hash.

Old free-coordinate choices and all old chart coordinates are fixed by this
post-chart extension. The inherited Horn reconstruction's original scope is
unchanged: it may overwrite obsolete source witnesses, and it never becomes
an identity on every old pre-Horn witness. No new inverse, omission, sign
deduction or numerical optimizer result is inferred for that older stage.

Consequently the exact old359 chart and this specified extension have
equivalent integer zero sets by a unique extension, at every whole native
coefficient tuple licensed by that old chart. The parent already supplies the
ordinary C222/refutation calibration; this theorem adds no source semantics
or new formal Lean endpoint. The fixed inherited contracts remain
KEndpoint.c222_iff_zf_refutation and
ConstructibleChoice.zf_refutation_iff_zfc_refutation. No canonical compact
page or source proof is modified.

## 6. Required actual checks and execution hold

The new checker must independently bind the complete old input and both
changed rows; every unchanged row/header/variable; all new definitions,
metadata and occurrences; all complete inherited maps; every old-row
reconstruction and unique-extension identity; the full SOS difference and
whole-polynomial substitution; the complete collected quartic and census;
and every output length/hash in a closed data index. Its corruption controls
must mutate actual artifacts, including old/new rows, headers, maps, full
polynomial coefficients and metadata. Pure normal/optimized rebuilds must
match every generated byte. Both full static reviews and explicit root
release are required BEFORE importing, compiling or executing either new
program. No optimizer, factorizer, projection or centering is part of it.
