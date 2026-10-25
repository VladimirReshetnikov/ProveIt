# Independent diagnosis of the first coordinate25 V checker failure

**CONFIRMED FIRST FAILURE.** The ordinary row30 table and checker literal
have an incorrect new linear c coefficient: -24 must be -48 for the
specified composition P(Vz). The source checker correctly rejected its
own inconsistent ordinary literal at prepare/check.py:470. No candidate
application, helper, import, AST, collector, evaluator, search, Lean or
PDF was run for this diagnosis; all reasoning below is hand algebra
from immutable source and previously captured raw data.

I authored the original independent FULL static PASS pair. That review
explicitly claimed every affected linear term was verified, but missed
this incorrect coefficient. That claim and PASS verdict were wrong.
The original reports remain byte-for-byte immutable as failed review
records; this separate finding does not rewrite their history or imply
that the original review discovered the problem. The actual first
independent checker execution exposed it. ROOT observed the successful
producer exit0 and failed checker exit1; I inspected their retained
captures and recorded observations, without independently running or
observing another candidate process.

## Exact evidence and stopping point

The complete first-failure packet is
research/second-pair-sum-gate-shear-first-failure, committed7848830a7d.
Its MANIFEST is3807 bytes/SHA256
fc8676225660ab9219d5a2ed0c850bbd2ce52db70389da7fdcb50c9b219acba1.
All23 payloads/597128 bytes and24 whole files/600935 bytes authenticate,
including13 unverified produced artifacts, five original captures and
five metadata files. Actual Git commit manifest bytes agree. All20
verbatim copy associations equal their complete original bytes.

The original source remains HOLD2310 bytes/SHA256
32677cb70a9547c573c425aa2aade8682e08e4a7282bb5914d7f599f3a9938a9,
PINS195063 bytes/SHA256
47eda12cfd11e68419af59c8a68974492c92b89fa1017c9e8597e0c118d8e9ca.
Every one of540 original source snapshot records and20 complete trees/
418 members is unchanged. The eight held source files, ten original
ordinary/static review/acceptance/release records and this reviewer's
original pair match the first-failure provenance. The original snapshot
INPUTS is98683 bytes/SHA256
e9c565a326c1b9061178216b63beb10657ab4c9ded89da4fde664e75b18f95e6.
The22 remaining original output/capture paths, including the failed
checker receipt, are absent. No source, historical report, data or closed
packet was edited, repaired, deleted or resealed by this review.

The full checker stderr is1042 bytes/SHA256
dd8cc9b7db067087627c5e364c7d3e05748e549e8fb8cb3717f9f941c4f61614.
It records main:824 calling prepare, then prepare:470 raising
ValueError: ordinary/unchanged full row. Checker stdout is empty and no
checker JSON exists. The producer JSON equals its entire stdout, stderr
is empty and all13 produced data hashes match its receipt. Those facts
are provenance and successful materialization evidence, not independent
acceptance of the produced polynomial or its provisional exact metrics.

The failing prepare call is the plain profile, because contexts is built
in order plain, weighted. It stops before full expected quartic forward/
inverse checks, actual saved-successor verification or any negative/valid
control. No optimized checker, rebuild or fresh application followed.
The traceback itself does not print the row index; the precise row30
diagnosis follows from the frozen code, ordered loop and independent hand
rederivation below, rather than from an imaginary index in stderr.

## Direct row30 derivation

Write b=z11,c=z12,p=z25,r=z27, y46=z46. The accepted old U row30 in
BOTH profiles is

    y46-(2b-2c+2p+2r)^2+24b-24c+24p+24r-35.

Its full raw coefficient array is preserved in the companion JSON.
The specified map replaces p by p-b-c. Its quadratic argument becomes

    2b-2c+2(p-b-c)+2r = -4c+2p+2r.

The complete linear part independently becomes

    24b-24c+24(p-b-c)+24r
    =24b-24c+24p-24b-24c+24r
    =-48c+24p+24r.

The constant-35 and output y46 remain. Thus the correct composed row is

    y46-(-4c+2p+2r)^2-48c+24p+24r-35.

The frozen ordinary README row91 and checker new literal at156–157
instead use -24c. The producer's existing raw row30 contains exactly
[-48,[12]] in both profiles and otherwise agrees with the corrected
expression. This is consistent with factor substitution, which does not
read the erroneous ordinary literal. No producer rerun was used.

The ordered prepare loop at469–471 compares multinomial-composed source
rows with ordinary literals. Every affected row before30 is correct by
the ledger below; rows not reading25 are fixed by substitution. At row30
its composed c coefficient is-48 and its literal coefficient is-24, so
the equality at470 is false. This accounts for the observed first error
without modifying or executing the checker.

## Fresh hand ledger for every affected quadratic and linear term

For any old square argument with b,c,p coefficients(B,C,k), substitution
changes these to(B-k,C-k,k). Independently, an old residual linear part
with coefficients(U,V,l) changes to(U-l,V-l,l). Every other coefficient,
output and constant stays fixed, except the row9 output p itself supplies
l=1 and therefore creates linear -b-c. I checked every full old and
produced row in both profiles; the complete raw arrays agree between
profiles. This ledger performs the two subtractions separately for each
row and is not a reuse of the old PASS assertion.

|Row|Old square(b,c,p)|New square(b,c,p)|Old linear(b,c,p)|New linear(b,c,p)|
|---|---|---|---|---|
|9|(1,1,0)|(1,1,0)|(0,0,1)|(-1,-1,1)|
|10|(2,0,2)|(0,-2,2)|(12,0,12)|(0,-12,12)|
|14|(0,2,2)|(-2,0,2)|(0,8,8)|(-8,0,8)|
|16|(6,8,2)|(4,6,2)|(-36,-48,-12)|(-24,-36,-12)|
|19|(-4,2,2)|(-6,0,2)|(-32,12,14)|(-46,-2,14)|
|26|(8,6,2)|(6,4,2)|(8,6,2)|(6,4,2)|
|30|(2,-2,2)|(0,-4,2)|(24,-24,24)|(0,-48,24)|
|33|(2,0,2)|(0,-2,2)|(8,0,8)|(0,-8,8)|
|34|(4,1,4)|(0,-3,4)|(0,0,0)|(0,0,0)|
|45|(2,0,2)|(0,-2,2)|(4,0,4)|(0,-4,4)|
|46|(5,0,4)|(1,-4,4)|(1,0,0)|(1,0,0)|

All other square-argument and residual linear coefficients were also
checked directly, including row19's -19a+16u-r and new-2c, row16's-5a,
row14's-8a and row46's unchanged linear b. Outputs are25,26,30,32,35,42,
46,49,50,61,62 and constants-2,-9,-6,-10,-12,-4,-35,-1,-1,+1,0.
There is no other incorrect complete affected row literal in this hand
check. The row30 error is confined to its residual linear c coefficient;
its quadratic argument, output and constant are already correct.

## Consequences for ordinary claims

The corrected row30 expands by hand to

    y46-16c²+16cp+16cr-4p²-8pr-4r²-48c+24p+24r-35.

Its exact height is48, not35: the coefficient-48 is present, and every
other displayed magnitude is at most35. Its support still has11 terms,
so146/138 total residual occurrences and the8-term reduction do not
change. The maximum among all changed rows is still48, already attained
by rows16/26. Unchanged row12 still has-72ac, so the intended full
composition retains ordinary exact residual height72.

Changing a linear coefficient cannot change the degree4 part of a
residual square. Consequently all120 quartic witness cells, six whole
quartic witnesses, degree4/liveness argument and signed quartic budgets
are unaffected. For clarity, if B denotes the erroneous printed row and
R the correct row, R=B-24c and R²-B²=-48cB+576c², which has degree at
most3. This identity proves the quartic part is unchanged; it does NOT
identify the two complete SOS polynomials or their zero sets.

The whole lower-degree bounds for the intended F=P composed with V were
derived directly from complete OLD homogeneous slices: the69-term cubic
p slice,17-term quadratic p slice, old linear p coefficient-2116 and
constant2674. Their substitution p-b-c does not use the erroneous new
row30 linear table. The full cubic/quadratic identities and budgets
20762/15557, linear4386 and constant2674 therefore remain valid for
that intended composition, together with ordinary15109<=H<=24000.
This is an ordinary hand dependency audit, not a successful fresh checker
run or acceptance of the provisional exact produced H/support. The
erroneous printed residual system cannot inherit whole source calibration
from an equality to P composed with V that it does not satisfy.

Whole coordinate V, inverse order V,U,T,N,S, translations/private maps
and calibration contracts themselves do not change. However the original
ordinary proof package has a false full-row table and false row30 height,
and both static PASS reports failed to detect it. They cannot serve as
complete corrected-source approvals. Every repaired source/proof/table/
control/map obligation still needs its own fresh FULL review.

## Scope retained

This separate diagnosis preserves the complete first failure and openly
records the missed literal. It does not edit or approve R1, does not
review an unsealed replacement, and releases no repair or application.
ROOT's separately approved code-only bounded R1 preparation is a distinct
authority. Any eventual replacement needs its own exact seal, two FULL
final statics and separate ROOT release with fresh paths, followed by
fresh-run/evidence review and endpoint decisions. Original first source,
all first reports/captures, maintained page and paused Lean stay unchanged.
