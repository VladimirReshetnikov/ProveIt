# Free-J 95-operation model factor split

For the pinned 95-operation literal with twelve free variables, including
`J`, Lean proves that an internal zero in any `IΣ₁` arithmetic model makes
each of the three exact signed factors represent +1. The four integer ports
are arbitrary parameters. First and main factors use the expression-shaped
carrier exclusions; the polarized ordinary factor has its own modulo-four
exclusion because its correction is an explicit multiple of four.

The source checker binds all 95 operation rows, all twelve variable slots,
all four port slots and the exposed factors to the graph SHA-256
`2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22`,
and rejects four row/input/port/factor mutations. This separate Python check
is source validation, not a Lean theorem about the JSON file.

Fresh replay session 54657 exited 0 and printed
`PASS_BOUNDED_FREE_J_95_FACTOR_SPLIT
d7ac39974e9f6817709382dfe24ecb2425366096cfb2866fd0271305a5b7d1e3`.
The receipt preserves the seven Lean axiom reports, source/object hashes,
compiler direct dependencies, and inherited fresh historical overlay
receipts and post-use guards. Earlier exploratory session 83894 also exited 0
with the same seven reports. The initial source-check attempt exited 1 from
an incorrect relative path; it was corrected before the successful replay.
This single-author bounded replay does not replace a matched full-project
build or audit dynamic/package-transitive dependencies.

The [independent bounded replay audit](../../../reviews/ordinary12-freej-prototype-independent-audit/README.md)
passed for this free-J split, with the historical-provider qualifications
recorded there.

The 100-row theorem uses `J=6j+1`, while `J` is free here. A theorem for the
former does not cover every free-J valuation. This direct split makes no such
restriction. The ordinary free-J soundness proof instead describes an
exceptional-factor argument: recover rank while allowing `gcd(q,3)=3`, then
use the Mersenne coefficient to exclude the unwanted factor three. It does
not require a claim that all zeros have `J=1 mod 6`. That argument, ordinary
norm recovery, compact44 checker calibration, and both consistency directions
remain unproved here. In particular this model theorem is not an iPRA
derivation. The compact44 tuple's β is `2^590069−1`; the older 2011 endpoint
uses a different β and cannot be substituted.
