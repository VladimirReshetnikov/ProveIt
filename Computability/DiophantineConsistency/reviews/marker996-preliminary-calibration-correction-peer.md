# Correction to the preliminary marker996 calibration check

Reviewer: `/root/complemented47_review`.

**The marker996/clause995 proposal is rejected as a complete candidate.**
The ordinary-proof author found, and ROOT independently confirmed, a
coordinate-calibration error. This reviewer also missed it in preliminary
messages. No completed independent ordinary-proof or page acceptance
receipt for996 was issued. This document preserves the failed preliminary
review rather than rewriting it as a successful rejection from the outset.

## What was inspected and what failed

I read the complete marker996 NOTE and all278 lines of its finite probe,
SHA256 `dea15e895186d44c00af1946938dd399b4df52da449a2f9e83c9179a0d2d9499`.
Normal and optimized runs reproduced its receipt
`a525ef0167dd325fe6bdf7c5ceffc8a727161c61a42a94cdc1c616465d2dc65c`.
I sent preliminary messages accepting its proposed offset18 monotonicity
and Boolean canonical-marker interpretation under the NOTE's stated
Eastbit0 calibration. That interpretation was incorrect. Passing those
finite runs only reproduced the same incorrectly chosen tile coordinate;
it did not establish the required semantic calibration.

The probe used `(255-tile[2]) % 2` to identify the bit at physical978,
and checked the Start value using complemented East252. The actual
coefficient at978 divided by2048 is1. It therefore encodes complemented
West, the tile's coordinate0, not East. The Start tile is(2,435,3,1),
so complemented West is253 and its bit0 is1. The claimed disjointness
`Start+bit<=1` fails at the actual Start: the sum is2. Its parity is0,
so the marker test does not force the temporal one claimed in the
coarse phase analysis. The proposed canonical marker is also not a
Boolean digit at Start. The offset18 nondecreasing-cycle argument thus
cannot be applied to this physical encoding.

I independently checked the entire unchanged coefficient-array hash
`43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93`
and reconstructed its actual label calibration. The selector coefficient
is

```
c'_i = 2 + 2048*(1+w_i+2^8*n_i+2^17*p_i+2^25*s_i).
```

Consequently its physical control locations have this exact meaning:

| Physical locations | Coefficient divided by2048 | Decoded complemented coordinate |
| --- | --- | --- |
|942..950|2^(25+j), j=0..8|South s|
|960..968|2^(8+j), j=0..8|North n|
|969..976|2^(17+j), j=0..7|East p|
|978..985|2^j, j=0..7|West w|

Every entry of these four families was checked directly. Descriptive
`west`/`east` slot names in a specification dictionary are insufficient
for this mapping. My preliminary review should have made that direct
coefficient check before endorsing the new marker argument.

## Subsequent scope

The accepted2011 theorem/page and the frozen13-variable packets are
unchanged. Their completed reviews do not depend on this proposed996
marker interpretation. The historical996 sources and failed receipt
remain preserved. No claim is made here that996 has a full native
counterexample; the failure is of this claimed proof and canonical map.

A separate997-marker proposal uses physical979, whose actual coefficient
is2048*2 and hence complemented Westbit1. That bit is0 at Start253.
This repairs the specific local disjointness issue, but it is only a
new lead until its complete geometry, phase argument, canonical marker,
safe subsets, controller and whole proof receive separate review.
No acceptance of that successor is implied by this correction.
