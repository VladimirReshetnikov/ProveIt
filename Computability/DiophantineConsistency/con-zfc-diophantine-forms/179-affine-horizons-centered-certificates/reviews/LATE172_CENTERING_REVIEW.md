# Independent review: source172 polynomial-centering composition

**Accepted**, for ten strictly positive integer unknowns, at the bounded source snapshot `09764940c289c493aa573530eda86dd75f319787`. The new points are **89 integer-leaf operations / exact degree 210** and **90 / 206**. Incoming source172's **87 / 214** is a different operation/degree tradeoff. Earlier round22 **87 / 228** and **88 / 224** are dominated controls, not current frontier claims. No global minimality is asserted.

Reviewed ordinary proof: `round22/positive/late172/PROOF.md`, SHA-256 `a0b02fe85e3ab3bde1b68894066ba93e9363b4e98c83084c9af6db19f9ea041a`.
The exact reviewed graph hashes and all coefficient ports are bound in `LATE172_CENTERING_INDEPENDENT.json`.

## Mathematical review

1. **Correct source interface.** Source172 is the free chart `Y=s`, `lambda=q`, not the previous scaled chart. Root extraction uses only the norm equation and remains valid after changing its numerator. Main index `p>=3` suffices for `c>=4 Delta+3>4q^4`; neither `q|Y` nor exclusion of either index-three branch is assumed prematurely.
2. **The strengthened signed bound is justified.** Source172's actual preceding inequality is `|b|>4 Delta f-1`, with `f>6g`, `Delta>=3` and integral `g>=1`. It implies `|b|>72g-1>8g`, stronger than the displayed old consequence `|b|>4g`. This strengthening does not change the inherited all-index theorem or exclude an auxiliary branch.
3. **Both chosen centers fit the margin.** The 90-operation center is `A U E`, with exact remainder `U^2 E^2-E`. The 89-operation center is **`(A+1) U E`**, not `(A-1) U E`, with exact remainder `2(A+1)U^2E^2-E`. Both are positive and less than `2g`. Thus `gy+ghat|V|<7L/16<L/2`. Together with `rho<|b|/q^7`, `|V|>1`, and `q>=32`, the negative-`B` carrier would make independent positive `n` negative. This recovers `B>=0,C>0` before using the mask rank bound.
4. **Authentication order is retained.** The center changes the numerator by `-M ghat V`, divisible by both literal clearing factor `D` and projector `H`. One first obtains `q^4|e*`, including the prime 3, authenticates the first index, and projects to `X=2^R` while retaining the entire factor `6h`. Only then does the proof obtain the full `q^7|e*`, and recover `q^3|Y` and `h|B`. Integrality of the center adds no denominator. No unjustified factor cancellation was introduced.
5. **Completeness is constructive and positive.** On a parent positive zero with `V>0`, retain all other inputs and set `n_new=n_old+ghat V`. This is strictly positive, and the numerator is literally unchanged. Soundness was separately proved, so no inverse shift is assumed to preserve positivity.
6. **Actual current tuple is separately calibrated.** The frozen4177 specialization retains its complete native proof, decoder, physical zero-weight marker1048, once-shifted source mask, and specific Pcs certificate. The free-chart endpoint supplies the actual original-source witnesses at `Y(X+1)+2`; this is not an inference from scalar boxes alone. Completeness obtains fresh outer data from the same whole tuple and applies the parent lambda-uniform construction. No individual coefficient port or old controller certificate is substituted.

## Independent finite checks

`check_late172_centering.py` is independent of the producer and uses our own bounded Git-object comparison code. Normal and `python -O` runs both pass and have byte-identical receipts.

- Full graph delta against the actual source172 JSON; exact variable/domain lists; unique binary nodes, backward references, all nodes and all fourteen leaves live.
- Exact square-remainder and centered-norm polynomial identities.
- Complete 99-term highest homogeneous forms, not numerical rays or degree metadata: `9*2^10 q0^82 w^24 s^56 i^10 k0^32(q0-F)^2` at degree206, and `9*2^11 q0^84 w^25 s^57 i^10 k0^32(q0-F)^2` at degree210. The actual positive beta makes both nonzero.
- Every compressed/raw coefficient hash, endianness, bit length and total raw byte count at both coherent calibrations: historical radix67, 295388 bytes; frozen4177, 98219 bytes.
- All 88 retained source files, all 67 original source172 dependency pins, and all 59 deduplicated dependencies checked against the actual immutable Git objects and authenticated placement map.
- Relocated4177 proof and certificate paths resolve locally and match their original hashes.

The finite checks do not prove the unbounded Pell/index or syntactic calibration theorems. This is an ordinary proof composition at the retained source boundary, not a new full proof-assistant or internal-ZFC replay. The documented upstream gzip-header portability failure is not silently relabeled a successful original byte-for-byte build.

## Late comparison and stopping boundary

`LATE_SNAPSHOT.md/JSON` retain the comparison through commit09764940, including source174. The new current display at that commit is the **different whole4027 tuple, 94689 raw bytes**, while source174 separately has4127 at97046 bytes. Neither replaces the deliberately frozen4177 specialization. The incoming213-variable quartic has a major height cost and does not fully dominate the reviewed215-variable quartic profiles. No new natural202/200 or roots14 challenger was found among the bounded changes.

No subsequent fetch, upstream edit or later-source comparison was performed.
