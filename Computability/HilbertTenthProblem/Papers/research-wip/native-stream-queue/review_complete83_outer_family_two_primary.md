# Independent review: eventual two-primary success of the outer family

**PASS within the stated scope; no remaining finding.** I read the complete final author proof and helper as inert text, challenged the all-size carry argument, and ran only the new reviewer helper. The theorem proves the two-primary part of the scale condition on an explicit infinite tail of the previously proved outer family. It establishes neither the odd-primary conditions nor a completed source zero or universal83 statement.

## Frozen artifacts and read scope

Author stem `/tmp/complete83_outer_family_two_primary`:

| File | SHA256 |
|---|---|
| `.md` | `fe9378a51f61d35147ec11dfed0aae8c0d0fc795d7e3afcec5cd22a01df9906b` |
| `.py` | `f595bb59d34f3ce0bb3a469ab7ea93feefe373ac5642ca0be5a78a1eb3b374d6` |
| `.json` | `0ec74608dfd8550c7478a39ff902351304e66ecc2d06f011f5cfdaab5e4d6e35` |

The receipt separately authenticates the unchanged83 source JSON and the even-radix, outer-family, and odd-prime notes, using their exact pinned installed bytes. The outer-family and even-radix proofs were read in the preceding review; the present review independently rederives the needed two-primary valuations. The odd-prime note is authenticated as a dependency, not independently certified here. Thirteen literal outer rows are checked against the83 source. This is not a new audit of the entire83 circuit or its degree.

## Mathematical challenge

The checked literal rows give

`R=(q²−z−qF)(q²−1)+(MC+q MF)J`.

I independently expanded this entire expression, including its constant `+z` and mask symbol, for both shapes. The resulting minus formula and the formula for `16R` in the plus case are precisely the final equations(10),(13). The author's retained correction remark accurately records the earlier omissions and the corrected residue of the extra factor in J. Each extra factor is1 modulo `B^(n−1)`; its nonconstant part is divisible by that modulus.

For the low window, this yields `R=z+MC(1+B+...+B^(n−2))` modulo `B^(n−1)`. The bounds `z+5<B` and `2<=MC<=B−2` ensure that adding z, z+1, or z+5 stops carrying by the second digit. The unchanged positions2 through n−2 and the strict bounds on `v2(R+1)` and `v2(R+5)` therefore hold, including the large-mask endpoint. Since `alpha=u>=2D+b`, the three noncentral cubic terms have valuations strictly greater than `p=popcount(r)`. Also `p<=8D+3<4alpha`; every remaining term has integral coefficient and index at least4, so it also lies strictly above p. This proves the exact valuation of the full half-binomial polynomial, rather than only a truncated congruence.

For the high window I checked both signed polynomial tails, their carries, and their termination. With `F>=4` and `Q>Astar`, the minus digits at4,6,7 have deficits `6F+4z+3−epsilon`, `8F−24`, `33`; the plus digits of16R at4,5,6 have deficits `6F+4z+3−epsilon`, `6F−3`, `2F−5`. All deficits are positive and below Astar. The intermediate minus digit is `12F−9`; the top digits are15 in the minus case and3,1 in the plus case. These checks exclude a hidden further borrow. The revised tail estimates retain the conservative epsilon intervals, including the newly restored constants.

The three complement blocks each have at least `D−ell` set bits. Their support is disjoint from all n−3 low MC blocks, also after the four-bit shift used for16R. Since R is odd, `popcount(r)=popcount(R)−1`; hence `p>=3D−3ell+n−4`. At `n>=3ell+5`, this is at least `3D+1`, and therefore at least `3v2(q)+1` in either shape. The same threshold makes `Q>Astar`, so there is no circular use of a block-size assumption. The auxiliary estimate `Astar<B³` correctly uses the inherited compiler bounds on K and d. The actual lower bound `K>B` is essential to the positivity of the deficits and is not silently extended to arbitrary small synthetic K.

## Fresh independent evidence

Reviewer stem `/tmp/review_complete83_outer_family_two_primary`:

| File | SHA256 |
|---|---|
| `.py` | `f698149188d1e30aa6c35da967c44b9e5269a5f119b8278a406cb052eab408c8` |
| `.json` | `a35f884198c4e104d2c4b896de0c5b86c37980e5a1e94a649bcabde0d4eac3eb` |

The fresh checker constructs rational sparse polynomials in Q,F,z,S directly from the literal outer expression and verifies both complete18-term identities. It reconstructs all64 saved cases with direct base-Q quotient/remainder extraction and adds24 relaxed synthetic cases with larger K. It checks whole low windows, every stated complement and intervening carry, disjoint bit contributions, the threshold, and the unique minimum using independent Kummer population calculations. Forty-eight of the88 cases lie above the threshold; the largest R has28,204 bits. These cases do not instantiate actual compiler tables or enforce the family's z/input congruence construction.

Writer, normal, and optimized-Python exact-receipt runs all passed from `/`. No author or predecessor helper was run or imported. No X of exponential size, full binomial value, Pell witness, compiled history, or full source zero was materialized. Finite checks corroborate the all-size proof; they do not supply its quantifiers. No repository file was changed.
