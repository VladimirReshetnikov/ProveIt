# Independent review of the positive CRT duration interface

**PASS; no author correction requested.** This review covers the complete frozen author source and companion proof, the exact new fixed-numeral recipe, the unchanged 133-operation local graph, and both saved positive-duration arrays. It supports the claimed **140h+7 operations, 31h+1 positive witnesses, degree at most 10** for each fixed duration h. It does not certify an unbounded fixed-arity history compiler or a new universal-polynomial bound.

## Frozen inputs and read scope

The reviewed author files are:

| File | SHA256 |
|---|---|
| `matrix193_positive_crt_duration.py` | `383f25df2c8e4f796d9c203d4ff543af3d94e70e19ba83052472d498e5c21abc` |
| `matrix193_positive_crt_duration.json` | `98e369e35d3e094f715f80e2bf12c9d277fed17cf3c3ed28f47044d758c3ef77` |
| `matrix193_positive_crt_duration.md` | `f2d9113f9c6aae1cffe2e84a38d9e9e63740bb0d5bb6359dd66bdb8ac81bc27c` |

I read the complete Python and final Markdown. I authenticated all five pinned dependencies:

| Dependency | SHA256 |
|---|---|
| `matrix193_centered_crt_selector.py` | `091ea1a9fae724f7dd9cab551e6938b0524677766b39f0311d9e324f8837cd28` |
| `matrix193_centered_crt_selector.json` | `51e304b13fbeea6d1b69a35ee8fbd3f359dfe050e2ceee177890b8b3d07d1d78` |
| `matrix193_centered_crt_selector.md` | `5360a8ecd24ab88eb0e7867ca98179eebfcded3a11fd427fb3923ba535106046` |
| `matrix193_gamma1_recode.md` | `6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742` |
| `matrix193_context_absorption.md` | `d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b` |

The inherited 96 paired matrices, fixed-context group interpretation, and countdown language reduction retain the scope of those dependencies and the earlier independent centered-CRT review. Here I independently re-enumerated the circle labels, retained matrix determinants and pivots, and reconstructed the new arithmetic. No predecessor Python was imported or executed. No repository file was changed.

## Positivity proof and uniformity

For each distinct nonzero absolute doubled entry A, the assigned prime p is 3 modulo 4, differs from 3, and does not divide 2A. The congruence T=A+p modulo p² makes T²−A² have p-adic valuation exactly one. A sum of two integer squares cannot have this valuation: divisibility by such a prime forces divisibility of both roots and hence of their squared sum by p². Because T is odd, A is even, and T>|A|, the same gap is positive and equals 1 or 5 modulo 8. The three-square theorem supplies three integer roots; the two-square exclusion forces all three to be nonzero. Absolute values therefore give strictly positive roots. For A=0 the displayed triple (2T/3,2T/3,T/3) is positive and exact.

I independently checked the stated three-square criterion in the [Archive of Formal Proofs entry by Danilkin and Chevalier](https://isa-afp.org/entries/Three_Squares.html). The criterion rules out precisely the natural numbers of the form 4^a(8k+7). This citation supplies the classical existence theorem; it is not a claim that the present circuit has been formally verified.

The finite prime assignment is effective for every fixed finite table. Infinitely many primes congruent to 3 modulo 4 follow by the elementary product argument; avoiding previously used primes and divisors of 2A excludes only finitely many. Pairwise coprimality of 6 and the distinct p² makes the radius CRT valid. All new constants are chosen from the fixed table, independently of external input x and duration h.

At a circle node the intended remainder r=T+2entry satisfies 0<r<2T<m. For the least nonnegative CRT value C, writing C=r+km gives k≥0. Adding the full modulus product M to the center changes the required quotient to k+M/m>0. Conversely, the sphere bound places the recovered coefficient plus T in [0,2T], so its congruence identifies the unique intended doubled entry. The circle RHS is nonsquare, allowing its root to be chosen strictly positive. Thus all 25 designated auxiliary ports can be positive without changing the integer state relation. On LOAD they are unconstrained by the vanishing product and may be chosen arbitrarily positive.

The note correctly distinguishes this state projection from a bijection of full auxiliary fibers. Recompiling T and L changes the numerical frame. Its all-value center-shift identity is relative to the new unshifted frame, not the old parent's numerical constants. A node-dependent quotient translation is not claimed away from the selector circle.

## Independent exact reconstruction

A fresh scratch checker at `/tmp/aristotle_matrix193_positive_crt_checks.py` used only inert JSON and its own arithmetic/polynomial routines. It produced `/tmp/aristotle_matrix193_positive_crt_checks.json`. No author helper or predecessor was imported. Its exact checks passed:

- A separate sieve reproduced all 504 assigned primes. A product-and-inverse CRT, distinct from the author's sequential radius construction, reproduced the exact 11,394-bit T and 11,399-bit period. Every positive gap has the required residue modulo 8 and valuation exactly one; the last assigned prime is 7,963.
- A complete integer circle scan reproduced all 96 labels and positive roots. Independent factor extraction reproduced the 148-prime difference radical. All 4,560 modulus pairs are coprime.
- Sequential CRT per coefficient column, distinct from the author's product formula, reproduced every complete effective numeral, all 576 coefficient residues, and all 576 strictly positive node quotients. The product has 1,094,898 bits; the largest bound source numeral has 1,094,899 bits.
- All 192 matrix determinant/nonzero-pivot conditions hold. The new local array and variable interface equal the parent's complete 133-row array literally.
- Independent sparse expansion of the complete local source equals a separately written sum-of-squares/product formula: 8,466 terms. The same check after formal center shifts gives the complete 14,040-term polynomial and both saved polynomial hashes. The degree line has the nonzero leading coefficient L^4 at t^10.
- Independent emission reproduced every row of both positive-duration arrays, every supplied-port role, the initializer, endpoint and final additions. Closure and reverse liveness include all rows, variable ports and fixed bindings. Twelve additional whole-duration modular comparisons against an independent state recurrence passed; these corroborate the exact source reconstruction.

| Duration | M | A | Total | Positive witnesses | Degree claim |
|---|---:|---:|---:|---:|---|
| 1 | 67 | 80 | 147 | 32 | at most 10 |
| 2 | 131 | 156 | 287 | 63 | at most 10 |

The generic count follows directly from 133h local gates, 6h signed-coordinate reconstructions, seven endpoint gates and h final additions. There are 25h direct positive auxiliaries, 6h positive encodings of signed coordinates, and one shared positive offset. Every finite signed trajectory admits such an offset. Each local polynomial and the endpoint are nonnegative over the reals, so summing without another squaring gives the required conjunction over positive integers. The countdown proof still forces LOAD^x followed by tiles; positivity changes no state or counter condition.

## Limits and replay evidence

The actual new-T sphere triples are not materialized. Their existence and strict positivity follow from the proof above; small component triples and modular evaluations are not presented as accepting histories. The author accurately separates exact grammar/constant identities from bounded numeric diagnostics. The final rational counterexample also remains valid: setting the recovered coefficients to zero, using the explicit positive three-square triple, and allowing rational positive quotients sends nonzero current rows to zero rows. An invertible tile cannot do so. Therefore the integer-domain qualification is essential.

The author reports fresh normal and optimized exact receipt replays; root separately corroborated all 504 radius conditions, all 576 quotients and 48 whole-history modular comparisons. These are attributed checks, not my execution claims. At root's request I did not repeat an identical author replay: my fresh independent reconstruction completed against the final source and receipt hashes above. Source inspection confirms explicit exception checks, duplicate-key/noninteger-JSON rejection, recursive exact-type receipt comparison, and exclusive output creation.

The result is a uniform fixed-context, fixed-duration positive-integer compiler recipe with a larger coefficient-height cost. It leaves local cost 133 unchanged and pays no unbounded history encoding. No issue found within that scope.
