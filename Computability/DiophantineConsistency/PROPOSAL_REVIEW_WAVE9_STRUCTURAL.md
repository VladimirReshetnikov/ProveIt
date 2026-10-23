# Wave-nine source, sign and structural review

Reviewed the full arrival archives at `0c6be9a074`, placed by
`a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49`, for packages 61–64.
All four full normal release replays pass under Python 3.12.13. The
receipt is [data/wave9-review-structural.json](data/wave9-review-structural.json).
The full ZIP trees, including manifest members omitted during placement,
were used without repairing delivered content.

## Principal results

| Package | Domain / variables | Operations | Exact degree | Disposition |
|---|---|---:|---:|---|
| 61 congruence carriers | 13 positive | 93 | 34 | New lower-degree tradeoff |
| 61 congruence carriers | 12 positive | 104 | 118 | New lower-degree tradeoff |
| 61 SOS companion | 12 positive | 103 | 172 | Separate cost/degree tradeoff |
| 62 sign and norm | 13 positive | 83 | 114 | Improves the old 83/132 point |
| 62 global shared powers | 9 positive | 453 | 1,834,516 | Dominated by 66's 449/same degree |
| 63 sign recovery | 14 positive | 87 | 34 | Dominated by 64's 83/30 |
| 63 higher majorant | 9 positive | 504 | 1,573,266 | Dominated by 66's refined point |
| 64 adaptive modulus | 14 positive | 83 | 30 | Useful lower-variable/degree tradeoff |
| 64 smaller finite code | 9 positive | 470 | 1,781,068 | Dominated in the wave-nine catalogue |

The integer branches are distinct: package 61 gives 37 unrestricted
integers in degree 6 and 34 in degree 8; package 62 gives 42/4, 35/6 and
30/8; package 63 gives 42/4; package 64 gives 41/4, 36/6 and 31/8.
Operation counts were not optimized for those expanded residual systems.
They must not be compared as nine-integer equations. Whole native tuples
are bound separately to their positive and unrestricted-integer families.

## Mathematical and source boundaries

Package 61 combines two congruence carriers with a divided auxiliary norm.
The second carrier first recovers the actual Pell index modulo its q-fourth
part, and only then uses the extra q factor to recover the scale on X.
The resulting index order is essential: recovering the scale by assuming
the final index would be circular. Its divided auxiliary norm and modulo-four
unit argument are new unbounded arithmetic obligations, although their
finite identities and exact degrees replay successfully. The signed
minus-form auxiliary index argument is closely related to the separately
checked `NativePellStepDown`; the literal native/tableau calibration remains
separate.

Package 62's thirteen-positive form centers a root before its norm, removing
high-degree terms while preserving the integer-root argument. The integer
branch recovers a common sign only after Pell-rank recovery, with a stronger
cofinal square scale. Its quotient eliminations require that order of sign
recovery; finite residual identities alone do not establish it.

For its nine-variable branch, the source file SHA256 is
`9a32f3f4fdafcc75131691ee248a4dac7dcd26b14d3d539e8f13d6093087eb6b`.
An independent row comparison finds 21 expanded rows identical to the
authoritative package-59 old-z source; row 15 subtracts `beta*J`. Thus it
uses the shifted positive quotient, as in package 52. The substitution is
`z_old=z_shifted+1`; inverse positivity requires the genuine source/canonical
witness bound, not just a renamed JSON field. Its 453-operation global
circuit is the final point; the retained 467-operation ledger describes an
intermediate Horner evaluator. Both were distinguished in this review.

Package 63's nine-variable parent is byte identical to the current old-z
source, SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
Its improvement instead uses a higher root majorant and a 264-term exact
positive-coefficient defect expansion. Formalizing it needs the actual
uniform inequalities and strictness, not merely the sampled checks. Its
integer and fourteen-positive forms additionally use new sign recovery
and quotient absorption arguments.

Package 64's nine-variable parent has the same byte-identical old-z SHA.
The weights shrink to maximum 111 and the convolution height to 2010.
This is a new finite geometry and exact population calibration; the
already checked split116 numeric exponents cannot simply be copied. Its
fourteen-positive branch uses the adaptive modulus `Y^2`, with the gcd
bound preceding index recovery and restoration of the deleted quotient.
The integer branch delays sign recovery until the main Pell equation has
identified the scale. These are ordinary mathematical proofs with named
inherited interfaces, not new Lean endpoints.

## Replay and formal reuse

Package 61's normal driver itself exercises the new algebra/dossier
checkers normally and under optimization, while retaining normal mode for
historical coefficient tools. Package 62's entire flag-propagating root
replays normally and with `-O`. Package 63's root replays its new quartic
and fourteen-positive checks in both modes; the nine verifier and independent
majorant checker also pass separate `-O` runs. Package 64's full declared
`--optimized` replay passes after its normal replay. All normal runs include
the actual coefficient rebuilds and independent retained decoders.

The independent catalogue reader additionally checks the literal DAGs'
topology, liveness, binary counts and hashes. Reported exact degrees are
supported by the full release certificates, not inferred from naive DAG
degree propagation.

The current Lean-bound source, sparse borrow/carry machinery, free-carrier
tail, signed auxiliary index recovery, and literal nine-variable polynomial
are reusable foundations. No package here closes the authentic native
compiler/tableau theorem or the internal object-language ZFC equivalence.
Direct proof-certificate and non-Jones encodings remain open research
routes; these inherited constructions do not constrain the final choice.
