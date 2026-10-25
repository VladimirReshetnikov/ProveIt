# Quartics with every nonzero coefficient equal to +1 or -1

All four polynomials are explicit, parameter-free polynomials over unrestricted
integers. Every declared variable occurs, the total degree is exactly four,
and the constant term is one. Their complete collected coefficient lists are
`equations/NAME/polynomial.json`; readable expansions are `polynomial.txt`.

| Name | Variables | Monomials | Source |
| --- | ---: | ---: | --- |
| unit951 | 951 | 56,916 | Pinned signed324 |
| unit984 | 984 | 30,076 | Pinned signed324 |
| unit1050 | 1,050 | 21,766 | Pinned signed324 |
| matched1137 | 1,137 | 23,105 | Pinned signed442 |

`unit984` is the balanced choice. `unit951` minimizes the variable count
within this delivered set; `unit1050` has the sparsest support. The matched
1137 result isolates the compiler gain on the same source that package127
converted to 2215 variables and 30468 terms.

The new compiler pairs opposite occurrences, identifies aliases only when
the complete graph-energy coefficient map permits it, and replaces eligible
two-alias dummy cycles by `(a-b)^2*(a^2+a*b+b^2)`. Each transformation has an
ordinary proof in the main report. There is an exact bijection of integer
zero sets with the indicated source. The consistency calibration is inherited
from that source; it is not a consequence of testing coefficient lists.

From this directory, with Python 3.12 (the tested runtime) and no extra packages:

    python3 -B verify.py --rebuild --output verification.json
    python3 -B -O verify.py --output verification_optimized.json

The checker imports neither the producer nor its optimizer. It checks the
triangular normalization, every logical block balance, the internal trees,
the complete alias partition, every collected polynomial coefficient, and
the symbolic canonical lift. Deliberate corruptions must be rejected.
`--rebuild` additionally repeats the fixed construction in `profiles.json`
and compares the three mathematical JSON artifacts byte for byte. The
randomized ordering used in two selected profiles has a fixed recorded seed;
no random evaluation is used to certify coefficient height or equivalence.

`source127/graph/build.py` is an unchanged inherited normalization/layout
implementation; only its normalization and factor-orientation helpers are
used by the new paired builder. `SOURCE_PINS.json` gives the exact Git blob
and SHA-256 identities of all inherited sources. The main report distinguishes
the unconditional graph theorem from the inherited logical calibration.

No global optimum or external human review is asserted. The independent
review was a separately tasked AI-assisted mathematical and code review.
