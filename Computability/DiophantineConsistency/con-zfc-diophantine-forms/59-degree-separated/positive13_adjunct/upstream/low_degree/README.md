# Separate quadratic norms for direct positive consistency equations

All four files define ordinary integer-coefficient polynomials whose absence of
solutions in the stated strictly positive domain is provably equivalent in ZFC
to Con(ZFC), by the mathematical proof in PROOF.md and the pinned inherited
compiler/calibration arguments. They do not assert a proof of consistency or
global minimality.

| Artifact | Positive unknowns | Exact degree | Binary operations |
|---|---:|---:|---:|
| `twelve_positive_degree242.json` | 12 | 242 | 94 |
| `twelve_positive_degree258.json` | 12 | 258 | 89 |
| `twelve_positive_degree314.json` | 12 | 314 | 91 |
| `thirteen_positive_degree132.json` | 13 | 132 | 83 |

The 242 and 258 variants are the recommended twelve-positive tradeoffs. The
314 variant is a dominated but transparent intermediate. Relative to the
incoming wave-7 twelve-positive 897/108 form, both recommended variants
improve degree and operation count.

Run `python3 low_degree/verify.py` from the release root, or execute the script
by absolute path. It uses only the standard library. It reads the entire
compact coefficient tuple from `../coefficients/coefficients/*.gz`, checks
copied upstream proof hashes, verifies gate order/liveness and exact finite-
field polynomial degrees against universal leading-form formulas, multiplies
formal radical factors, and tests the quotient/congruence transcription.
No upstream executable or network access is used. Assertions must remain
enabled; -O/-OO is rejected. The resulting CHECKS.json is a finite diagnostic,
not a consistency proof or a replacement for the universal arguments.

Builders write only their own inert JSON DAGs. `build_twelve_balanced.py`
constructs degree 242, `build_twelve_reduced.py` degree 258, `build_twelve.py`
degree 314, and `build_thirteen.py` degree 132. The proof explains the two
existential coordinate changes, which preserve existence rather than each
individual auxiliary assignment. All constants are fixed leaves; named
registers do not add quantified variables.
