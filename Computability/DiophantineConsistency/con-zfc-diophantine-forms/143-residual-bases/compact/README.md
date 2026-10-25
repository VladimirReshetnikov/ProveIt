# Ten-positive denominator engineering

The four useful local operation/degree points are **77/626**, **78/464**,
**79/460**, and **80/384**, all with ten strictly positive integer unknowns
and the same whole indexed BFS943 fixed-coefficient tuple. The two additional
circuits are deliberately retained dominated controls, not frontier claims.

| Exact file | Carrier | Weight | Operations | Exact degree | Status |
|---|---|---|---:|---:|---|
| `xy_v2.json` | Y=q³s, D=XY | V² | 77 | 626 | tradeoff |
| `xy_bv.json` | Y=q³s, D=XY | bV | 78 | 464 | tradeoff |
| `q4_v2.json` | Y=q³s, D=q⁴ | V² | 78 | 622 | dominated control |
| `q4_bv.json` | Y=q³s, D=q⁴ | bV | 79 | 460 | tradeoff |
| `partial_v2.json` | Y=q²s, D=q³Y | V² | 79 | 518 | dominated control |
| `partial_bv.json` | Y=q²s, D=q³Y | bV | 80 | 384 | tradeoff |

The complete formulas and both unbounded proof directions are in `PROOF.md`;
the article-ready version is `report_section.tex`. The literal DAGs and full
coefficient payloads specify actual finite integer polynomials. The ports
are not additional variables. The largest port has 592,884 bits; expanded
polynomial coefficients may be much larger.

The incoming Certificate Reductions package already supplied staged
recovery with D=Y² (78/630 and79/468); Semantic Signs already supplied
unshifted transport. The new cubic choices improve those matched incoming
points, and the 80/384 partial chart dominates the incoming unshifted83/436
point. These are not global-minimum claims. Product-square extraction,
Pell doubling, and quotient normalization are credited inherited mechanisms.

## Reproduce offline

Python 3.10+ and its standard library suffice; no network or optional
packages are used. From this component directory:

    python3 -B build.py --check
    python3 -B verify.py --output /tmp/compact-check.json
    python3 -B -O verify.py --output /tmp/compact-check-optimized.json
    python3 -B rebuild_coefficients.py

`build.py` without `--check` deterministically regenerates the six DAGs
from frozen JSON data. It executes no inherited source program. The
independent verifier does not import the producer. It checks 28 symbolic
cut identities per endpoint, covering every actual row; exact complete
leading homogeneous forms; all register/input/port liveness; counts;
whole coefficient hashes and independent finite reconstruction; and eight
actual algebraic corruptions per endpoint. The two delivered receipts are
byte-identical across normal and optimized Python. Assertions are not used
for acceptance. These finite tests do not replace the universal proof.

## Provenance and boundary

`SOURCE_PINS.json` is the active local provenance inventory: every listed
`file` path resolves inside this component, and `verify.py` authenticates it.
`PROVENANCE.json` records immutable checkout/archive origins and local maps.
The frozen `provenance/SOURCE_PINS.json` and `parent_ledger.json` are
historical documents copied unchanged; their original relative paths
refer to their source packages and are not the active local inventory.
`provenance/prior_verifier.py` is a static historical source copy, never
imported or executed by this release. Its elementary sparse-ring routines
were adapted in the standalone checker, with the inherited notice retained.
The printed fixed-integer recipe is `provenance/indexed_constants.tex`.

The ordinary mathematical equivalence composes with the explicitly named
retained universal Pell and indexed native/refutation calibration. It is
formalizable in ZFC, but no fresh full Lean/Rocq or encoded object-ZFC proof
is claimed. This package does not prove Con(ZFC) or assert a zero exists.
No remote repository was modified. New research, code and exposition were
prepared with AI assistance; independent review means separately performed
review within this workflow, not outside human endorsement.

A tempting Y=qs,D=q⁶ branch was rejected because its first Pell modulus
only visibly contains q³, not the needed q⁴. No such endpoint is shipped.
