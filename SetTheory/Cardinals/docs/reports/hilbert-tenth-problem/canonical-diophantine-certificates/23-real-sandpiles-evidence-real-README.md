# Real-exact binary sandpile cubic: proof and verification packet

Status: independently reviewed mathematical strengthening; not published or
uploaded, and not a modification of delivered Report 35.

## Result in one line

Replace the old local term `f*g` with `f*(g+k+c)`. This makes the entire
nonnegative-real zero set equal the old full natural zero set, while retaining
the same variables, displayed nonnegative summands, cubic degree, collected
monomial support, and collected coefficient height.

The essential argument is finite predecessor descent of real burning ranks,
not a claim that Boolean selectors alone make continuous magnitudes integral.
The comparison gadget was already real-exact; extra edge penalties are not
needed. For precise hypotheses, all zero fibers may be empty, and the result is
only for binary odometers on each externally fixed finite prism.

## Files

- `PROOF.md`: exact theorem, full proof, edge cases, monomial invariance, ledger,
  and limits; primary merged presentation plus two optional comparison variants
- `real_certificate.py`: merged/default, unmerged/flat, and full-pair/sharp
  implementations using the verified local base compiler
- `exact_checks.py`: independent sparse-polynomial expansion, exact rational
  adversarial tests, finite exact real support-pattern branch enumeration
- `verification.json`: complete normal-mode test receipt
- `verification_optimized.json`: identical receipt with Python optimization
- `independent_math_review.md`: independent proof/implementation/count review
- `independent_coefficient_ledger_checks.py`: separate reproducible 54-case
  coefficient/ledger audit, with normal and optimized JSON receipts
- `approved_base/`: unchanged source/proof snapshots of the approved dependency
- `freeze_packet.py`: deterministic self-contained local review archive builder
- `MANIFEST.json` and `SHA256SUMS`: frozen payload identities
- `ENVIRONMENT.json`: version and verification summary
- `report35_integrity_check.txt`: all 78 frozen-release SHA256 checks still pass
- `PUBLIC_PRIOR_ART.md`: versioned targeted public-source comparison and explicit
  credit for existing strong-gate and real/Nat trace results

## Run

Python 3 and the installed SymPy are used; no upstream program or internet
connection is used by the verification commands. The approved base compiler is
included as an unchanged source snapshot under `approved_base/` and
authenticated against a fixed SHA256. Its files
are not changed; bytecode writes to the dependency are disabled.

    cd real-sandpile-certificate-20261003
    python exact_checks.py --output verification.json
    python -O exact_checks.py --output verification_optimized.json
    cmp verification.json verification_optimized.json

The recorded fixture contains 18 independent polynomial/ledger cases and nine
real branch-search instances. The branch search enumerates allowed positive
category supports and the five exact edge cases. It first eliminates equalities
with exact Gauss–Jordan arithmetic, then solves remaining rational inequalities;
every returned point is substituted back into all equations, inequalities, and
polynomial summands. Successful modified branches have no undetermined witness
coordinates even before inequalities. Returned feasible points are independently verified exactly. Reported infeasible
branches have no independently checked Farkas certificates, so their rejection
is solver-assisted regression/exploration rather than an independent real
infeasibility certificate. These tests are finite checks; the
all-prism, all-real conclusion is the mathematical theorem, not an extrapolation
from the tests.

During checker development, calling SymPy's direct `linprog` with equality
constraints produced a residual-invalid point on an infeasible branch. The
independent residual check rejected it. The final checker uses prior exact
equality elimination and retains full residual verification. No invalid point
was counted as a witness, and no theorem relies on that solver behavior.

## Exact overhead

The merged display adds exactly 2V to each of raw polynomial records,
coefficient-expansion multiplications, evaluation multiplications, and evaluation
additions under the original ledger. It adds no displayed summands. Only the
existing `fk` and `fc` collected coefficients change, from 2 to 3. The unchanged
`kc` coefficient is 86, including neighbor/halo contributions, so collected
coefficient height is exactly preserved.

## Attribution and scope

The compact cubic, support burning, and canonical parallel-rank theorem are
existing results in ProveIt manuscripts 16/19. Its neighboring quadratic-orthant
report already gives real one-hot gates and all-real-zeros-natural trace
certificates. This packet claims only the particular binary-sandpile merged
strengthening, its real-rank proof, and its exact support/height/count invariance.
It makes no global novelty, fixed-arity unbounded, finite-fold MRDP, universal
halting-cutoff, numerical-conditioning, or formal Lean-verification claim.

The local archive can be recreated with `python freeze_packet.py`. It excludes
bytecode caches, verifies both receipt pairs and the independently reviewed code
hashes, and performs no network action or upload.

`evaluate_orthant` is exact on integer/Fraction inputs. For floating-point or
other nonexact inputs it is only a calculation helper, not a zero verifier.
No tolerance-based acceptance or numerical conditioning claim is made.
