# Binary five-particle computational frontend

The construction in `proof.md` compiles any fixed finite ADD/SUB two-counter
program into a fixed binary conservative one-dimensional cellular automaton.
It uses exactly five occupied sites on every valid encoded computation, with
one anchored finite halt-word observation. The component rule is defined and
conservative on every binary finite-support input, including malformed inputs.
It is not reversible and no intrinsic-universality or efficiency claim is made.

The pinned universal two-counter instance has 8408 literal instructions. The
compiled alphabet is exactly {0,1}, the radius is 756787, and the halt word has
50452 cells. Its enormous 2^1513575-entry binary local table is specified by
the explicit rule algorithm, not written as a full bit string. All geometric
codes and counts are fixed by the delivered literal source. No new-record or
priority claim is made.

## Files

- `five_binary.py`: source-table validation, exact finite component update,
  Boolean local-rule evaluator, finite encoding, exact microclock, and ledger
- `proof.md`: full-shift conservation/locality proof, all-input simulation,
  primary-source scope, exact finite-horizon polynomial construction and costs
- `frontend.py`: emits an ordinary polynomial as explicit sparse squared
  residuals, with complete-witness reconstruction and actual cost accounting
- `example_frontend.json`, `example_witness.json`: a small accepted example
- `universal_h1_frontend.json`: all residuals of the literal source's one-step
  constant-input certificate, including exact physical clock; this is a fully
  emitted finite-horizon example, not a claimed accepted universal computation
- `source-replay/`: unmodified pinned literal source tables, their all-input
  simulation proof, and the previously validated independent source verifier
- `checks.json`, `frontend_checks.json`, `audit_*.json`: executable receipts

The frontend source horizon is fixed in the syntax, not a polynomial input.
The baseline witness domain is the natural numbers. Setting
`nonnegative_real=True` pays one selector-norm square per layer and gives the
same unique-witness result on the nonnegative real orthant, still requiring
natural external inputs. No claim is made over unrestricted real witnesses.

## Reproduction

Requires standard-library Python 3.10 or newer; no package installation or
network connection is needed. From this folder run:

    python check_five_binary.py
    python check_frontend.py
    python source-replay/verify_source.py
    python audit_independent.py
    python audit_literal_boundaries.py
    python audit_frontend_independent.py
    python audit_api_independent.py
    python -O audit_api_independent.py
    python audit_regression_modes.py

The finite tests supplement the all-input proof; they are not a substitute for
it or a machine-checked formalization. The source verifier covers every literal
instruction by affine loop-body paths, and uses separate decreasing-rank
arguments to justify their composition on unbounded input.

## Minimal use

    from five_binary import Machine, BinaryCA
    from frontend import Frontend
    machine = Machine({'go': ['ADD', 0, 'HALT']}, 'go', 'HALT')
    ca = BinaryCA(machine)
    initial = ca.encode('go', 0, 0)
    ticks = ca.duration('go', 0, 0)
    certificate = Frontend(ca, 1, initial_counters=(0, 0))
    witness = certificate.witness()
    assert certificate.evaluate(witness) == 0
    assert witness[-1] == ticks

Source tables are defensively copied into immutable snapshots; later edits to
the caller's original lists or dictionary cannot change the compiled rule.
Machine, CA and frontend lookup data are immutable after construction.
Source counters and horizons require exact nonnegative Python integers;
Boolean or floating-point values are rejected, including on halt paths.
Lattice coordinates may be negative exact integers, but Boolean/floating-point
coordinates and duplicate supplied iterable entries are rejected before set
conversion. Instruction rows must have exact supported lengths and destinations.

The exact numerical evaluator accepts natural integer witnesses in its baseline
mode, and nonnegative integer/Fraction samples in its paid real-orthant mode.
Floating-point values, NaN and infinities are rejected. The exported polynomial
still has the proved interpretation over all nonnegative real witnesses; the
exact sample evaluator is not an implementation of arbitrary real arithmetic.

For an explicit
radius-R local word, pass `ca.local` the set of occupied integer offsets in
[-R,R]; all other offsets within that interval are interpreted as exact zero.
The returned value is the central output bit. `ca.step` is the equivalent
sparse global evaluator for arbitrary finite configurations.

Primary references and the preserved Table-16/prose halt-symbol discrepancy
are documented in `proof.md`. Earlier delivered packages were not modified.
