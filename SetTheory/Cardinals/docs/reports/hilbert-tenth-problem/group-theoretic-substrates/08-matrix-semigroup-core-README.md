# Fixed numerical universal matrix semigroup

This research packet gives **229 literal generators in SL4(Z)** and a fully
implemented finite-U15-tape-to-target matrix reduction. Membership in the
fixed nonempty-product semigroup is many-one r.e.-complete, using the cited
effective finite-tape universality construction of Neary and Woods.

Read `PROOF.md` for the complete local argument and the precise imported
universality dependency. The program/input-to-U15-tape compiler from that
publication is **not claimed to have been reimplemented** in this packet.
No inverse generators, Higman embedding, ordinary-affine arithmetic bridge,
Diophantine operation count, optimality claim, or novelty claim is included.

## Files

* `compiler.py`: new standard-library compiler and exact target encoder
* `data/u15_table.json`: pinned 30-cell source data (29 defined transitions)
* `data/semigroup.json`: full literal alphabet, 93 rules, 114 tiles, 229
  integer matrices, symbol codes, provenance hash and exact resource ledger
* `data/matrices.txt`: the same 229 matrices as a plain integer list
* `data/ledger.json`: machine/rule/tile/matrix and bit-size counts
* `PROOF.md`: all construction, soundness and completeness proofs
* `PROVENANCE.json`: source locations, hashes, execution and scope boundaries
* `tests/check_all.py`: authored tests with an independent tape oracle
* `evidence/accepting-witness.json`: a complete 189-generator target witness
* `evidence/tests.json`, `evidence/tests-optimized.json`: normal/-O receipts
* `audit/`: independent JSON-only numerical/proof review and its own checks
* `loader-audit/U15_DEPENDENCY_AUDIT.md`: precise published input dependency

## Reproduce

Python 3.10 or later, standard library only, from this directory:

    python compiler.py build
    python tests/check_all.py
    python -O tests/check_all.py
    python compiler.py target --left 011 --right ''
    python audit/independent_check.py
    # For the integrated release identity gate and isolated replay, use ../verify_release.py

The first command regenerates the numerical packet, ledger and literal list.
The target command computes an exact matrix; it does not simulate the machine
or decide semigroup membership. Both tape halves are nearest-head-first,
state A initially scans zero, and both unlisted tails are blank zero.

The API is `compiler.from_tape(left, right)`. It returns exact Python integers
and the finite configuration word. The CLI emits literal decimal integers
and disables Python's optional decimal-output digit limit for valid long
inputs. Mathematical totality is subject in execution to ordinary resource
limits. Inputs must be strings containing only 0 and 1.

For example, left=101, right=01 encodes `[101A001]` and returns

    [[1881938649, 53001020, 0, 0],
     [-80139620240, -2256971351, 0, 0],
     [0, 0, 1, 2],
     [0, 0, 0, 1]].

The positive witness uses left=011, right=empty. Its actual U15 run reaches
the undefined J1 cell, and the saved witness continues through cleanup to X.
The literal 189-matrix product is checked with independent exact arithmetic.

## Counts and caution

There are 20 rewrite-alphabet letters, 93 directed rules, 114 inner tiles,
and 229 distinct generators. The largest absolute generator entry is
63,038,000 (26 magnitude bits). A tape input of total length n takes n+5
fixed-matrix multiplications and has a conservative 12(n+5)+1 magnitude-bit
bound on every target entry.

The all-input theorem is proved in `PROOF.md`; the finite tests are not a
nonhalting decision procedure. No upstream repository code was executed,
and earlier releases were not changed. New code only reads the pinned small
transition-table data. A separate independent audit reads the emitted JSON
without importing the compiler.

The distribution includes authored work and the small factual transition
table, but excludes third-party primary-PDF reading caches. Source links,
published bibliography, draft-specific printed-page locators and inspected
PDF hashes remain in `PROOF.md` and `PROVENANCE.json`.
