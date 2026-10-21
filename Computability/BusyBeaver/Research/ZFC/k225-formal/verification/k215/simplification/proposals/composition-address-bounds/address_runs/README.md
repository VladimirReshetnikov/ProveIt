# Five-zero source layout and alphabetic capacities

This packet supplies an exact source transformation and ordinary mathematical
proofs toward shortening K215's return scanner. **It does not supply an accepted
214-state machine.**

The final source has 206 distinct subtrees, 4,751 primitives, maximum depth43,
and maximum consecutive-zero run5. Its ordered primitive word and both full
guarded CFGs equal those of accepted K215. Thirteen globally shared closed
rotations produce it; their shared-DAG certificate is3,720bytes. The least
possible maximum zero run within the entire closed-associativity class is5,
proved by a fixed five-left-edge source fragment. This is not a state lower
bound or a minimum-DAG theorem.

`report_section.tex` contains the complete ordinary capacity theorem, its
constructive proof, the source-class lower bound, exact metrics, and physical
allocation limitations. The capacity criterion applies standard preorder
Łukasiewicz/tree-slot encoding; that underlying encoding is not claimed new.

## Verify

Python3.10 or newer, standard library, assertions enabled:

```sh
python3 -B verify.py
python3 -B check_capacity.py
```

The first command checks every literal closed rotation, the primitive word and
two guarded-CFG resolvers at every stage, exact final source bytes, the small
invariant-spine certificate, and capacity results. The second compares the
linear prefix formula with independent exhaustive Catalan recursion on97,655
capacity vectors and performs25,190 tree-construction checks. These finite
checks accompany the ordinary mathematical proof, not a kernel formalization.

## Failed physical allocation experiments

With NumPy/SciPy installed, choose a fresh output directory:

```sh
python3 -B run_allocations.py --output /tmp/zero5-allocation-replay
```

This rebuilds a deliberately unaccepted scanner-deletion template from K215,
removing50 and setting34/0=0L75. It then reproduces two restricted failed
allocations: retained contextual roles give EMPTY_DOMAIN; releasing all pure
decoder roles gives NO_ALLOCATION (HiGHS model infeasible). The inherited
engine filter with state50 removed is a conditional synthesis assumption;
there is no new full runtime or blank-start proof for that template. The
reproducer does not accept or publish a214-state candidate.

## Files

- `baseline_sites215.json`: exact original source.
- `sites_zero5_206.json`: exact new source, SHA256
  `c7f8d2b7fca09d48afb560bfd42eacb22ca2e70ba6478bffa85b7b9fae3993c5`.
- `rotation_certificate.json`:362shared nodes and13global closed rotations.
- `source_capacity.py`: exact recursive capacity solver; reconstruction is a
  feasibility witness, not a DAG-size optimizer.
- `check_capacity.py`: independent exhaustive small-case corroboration.
- `evidence/`: actual verification, bounded search summaries, allocation results.
- `allocation/`: inherited bounded allocator and pinned inputs.
- `NOTICE.md`, `licenses/`: provenance and inherited terms.

The failed exploratory beam that exhausted memory and a stopped cubic DP are
not included. No result was inferred from either incomplete experiment.
