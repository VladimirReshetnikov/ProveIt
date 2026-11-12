# A certified zero removes a computation opcode

Research prepared for Vladimir Reshetnikov, November 10, 2026.

## Result and scope

This package gives an admissible computation restriction and smaller complete
proof checkers for the inherited full first-order intuitionistic PRA
presentation. The new idea uses an initializer's nonempty syntax to select
computation, removing a separate arithmetic opcode.

The missing zero initializer is recovered with the independently proved equation

    C = I(2, 1; v.0) = 0.

Its direct successor computation has nonempty predecessor and initializer.
Replace a forbidden zero initializer, a zero successor predecessor, or both by
the same C and transport C=0 once. Every affected computation leaf becomes
exactly three native inference nodes. The native syntax, contexts, and end
sequents are unchanged. The complete report supplies all primitive logical and
nonlogical rules and the full-domain bi-interpretation with iPRA.

This is a proved checker simplification. It does **not** establish an absolute
simplest axiomatization or a major new arithmetic foundation. The proofs are
written mathematical proofs, not Lean/Rocq formalizations.

## Measured whole programs

| Complete program or comparison envelope | Tokens | AST nodes | Raw / normalized bytes | Gzip-9 bytes |
|---|---:|---:|---:|---:|
| Supplied coordinate minima, different files | 268 | 300 | 616 | — |
| Seven driver-only matched controls plus supplied sources | 264 | 300 | 601 | — |
| `code/checker.py` — recommended explicit list test | 264 | 308 | 566 | 351 |
| `code/checker_bytes.py` — zero-product list test | 264 | 310 | 558 | 345 |
| `code/checker_joint.py` — qualified generic traversal | 262 | 296 | 598 | 350 |

The joint profile is one program below every coordinate of both stated
envelopes. Its generic traversal has the inherited qualification that nonempty
strings can diverge with an ideal unlimited stack; actual CPython rejects them
through its recursion limit and subsequent type failure. The recommended and
byte profiles use explicit list recognition and avoid this qualification.
Canonical mathematical completeness assumes adequate resources, as with the
comparison programs.

All source is charged, including imports, input, scope checking, arithmetic,
logic, and acceptance output. Measurements use CPython 3.12.14, `ast.unparse`,
and zlib 1.3.2. Gzip is informational only:
`gzip.compress(source, compresslevel=9, mtime=0)`.

The source comparison is pinned to ProveIt commit
`fb2dbd2a33c6b132671a54b029d0bf3cd98c633d`: 13 ZIPs, 2,701 recursive Python
occurrences, and 370 distinct source hashes. All 31 sources at or below a
supplied boundary were classified; 28 are supporting utilities, not complete
checkers. All 370 frozen source byte strings are included for offline measurement.

The independent dispatch ablation restores only `m is None` in the final code.
It gives 574/566/606 bytes for the three corresponding programs, isolating an
eight-byte, two-token, three-AST-node gain from the new normalization itself.
The remaining overall reduction combines the inherited representation with
shared construction of the continuation assumption. The ablations are separate
from the seven driver-only controls.

## Read and run

- `ipra_certified_zero.pdf`: complete report, including attributed full arithmetic
  and logical bridge appendices.
- `ipra_certified_zero.tex`: standalone, independently compilable LaTeX source.
- `report_main.tex`, `theory/`, `reference/`: modular authoring sources and provenance.
- `code/FORMAT.md`: exact raw packet grammar and runtime qualifications.

From a fresh extraction:

```sh
python3 reproduce.py
python3 code/checker.py < examples/certified_zero.json
python3 code/checker.py < examples/literal_zero_seed_restored_by_three_node_normalization.json
python3 code/checker.py < examples/fresh_zero_instance_cannot_prove_false.json
```

The last example must reject with a nonzero process exit. Successful checking
means exit zero and the exact line `ACCEPT`; tracebacks are diagnostics.

The default reproduction command checks all payload hashes, remeasures the 370
frozen sources and seven exact driver-only transformations, regenerates the
named proof data, and replays the three selected checkers in ordinary and
optimized Python. It does not execute historical corpus code or modify package
files. The documented run passed **216 complete CLI expectations**: 36 cases
across three profiles and two Python modes, with 108 accepts, 108 rejects, and
zero mismatches.

To rebuild the PDF with a normally configured TeX Live installation:

```sh
python3 build.py
```

To intentionally refresh source measurements and the comparison table:

```sh
python3 measure.py --write
```

Rebuilding or editing may change file hashes. Verify the distributed manifest
before editing, or rebuild in a copy. The package's `build.py` writes the
standalone source, compiles in a temporary directory, and places the PDF beside
it. It does not require network access or shell escape.

## Additional findings

An eager iterator with `F(0,a;h)=h(a)` and
`F(Sn,a;h)=h(F(n,a;h))` admits a two-element model even with coverage,
zero–successor separation, and induction for all formulas. Consequently it
cannot interpret iPRA through any ordinary finite-dimensional definable domain
or quotient. The report gives the structural proof; a small independent script
exhaustively checks the finite model.

A second attempted simplification inserted projection boxes at all numerical
substitutions. A syntactic invariant excludes even a basic reflexivity equation.
That rejected experiment is documented as a completeness obstruction and is
not presented as a delivered iPRA checker.

## Contents and trust boundary

The three files in `code/` are complete standalone checkers. The producers,
source measurers, build scripts, example generators, and independent finite
model checks are supporting artifacts and are not imported by a checker.

`evidence/` records source counts, classifications, measurements, tests,
reviews, provenance, and the PDF build. `reference/` includes exact comparison
sources, driver-only controls, dispatch ablations, the source census, and the
attributed prior proofs. The MIT No Attribution license from ProveIt is retained.

The new initializer dispatch was not found in the inspected current corpus.
The broader technique of replacing a zero representation by a proved nonempty
one is inherited from predecessor/witness repairs and is credited. No
literature-wide novelty, absolute minimality, or external peer-review claim is
made. Finite tests do not substitute for the written universal proofs.
