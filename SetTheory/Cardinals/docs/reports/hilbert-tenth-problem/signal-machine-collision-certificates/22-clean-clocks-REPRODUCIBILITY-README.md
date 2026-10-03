# Complete unbounded compact-clean-clock arithmetic artifacts

**Mathematical result:** for four specified fresh-entry, terminal-halt reversible sources, the emitted fixed-arity Diophantine polynomials represent the first exact cleaned three-mass target time with natural input/time coordinates and strictly positive integer witnesses. No external source-step horizon is supplied.

Start with [THEOREM.md](THEOREM.md). The two independent assessments are [the proof audit](audit/PROOF-AUDIT.md) and [the complete emitted-circuit audit](audit/EMITTED-CIRCUIT-AUDIT.md).

| Fixture | Native/spatial operations | M + A | Positive witnesses | Exact degree | Phase4 operations |
|---|---:|---|---:|---:|---:|
| INC2;DEC2 | 604 | 239 + 365 | 60 | 2344 | 605 |
| ZERO3 | 479 | 184 + 295 | 58 | 1192 | 480 |
| NOP | 477 | 182 + 295 | 58 | 1192 | 478 |
| POSITIVE3 | 480 | 189 + 291 | 58 | 1192 | 481 |

Every complete nonempty circuit has natural ports `x,Tclean`, twenty comparison squares, a complete 59-gate finalizer, and a paid positive existential native time. The output-copy equality `F=y` is safely projected away; positive terminal F and all nineteen other raw constraints remain. The complete cleanup equation is `Tclean=2*theta+192*(F+x+1)+16`. Spatial blocking preserves time; the phase4 variants pay one extra multiplication by 4.

Initially halted sources use separate four-gate polynomials `(384*x+400−Tclean)^2` and `(1536*x+1600−Tclean)^2`, with zero witnesses. They are not forced into the nonempty positive-time packet.

## Files

- `circuits/*-native.json`: four full native/spatial DAGs, coordinate domains, complete comparison lists, exact ledgers and per-gate exact-degree certificates
- `circuits/*-phase4.json`: four independently checked full phase-dilated DAGs
- Matching `.dag.txt` files: complete human-readable arithmetic instructions, not executable programs
- `circuits/zero-step-*.json`: separate initially halted affine SOS circuits
- `emit_clean_clocks.py`: standard-library, data-only deterministic emitter; it authenticates the pinned raw JSON before composing it
- `check_semantics.py`: separately implemented source interpreter, clean-wrapper tests, actual packed AND/no-wrap checks, false-halt and clock/endpoint mutations
- `receipts/emission.json`, `receipts/semantics.json`: exact deterministic receipts
- `audit/check_emitted_circuits.py`: independently written literal/degree/count/SOS auditor with deliberate-corruption tests
- `audit/check_degree_certificate.py`: a second independent homogeneous-component degree checker
- `source/`: exact pinned upstream material and unchanged inherited cleanup proof; upstream Python is provenance only and is never executed by these commands

## Reproduce without third-party executable dependencies

From this directory, using standard Python3:

```sh
python emit_clean_clocks.py --check
python check_semantics.py --check
python audit/check_emitted_circuits.py --expect audit/independent_emitted_circuit_audit.json
python audit/check_degree_certificate.py
python verify_manifest.py
```

The first three commands and manifest verification are read-only replays. The degree checker rewrites only its deterministic degree receipt. No repository checkout, network, package installation, compiler, or author verifier is required. The degree certificate substitutes every variable in emitted `parameters+auxiliaries` order by `(i+2)*z`, keeps formal degree bounds even when a top component cancels, and finds nonzero coefficients at the claimed full degree modulo 1,000,003. This certifies exact degree without full multivariate expansion.

## What these artifacts establish and do not establish

Both directions of the new composition are elementary, conditional on the documented inherited raw/native and cleaned CA theorems. Complete DAG semantics/counts/degrees are independently checked. Concrete outer histories satisfy every outer equality and the full packed AND; signed/modular full-DAG evaluations verify all literal arithmetic including native rows. Huge positive native/Pell zero tuples are not numerically materialized. Native and phase4 versions are separate test cases, not distinct source programs.

Every accepted input/time pair has infinitely many positive witnesses in these emitted nonempty circuits: all sufficiently large dyadic heights admit fresh native extensions and different retained height slacks. Deterministic source history does not imply unique arithmetic witnesses. This is not a finite-fold construction. The separate zero-step circuits have no witnesses.

The fixtures are nonuniversal and themselves have only one or two accepted source steps. Their complete generic encodings have no horizon parameter, but these examples are not evidence of a long universal execution or a new universal operation bound. Hiding output/time leaves a raw halting language depending only on `nu_2(x+1),nu_3(x+1)`. An arbitrary c.e. ordinary-input loader remains unconstructed. There is no optimality, rational-zero exactness, fixed universal target, stationary-halt, or arbitrary later-recurrence claim.
