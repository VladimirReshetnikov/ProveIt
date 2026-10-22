# One boundary-completeness argument for the Rocq K215 enumerator

This component is a conservative refactoring of the sources at ProveIt commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`. It factors three repeated arguments
between `L1_CompPerm` and `SeedPerm` while retaining all existing theorem names,
statement types, definitions, and client imports.

The new core statements are:

```coq
reach_from_boundary seed k : pl seed = 0 ->
  halts_from seed \/
  exists n s, run n seed = Some s /\ pl s = 0 /\ np s = np seed + k.

halts_from_run seed n s : run n seed = Some s ->
  halts_from s -> halts_from seed.

enum_complete_from_boundary seed :
  pl seed = 0 -> thm222 1 -> halts_from seed.
```

The first proof is the existing general `SeedPerm.reach_from` induction moved
to the shared compiler module. The second is the existing run-addition argument.
For completeness, compile a refutation to a block `L`, set `Y = np seed`, and
encode `START Y :: L ++ SUFFIX`. Its candidate code is

\[
N=P(3,P(Y,P(1,\operatorname{enc\_tail}(L++\mathrm{SUFFIX}))))\geq Y.
\]

The search reaches that candidate after `N-Y` candidate increments unless it
halts earlier. The inherited `program_halts` theorem accepts every working
register tuple, so no invariant on the current formula, stack, cache or
arithmetic counter is needed for this completeness direction. The condition
`pl seed = 0` is retained explicitly. This component does not assert unconditional
soundness for arbitrary initial register values.

Both existing endpoints become direct specializations:

```coq
Theorem enum_complete : thm222 1 -> enum_halts.
Proof. exact (enum_complete_from_boundary s0 eq_refl). Qed.

Theorem seedPerm_complete : thm222 1 -> halts_from seedPerm.
Proof. exact (enum_complete_from_boundary seedPerm eq_refl). Qed.
```

## Measured scope

| Production proof source | Before lines | After lines | Before bytes | After bytes |
|---|---:|---:|---:|---:|
| `L1_CompPerm.v` | 351 | 372 | 15,406 | 16,391 |
| `SeedPerm.v` | 59 | 31 | 2,694 | 1,442 |
| Combined | 410 | 403 | 18,100 | 17,833 |

The source saving is deliberately modest: seven lines and 267 bytes. The
structural benefit is one proof each of candidate progress, prefix transport
and boundary completeness. The old helper interfaces remain as wrappers,
including both `reach` and `SeedPerm.reach_from`, both prefix lemmas, and
`drain`. This compatibility is why the byte reduction is smaller than in a
more invasive removal of those declarations. No whole-endpoint build-time
improvement is claimed.

## Relationship to prior proposals

The repository's `checked-transport/rocq_seed_rank` proposal already develops
a stronger arbitrary-state completeness theorem using a ranking argument. It
removes the older scheduler helper declarations. This component is an
alternative aimed at preserving every existing helper API, and reuses the
existing general seed induction. Generalizing the start state and prefix
transport are established proof-engineering ideas, not mathematical novelty
claims. The contribution here is the small compatible patch, synchronization
of maintained and generated files, and focused fresh checks at the selected
main revision.

## Integration

`integration.patch` changes five files:

- The two maintained templates in `k225-formal/rocqperm/`.
- Their generated `K215F` counterparts under `rocq/rocq-extension/coq/215/`.
- The corresponding two digest entries in `rocq/rocq-extension/manifest.json`.

The generated headers use the exact SHA-256 of the new templates and the
existing namespace substitution. No generator logic, machine table,
enumerator transition, formula encoding, command semantics or source program
changes. The old production verification receipts are not modified or promoted.
Apply the patch to the pinned revision, regenerate through the normal workflow,
and rebuild the affected production endpoint before treating it as adopted.

## Reproduction and verification boundary

**Observed result: PASS.** Coq 8.18.0 / OCaml 4.14.1 freshly compiled all eleven
modules in each lane. The baseline audit printed nine closed assumption
reports; the candidate printed twelve. Both recursive `coqchk K215F.Audit`
runs exited zero. All 46 original theorem headers are identical. The exact
logs, source/object bindings, source metrics and verification summary are
retained in `evidence/`.

Run with Coq 8.18 or a compatible Rocq toolchain:

```sh
python3 reproduce.py --out /tmp/k215-enumerator-boundary-check
```

The output directory must not exist. The script builds the baseline and
candidate in separate fresh trees, checks eleven source modules in each,
and recursively rechecks each typed audit with `coqchk`. Compilation is
serialized through the repository's shared proof-build lock. The distributed
production sources retain their original import spelling; for Coq 8.18 the
build copies change only `From Stdlib Require` to `From Coq Require`.

The typed audit checks nine exact original interfaces on both sides and three
new interfaces on the candidate side. Their `Print Assumptions` reports must
all be closed under the global context. The original theorem statement
headers in both touched files are also compared exactly. The auxiliary
arithmetic-code sources are the pinned copies already present in the
repository's shared-core proposal; `source_provenance.json` records their
repository paths and hashes.

This is a focused compiler/seed compatibility check. The full 237-module
Rocq 9.1 production machine-to-ZFC closure is not rebuilt by this component,
and no new internal ZFC derivation or smaller machine is claimed. Any timings
in the local logs are measurements of this particular run, not a controlled
performance comparison.

## Attribution

The machine, enumerator, encoding, calculus, compiler, original reachability
proof and prior refactoring ideas are inherited from ProveIt and its credited
sources. `LICENSE.ProveIt` preserves the repository license. The source files
retain their inherited attribution comments.
