# K215 proof simplification

**Research and checked local extensions for ProveIt, October 21, 2026.**

The recommended first change is to choose the decoder's finite plan **before**
quantifying over its tape interpretation. The enclosed Lean proofs establish one
fixed decoder clock and primitive-entry port for every gap and register list in
the actual K215 semantics. A checked source-depth fact gives at least two physical
prefix steps. Semantic edge contracts can then let the existing simulation reuse
that prefix proof.

Read [report.pdf](report.pdf) or its editable [LaTeX source](report.tex) for the
mathematical arguments, exact source references, tradeoffs, and integration plan.
See [REPRODUCE.md](REPRODUCE.md) for commands and [RESULTS.json](RESULTS.json) for
a machine-readable status map.

## Baseline

- Repository: <https://github.com/VladimirReshetnikov/ProveIt>
- Commit: `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`
- Exact candidate: `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm`
- Table SHA-256: `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`

The production checkout was left unchanged. This packet supplies proof extensions,
a proposed source patch, and evidence; it does not claim their production adoption.
The accepted machine, source program, and transition table are not modified.

## Deliverables and validation boundaries

| Item | What is supplied | Completed validation | Remaining integration |
|---|---|---|---|
| Uniform decoder plan | `proofs/UniformDecoder.lean` | Lean 4.32.0; exact source depth and uniform whole-tape run | Integrate into the existing decoder API |
| Exact zipper adapter | `proofs/UniformZipper.lean` | Fresh build of 23 original modules plus these two new files; source hashes and all logs retained | Connect a production site producer |
| Rocq abstract implication proof | `rocq/DominatedImplication.v`, numerical adapter and explicit certificate | Coq 8.18.0 compilation, closed assumption reports, independent `coqchk`; focused adapter uses two pinned arithmetic dependencies and one documented import-name adaptation | Production Rocq 9.1 build, maintained generator and endpoint checks |
| Enumerator abstractions | `proofs/OptionContracts.lean`, `proofs/FairSearch.lean` | Ten printed public results are axiom-free under Lean 4.32.0 | Concrete execution, scheduler and candidate instances |
| Dependency separation | `patches/import_boundaries.patch` and proposed source tree | Reproducible import projection and `git apply --check` | Affected modules, full endpoints, historical wrapper clients and regeneration must compile |
| Semantic edge coverage | Detailed interface and migration plan in the report | Architecture reviewed against current `KSim` | New interface, old-checker adapter and residual-tail producer are not implemented here |

The decoder's concrete results use the standard Lean axioms already exposed by
their imports: `propext`, `Classical.choice`, and `Quot.sound`; their reports contain
no `sorryAx`. The abstract implication and standalone enumerator results have the
stronger axiom-free/closed reports stated above. These scopes are not interchangeable.

## Measured opportunities

The independent finite decoder audit checks 281 local blocks, 430 transition rows,
and all 4,751 source leaves. Counting both decrement outcomes gives 6,176 branches.
Their exact decoder-prefix clocks total 213,945 physical steps. These are finite
trace counts, **not** kernel reduction counts or a measured speedup.

The import proposal changes a scoped BusyBeaver-local endpoint closure from 180 to
167 modules and from 1,989,076 to 1,755,573 source bytes: a net reduction of 233,503
bytes (about 11.74%). Seven external library boundary names remain unchanged.
This is a static projection, not an integrated build or the repository's full
192-module endpoint-closure count.

The generic Rocq core plus adapter occupies 16,044 proof-source bytes, compared with
22,673 for the current production replay: 6,629 fewer bytes (29.24%). The repository
already contains a smaller, 11,190-byte numerical 52-step proposal. The new port's
benefit is sharing Lean's current 58-step abstract derivation and interface. The
certificate and audit scripts are additional review material, not included in the
proof-source savings claim.

## Suggested sequence of repository changes

1. Incorporate the uniform source-plan theorem, checked depth-three fact, and exact
   zipper adapter. Preserve old exported statements with compatibility wrappers
   where needed.
2. Let simulation consume semantic edge coverage; first derive it from the current
   Boolean checker. Then migrate one existing site batch to prefix plus residual
   tail, preserving positive physical progress and every original branch contract.
3. Build and adopt the narrower model-theory imports, including the generator edit.
4. Adopt the common Rocq implication core after production-version checks, or choose
   the existing numerical 52-step rendering if raw source size is the primary goal.
5. Instantiate the option-composition and finite candidate-search lemmas in the
   concrete enumerator proofs.

## Assurance boundary

The repository records an externally checked equivalence between halting and a
finite ZFC refutation. Its negation gives the external equivalence with syntactic
consistency. The pinned verification page distinguishes that result from an
internally encoded PA proof or a derivation in ZFC's own proof syntax. This packet
does not supply that additional internal derivation, a new full endpoint build,
or a new machine-state reduction.

## Evidence and attribution

- `evidence/lean-uniform/`: final 25-module fresh build record and logs.
- `evidence/lean-standalone/`: the option-contract and finite-search assumption logs.
- `evidence/decoder_prefix_metrics.json`: finite census and source pins.
- `evidence/import_boundaries.json`: projected graph, exact byte counts and source pins.
- `rocq/*.json`: focused compilation, explicit-instance checks and comparison receipts.
- `reviews/`: supporting source reviews; these are reviews within this collaboration,
  not independent human endorsements.
- `MANIFEST.sha256`: integrity inventory for the delivered packet, excluding itself.

Historical commands in receipts contain the original absolute build paths. The
portable commands in `REPRODUCE.md` replace those paths. The failed first adapter
elaboration is retained as `rocq/adapter_check_attempt1.json`; the repaired final
receipt is `rocq/adapter_check.json`.

The mathematical implication derivation, accepted machine, and existing proof
infrastructure remain credited to their original contributors. See `NOTICE.md`
and the inherited notices in `notices/`. New material follows the project's MIT
No Attribution terms; inherited third-party terms are preserved.
