# Actual literal control catalogue and deterministic resolver

`FiniteControlTable254.lean` derives the6,460 source leaves of actual literal
`Prog254.program` from its already checked `ActualTree254.tree`. It proves
source-instruction acceptance, unique source indexing, and a deterministic
consumed-path resolver. It does not yet supply an arithmetic table graph,
represented control step/run, or internal L2/scheduler simulation.

`leafEntries` recursively concatenates false-prefixed left leaves and
true-prefixed right leaves. Generic soundness/completeness identifies exactly
`SiteCoverage.LeafAt`, and a prefix-separation argument proves `Nodup`. Its length
is the existing tree leaf count, so the actual6,460 count reuses the closed tree
proof. A `Control` is `Fin6460`; `number` gives live codes1..6460. Each indexed
source inherits `checkSite=true` from `SitesPerm252.all_sites`. This imports the
completed site proofs rather than evaluating a binary guard again.

`source_walk` and `source_follow` bind each indexed path/instruction to the
actual6,459-node literal program. `source_injective` proves unique catalogue
indices. These are source-path pairs: identical register instructions at
different leaf paths remain different controls. This module does not replace
the source with the219-node structured DAG or treat an instruction name as its
full continuation.

`resolveControl P` executes the existing finite native walk with its literal
fuel and implicit trailing zeros. The resulting `(consume P depth,edge)` belongs
to the derived catalogue by existing tree/walk lemmas. Deterministic `List.idxOf`
then yields its in-range control. The impossible missing-walk branch is eliminated
inside a False proof using existing total coverage, without extracting a witness
from Prop into data. A generic lawful-equality index lemma proves
`source(resolveControl P)=(consume P depth,edge)`, and resolving an indexed source
path recovers its exact index. Empty input resolves to index0/live control1,
whose source is path000/`decnz8`. No register or binary step is executed by those
finite equalities.

The resolver may discard a nonzero suffix after the consumed leaf, as the native
walk does. Exact binary frame rebasing still requires the separate `Clean`
premise and padding theorem. No whole-configuration equality for arbitrary
unclean input is inferred here. Zero and out-of-range numeric control policies
belong to the future total arithmetic interpreter; this finite API never returns
an out-of-range `Control`.

The focused pinned Lean4.32 check passed in0.641032s for the227-line source and
0.471319s for the47-line audit:14 ordered probes,17 callers, only standard axioms,
and zero warnings. It reused32 exact native source/object providers from the
169-unit core evidence, with no Foundation/Mathlib imports or dependency build.
All74 inputs and the fresh object were unchanged after the audit. Existing
233 coverage chunks,8,391 binary guards and82,552-step bootstrap were not replayed.

Four unsuccessful source attempts are preserved separately: pure Std requires
`theorem` syntax rather than the imported `lemma` convenience; explicit list,
projection and dependent-match normalization; then the generic index proof had
to use the actual selected `BEq`/`LawfulBEq` instance rather than a definitionally
different fallback. The final helper derives DecidableEq constructively from
that selected equality. These repairs changed neither catalogue data nor the
resolver algorithm or its main source/resolver endpoint contracts. The helper
`entry_at_index` explicitly changed its typeclass API to the selected `BEq` and
`LawfulBEq`, instead of the former fallback from `DecidableEq`. No failed audit is reported as passed.

A portable fresh focused check uses existing matching core objects:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_finite_control_table254.py \
  --repo /path/to/Proofs \
  --core-evidence /path/to/command-word254-integration-verification.json \
  --output /outside/new-empty-directory
```

`--prepare-only` checks the actual compiler, source/object closure and first
Init/Omega providers without proof compilation. `--cache` relocates the32 project
objects only if their recorded hashes match. No downloads, dependency builds or
coverage/bootstrap replays occur. The original successful driver/record remain
unchanged; the maintained guard freezes the final source pin. Four negative
controls reject optimized Python, nonempty output, a wrong selected project
object and modified pinned core evidence. The guard has no arbitrary library
path override, so Init/Omega are checked positively rather than through a shadow
library control.

Successor columns can now be defined directly by resolving the source's actual
incPath/breakPath/continuePath. Their source correctness follows from the generic
resolver theorem, avoiding a second generated8,390-case successor certificate.
The checked compact lookup/frame substrate can then classify arbitrary internal
control indices and apply the existing all-model rebasing cases. Numeric-key
coherence, fixed nine-field logical state, represented iteration and the genuine
internal structured/scheduler bridge still require proofs. No new state bound,
calculus simplification, binary endpoint or PA consistency statement follows.
