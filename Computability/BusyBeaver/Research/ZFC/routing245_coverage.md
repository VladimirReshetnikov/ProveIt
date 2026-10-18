# Complete decoder coverage for the 245-state machine

[SitesRouting245.lean](../../Lean/BusyBeaver/ZFC/SitesRouting245.lean) proves
`all_sites` for the actual routed program: all 6,460 instruction leaves and
8,391 guarded cases are checked. `actual_walk_checked` applies this result to
every successful decoder walk, and `actual_walk_exists` supplies a walk for
every instruction pointer. These theorems have no external coverage premise.

The selected 624 modules pass 958 named axiom probes and 961 typed callers,
with zero warnings. Every reported axiom set is exactly `propext` and
`Quot.sound`. The [final verification record](results/routing245-coverage-verification.json)
binds the concluding theorem to 646 project prerequisites, including the
other 623 selected coverage modules. The
[complete independent review](routing245-coverage/review/complete-review.json)
checks every selected source, audit, actual first provider, pre-audit object
capture and raw log. It also independently expands the 203-row decoder and
checks that 478 closed blocks and 477 binary joins cover the entire tree.

The family comprises 599 final-generation modules and 25 previously checked
modules: three pilots, thirteen original batches, one second-generation cut
and eight third-generation units. The final refinement limits small blocks
to 32 guards and joins within newly refined cuts to two per file. The outer
composition modules retain their earlier grouping. Each new source and
audit was checked serially with one thread, 4,096 MiB, a shared 120-second
limit and Lean's default proof limits. Total selected source time was
3,629.414 seconds; total audit time was 304.645 seconds. These totals exclude
preparation, review and failed earlier attempts.

The [publication record](results/routing245-coverage-publication.json) lists
the exact selected records. The [history index](routing245-coverage/history.json)
preserves original sources, generators, guards, preparations, reviews and raw
logs as exact content-addressed bytes. Earlier timeout and recursion-limit
failures remain failures; successful providers were reused without replay.
The evidence review's initial parser failure and its narrow `.halt`-row
correction are also retained. No compiled objects or cache symlinks are
included. The historical guards require their exact recorded compiler and
provider caches; this packet does not certify a clean-checkout build.

Coverage supplies the missing decoder premise for the
[runtime simulation](routing245_execution.md). The
[blank-start composition](routing245_binary.md) uses this result in the closed
external Lean endpoint. An object-language PA proof remains separate; this
coverage packet alone asserts neither consistency nor nonhalting.

The program and calculus originate with Mira-Cult, the imported verification
with Jeff Ketchersid, and the compiler framework with Andrew James Wade.
The [candidate page](candidate-routing245/README.md) preserves the exact
transition table and submission provenance.
