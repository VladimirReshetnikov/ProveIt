# Checked transport and seed-rank proofs for K215

Research contribution for ProveIt, 21 October 2026. Read `report.pdf` for the
mathematical argument, candidate comparison, and bounded state-reduction
investigation; `report.tex` and its section files are editable sources.

**No verified machine with 214 or fewer working states was obtained.**
The 214-state table in `state_reduction/research/` is explicitly rejected and
is included only with its valid-frame counterexample and independent checker.

## Main results

1. **Concrete Context215 transport.** The existing five-row Context215 patch
   now has a checked all-tape halting equivalence with the exact old native
   K215 table. The proof uses a seven-control inductive guard, an eleven-row
   invariant-preservation slice, and a full-tape positive-duration simulation.
   Both literal 430-row tables and their 215-state counts are bound to the
   theorem. A new checked adapter connects the literal Context215 blank-run
   predicate to the repository's actual sparse K215 halting predicate.
2. **A single scheduler rank.** The refactor uses
   `R_N(s) = (N - np(s))*(N+1) + pl(s)` and eliminates three separate scheduler
   inductions. The checked compiler theorem now proves completeness from
   *every* initial enumerator state. The equivalence still requires the
   ordinary soundness invariant on formula, cache, and stack. Existing public
   enumerator/seed endpoint types are preserved.
3. **Local opacity.** `Local Opaque P wim wal wex weq wel.` leaves the existing
   soundness scripts and statements unchanged and avoids incidental expansion
   of arithmetic formula codes. Observed module times were 43.290 seconds
   before, 0.810 in the isolated trial, and 0.665 in the final focused build.
   These are local Coq 8.18 observations, not a whole-project benchmark.
4. **Scoped physical search.** Two complementary fold implementations ran on
   22 pinned tables. Neither found a complete fold. A synthetic positive
   control exercises changing both branches. The 19 partial primary folds
   identify concrete missing obligations; the 52/154 trial demonstrates why
   intended local blocks alone do not justify borrowing a live helper row.

## Verification status

| Item | Actual status |
|---|---|
| `NativeContext.v`, `LiteralBindings.v` | Compiled; selected assumptions closed |
| Exact native-to-sparse adapter and literal composition | Ten-module closure compiled; recursive `coqchk ContextLiteralSparse` passed |
| Rank/opacity refactor | Ten project modules and typed client compiled; six selected assumption reports closed; recursive `coqchk` passed |
| Context family | Independent audit of 32 masks; ordinary block proof, not a compiled all-mask theorem |
| Search and rejected trial | Complete scoped searches recorded; independent literal counterexample replay and positive control passed |
| `adapter/ContextZFCClient.v` | Source composes the real `Correct215` endpoint; **not freshly compiled with the full ZFC closure** |
| Lean port | Concrete proposal only; no Lean build performed |

The recorded proof toolchain is Coq 8.18.0 / OCaml 4.14.1. The production Rocq
9.1 lane was not rerun. Private rank-build copies adapt `From Stdlib` to
`From Coq`; no compatibility theorem is assumed. The exact minimal native
adapter includes its pinned upstream dependency source. An imported tactic
library declares global axioms, but the reported endpoints have closed
assumptions and do not depend on those declarations.

The complete ZFC client imports `K215F.Correct215` and its real
`tm215_sparse_halts_iff_ZFC_inconsistent` theorem. It has no hypothetical
calibration premise. Compile that client inside the maintained full K215
lane to record the final integration check. The ordinary mathematical
composition is immediate; the archive does not describe it as a fresh
end-to-end rebuild of the 237-source closure.

## Layout

- `report.tex`, `report.pdf`, section inputs: full editable research report.
- `transport/`: exact tables, concrete transport, literal bindings, byte audit.
- `adapter/`: exact BusyCoq/sparse-semantic bridge, final composition source,
  minimal dependencies, reproducible build, final receipt and logs.
- `rocq_seed_rank/`: baseline and refactored sources, three patches, exact
  dependencies, typed interface client, reproduction driver and receipts.
- `comparison/`: candidate-status analysis and the 32-mask family audit.
- `state_reduction/`: 22 table inputs, source sites, both search implementations,
  inherited helper-resynthesis code, receipts, nineteen partial pairs,
  positive control, clearly rejected 214-state trial and complete traces.
- `latest-refresh.json`: targeted baseline/latest source-identity check.
- `manifest.json`: SHA-256 values for all delivered files except itself.
- `NOTICE.md`, `LICENSE`, component notices: inherited attribution and licenses.

## Reproduction

Python 3.10+ and its standard library suffice for the default audits. Use a
new output directory outside this archive:

```sh
python3 -B reproduce.py --out /tmp/k215-quick
```

This verifies the root manifest, native bytes/Coq literal lists, five-row
patch, table completeness, critical invariant slice, 32-mask family, 22 input
hashes, independent rejected-trial replay and positive-control blocks.

To repeat both minimal formal proof closures as well:

```sh
python3 -B reproduce.py --out /tmp/k215-proofs --proofs
```

This requires `coqc` and `coqchk`. It compiles in fresh output directories,
retains logs and timings, and excludes the full ZFC client explicitly.

Optional full finite-search replays:

```sh
python3 -B reproduce.py --out /tmp/k215-search --full-search --context-search
```

The two complete corpus searches and contextual-helper filter were already
executed; their receipts are delivered. The pair-choice counts overlap and
must not be added. Window exits or failed symbolic derivations are unresolved
proof obligations, not semantic counterexamples.

To regenerate the report, install a normal TeX Live distribution with the
packages named in `report.tex`, then run `pdflatex report.tex` twice. For source
review and downstream changes, compare the component patches with their
included exact baseline files. Update maintained `rocqperm/` templates as
well as generated `rocq/rocq-extension/coq/215/` copies, refresh metadata, and
run the normal production endpoint build. The archive's patch targets use
`K215F` imports; maintained templates use `NS` and should not receive generated
provenance headers.

## Source pins and inherited work

Baseline ProveIt commit:
`aa66d0a33f1f8237a348899eb8095b045a502832`.
Targeted latest refresh:
`b0663213602b3635258150c58ffe105a2e0ba44f`.

The five relevant compiler/soundness/seed/table/semantics source blobs are
unchanged between those pins. Latest upstream automatic-certificate work,
Lean semantic-round-trip reuse and predecessor-specific elimination are
credited in the report. The upstream 21-table search corpus is contained in
our 22-table corpus; the search grammars are complementary and overlap.
There is no claim that finite-window or stuttering methods originated here.

The accepted K215 calibration, numerical calculus, original machines,
Context215 retargetings and ordinary block proof are inherited. This packet
adds checked concrete application and integration, the stronger enumerator
interface, scoped reproducible experiments, and an explicit obstruction.
It does not prove consistency, unconditional nonhalting, or a lower bound of
215 states. The remote repository was not modified.
