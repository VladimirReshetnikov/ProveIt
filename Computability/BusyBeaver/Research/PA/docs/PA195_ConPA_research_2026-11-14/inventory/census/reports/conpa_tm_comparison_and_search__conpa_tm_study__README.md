# Binary consistency machines: comparison and a search below 196 states

**Outcome: no verified machine with fewer than 196 working states was obtained.**
The requested construction remains unfinished. This archive is a reproducible
comparison and research record, not a claim of a new 195-state Con(PA) machine.
Files whose names include `195` are explicitly rejected or diagnostic candidates.

Start with `report/report.pdf` (the complete report) and `STATUS.json`. The TeX
source is `report/report.tex`. The report can be compiled on an ordinary TeX Live
installation with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory report report/report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory report report/report.tex
```

## Main verified findings

- The nine designated final 208-state tables represent exactly two rooted,
  action-preserving transition-graph isomorphism classes, containing five and four
  tables. They have the same resolved source control flow.
- The requested James Chang 209-state predecessor is distinct from the U209
  parents of those 208-state constructions.
- PA209 and PA196 have 134 native state names in common and only three changed
  rows among their 268 common rows. Removing 75 old controls and adding 62 gives
  196. The U208 fold roles are already absent and cannot supply another deletion.
- The exact PA196 literal startup and all 4,959 symbolic primitive contracts
  reproduce. These finite checks do not prove nonhalting by themselves.
- A rotated 195-state quotient preserves the resolved source control flow but
  fails 93 primitive contracts. Its identical-row quotient is valid; the
  preceding rotation already breaks the history-sensitive source decoder.
- A written universal Boolean-valuation proof shows that replacing the equality
  witness axiom with reflexivity produces a calculus whose consistency PA proves.
  That shortcut cannot retain the requested PA-provable equivalence with Con(PA),
  assuming PA is consistent.
- A new196-state alternative exchanging physical registers A and D passes all4,959 runtime contracts and reaches the clean frame after58,122 literal steps. It is included as a comparison point; it does not reduce the state count.
- The internal converse for the published196 machine is discussed as a proof
  strategy with outstanding exact trace/proof-coding and arithmetization bridges,
  not as a new Lean theorem proved in this work.

## Quick offline reproduction

Use Python 3.11 or newer, from this archive's root directory:

```sh
python run_checks.py
```

No third-party Python packages are required for this command. It checks:

1. All eleven literal tables and the exact source/table comparisons.
2. All 4,959 PA196 symbolic branch contracts.
3. The exact 58,154-step blank startup.
4. All 4,959 contracts of the rejected two-rotation195 candidate, reproducing93
   failures (this failure is the expected successful test outcome).
5. A scanner-shortening counterexample that halts from blank after699 steps.
6. The numerical regressions accompanying the reflexivity obstruction.
7. The new196-state A/D-swap table: all4,959 contracts and58,122-step startup.

The symbolic checker fields `max_steps` and `total_steps` count evaluator iterations with accelerated register oracles; they are not literal TM time bounds. Startup and the699-step halt are literal transition counts.

The command writes `checks/verification_result.json`, a fresh comparison output,
and the explicitly rejected195 table and failure list. It exits with a nonzero
status if any expected check changes. It does **not** establish a global lower
bound or a new nonhalting theorem.

## Other replayable searches

Research scripts should be run from the archive root, because some use relative
paths. The bundled `support/` infrastructure is an identified, previously
supplied input. Examples:

```sh
python search_root/global_rotations.py
python search_root/repair_history_alt1.py
c++ -O3 -std=c++17 search_root/coupled_history.cpp -o /tmp/conpa-coupled
/tmp/conpa-coupled search_root/repair_history_alt1.contexts.txt 240
c++ -O3 -std=c++17 search_root/donor_history.cpp -o /tmp/conpa-donor
/tmp/conpa-donor search_root/repair_history_alt1.contexts.txt 240
```

The coupled router search enumerates608,400 pairs of rows, in a finite tape
window and with a240-step bound. It found no survivor. Other layouts have their
own context files and logs. The ideal router used to generate these contexts is
an analysis oracle, not a state of a valid Turing machine.

Optional MILP scripts require NumPy and SciPy. Large source-reachability and
engine searches require a C++17 compiler and the prepared data named by the
individual script. Consult each branch's notes and receipts for search scope,
completed bounds, and dependency paths. Some inherited work files describe
previous experiments; their presence does not mean those old experiments were
rerun here.

## Directory guide

| Directory | Contents |
|---|---|
| `report/` | Full report in TeX and PDF |
| `comparison/` | Eleven requested tables, sites, conjugacies, exact comparison, provenance and original licenses |
| `checks/` | Fresh principal verification outputs |
| `proof_notes/` | Universal reflexivity obstruction, bootstrap constraints, and internal reverse proof strategy |
| `rejected195/` | Dense and native rejected table, status and concrete failed contracts |
| `search_root/` | Joint helper model, exact local contexts, coupled searches and global rotations |
| `research196/` | New logical, grammar, pairing and allocation experiments; complete checked196-state A/D-swap table |
| `research208/` | New lineage audit, scanner, reachability and engine experiments |
| `research_ipra/` | New logic/decoder investigations and branch status |
| `support/` | Inherited pinned source snapshot, earlier checker/grammar framework and alternative196 layout |

## Provenance and license scope

Pinned sources:

- BusyBeaver196: `407cdc356f6b586635e71ac92be394255f4bfea4`.
- Requested BusyBeaver209: `69d98241a721ead20b4f0b17df9062950b40fbfe`.
- ProveIt incoming and ConciseIPRA: `f7d2482e35cf2f8f3bd03b5a82387ad999243548`.

The earlier incoming `pa_tm_research_2026-11-13.zip` supplied reusable comparison,
source, checker, grammar, alternative196, and physical Lean material. Its own
result was negative. The `support/` files and parts of `comparison/` are retained
from that archive and are not newly authored results. Original notices and the
license chain are preserved under `comparison/licenses/` and in the source
snapshot. The exact table hash of PA196 is recorded in the report and checked by
`run_checks.py`.

No GitHub repository was modified or published by this work. The full Lean
arithmetic development was not freshly rebuilt. Included old build logs are
inherited evidence only. Read the report's proof-status distinctions before
using any construction or consistency claim.

Branch receipts may record hashes before path-only relocation. The top-level `MANIFEST.json` records the exact shipped bytes and is authoritative for this archive.
