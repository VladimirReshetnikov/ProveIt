AX grammar compression: 250-state and 249-state experimental candidates
======================================================================

Preferred proposal: machine-250-oldrho6.tm
Exploratory variant: machine-249-dual.tm

Both are complete binary, one-tape tables with blank symbol 0 and start 0.
The halt target equals the number of working states and is excluded from
the state count. There are respectively 500 and 498 transition rows.

The 250-state candidate retains the original rho6 quantifier row. It reduces
the repository's 254-state *experimental equality-free/base-three program*
to 188 decision states plus 62 framework states. This experimental baseline
is distinct from Mira-Cult's calibrated 254-state benchmark.

The 249-state candidate reduces the repository's dual-rho6 experimental
252-state program to 187 decision states plus 62 framework states.

Machine-generation dependencies are pinned to ProveIt commit
17d0f2eaa650901cda59764dfcc4661c199e49c8. The report's repository review
extends to e7c4cadf9b180e4b1801755b09777a7572412360; the later review does
not change these frozen inputs or the delivered tables.

Within each source variant the exact ordered list of 138 AX macro calls
is unchanged. Only the binary grammar and shared subtrees are changed.
Both sources and outputs have longest decoder zero run 7. The finite control
effect checker verifies that all 19 macro boundaries have only normal finite
exits, allowing association changes without escaping control instructions.
See proof_notes.tex for the precise mathematical source-level theorem.

NEITHER TABLE HAS A PROVED ZFC CONSISTENCY CALIBRATION OR A COMPLETE PROVED
BINARY COMPILER SIMULATION. These are reproducible compiler experiments with a
mathematical source-preservation argument, not new certified Busy Beaver
or ZFC-consistency machine bounds.

Reproduce using an existing pinned ProveIt checkout or partial snapshot:

    python3 verify_candidates.py --repo /path/to/ProveIt

Or fetch only the nine hash-pinned public dependencies:

    python3 fetch_dependencies.py
    python3 verify_candidates.py

The verifier uses only Python's standard library plus those pinned source
files. It rebuilds the 254/252 source baselines, checks both original named
table hashes, verifies each frozen grammar's exact 138-call expansion,
checks macro control effects, generates both smaller machines, independently
normalizes them, and compares both delivered tables byte for byte. No search
is needed to reproduce the outputs. Source snapshots are not redistributed.

The literal numerical audits also run without any external dependencies.
From the report directory, run:

    python3 code/table_audit.py --output results/table-audit.json

This standalone standard-library executable checks both pinned table hashes,
complete binary rows, start/halt conventions, directed reachability, exact
step-bisimulation refinement, and the full one-million-step blank prefixes.
It checks the canonical configuration digests against the existing audit
JSON files. It rejects Python -O/-OO. Numeric tables carry no routine-entry
metadata: AX nonentry is inherited source trace evidence, not a fact this
numeric-only executable independently checks.

Files:
  grammar-250-oldrho6.json, grammar-249-dual.json: frozen grammar certificates
  machine-250-oldrho6.tm, machine-249-dual.tm: complete standard binary tables
  verification.json: successful deterministic replay and table facts
  audit-250-oldrho6.json, audit-249-dual.json: normalization and finite prefixes
  source_pins.json: exact repository commit and all nine dependency hashes
  verify_candidates.py, fetch_dependencies.py: reproducible verifier/fetcher
  proof_notes.tex: detailed mathematical justification and limitations
  ../code/table_audit.py: standalone literal-table and blank-prefix audit
  ../results/table-audit.json: executed standalone audit results

The one-million-step prefixes do not reach AX and are explicitly not evidence
for the changed emitter, compiler correctness, or consistency. All working
states are graph-reachable, and exact step-bisimulation gives singleton
working-state classes (12 rounds for 250; 11 rounds for 249). These facts do
not establish global minimality.

Attribution: Mira-Cult's register program and construction, Jeff's preserved
verification snapshot 297ab8df7e5de329605c3875b4934643b371a5e3, Andrew James
Wade's MIT-0 TMBuilder backend, and ProveIt's experimental AX/coding changes
at 17d0f2eaa650901cda59764dfcc4661c199e49c8. Source 08 already applies
exact-word grammar compression to the original 185-call AX word, reducing
its public-Wade emission from 281 states to 269 = 207 decision + 62 framework
states. See the report's repo_source08 reference and the upstream source08
machine README/rebracketing evidence. The contribution here is the application
to the two experimental 138-call emitters: the frozen 250/249-state grammars,
exact-word certificates, finite-exit audit and resulting tables.
