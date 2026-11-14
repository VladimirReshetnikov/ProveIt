PA195 -- a 195-state binary Turing machine for Con(PA)
====================================================

Main deliverables
-----------------
report/pa195_conpa.pdf       Complete article, ordinary PA proof, comparison,
                            all 390 transition rows, and 27 archive summaries.
report/pa195_conpa.tex       Main LaTeX source; sections/ contains its inputs.
pa195/pa195.tm              Definitive literal five-column transition table.

The machine has 195 working states 0..194, start 0, and separate halt 195.
It uses one two-way infinite binary tape, initially all 0, with head at 0.
Every working state has one row for each read symbol. The halt control is
excluded from the 195-state count. All 195 states are graph reachable.

The article gives an ordinary mathematical proof of the statement

    PA proves: Nonhalt(PA195, blank) if and only if Con(PA).

The theorem is not conditional on PA being consistent. Actual nonhalting
follows if PA is consistent. A newly kernel-checked end-to-end Lean or
Rocq theorem is NOT claimed. See article Sections 1.2 and 5 for the exact
proof scope and the distinction from the published internal implication.

Machine SHA-256
--------------
5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455

Reproduce the new result
------------------------
From this directory, using Python 3 and its standard library:

    python3 -B pa195/build_verify.py
    python3 -B verification/verify_independent.py pa195 --concrete
    python3 -B verification/check_engine.py

No network, search, solver, or proof-assistant installation is required.
Do not use Python -O, because inherited parsers use assertions. The first
command includes all 4,815 universal symbolic primitive-branch contracts for
both the 202-state unfolded parent and the 195-state folded table. It also
checks the exact source graph, full-stack emitter identity, all 28 local
quotient cases, and the complete 58,154-step blank startup.

The second command imports none of the compiler or symbolic executor. It
checks the source control graph using a separate algorithm and the startup
using two tape representations. With --concrete it runs 19,260 finite frames
(8,234,830 literal steps). These finite controls complement, and do not
replace, the universal symbolic contracts.

The third command directly checks the 46 protected engine rows against the
pinned upstream Lean text and table. It checks that all 45 literal premises
needed by the native register-box theorem are present.

The first command's --export switch reconstructs the derived source,
startup, quotient, and validation artifacts. The table itself is rebuilt
in memory and compared exactly on every run. See pa195/README.txt.

The new reduction
-----------------
The supplied diagonal196 association has 134 inherited controls, 68 newly
allocated AX readers, and 6 compatible folds: 134+68-6=196. The new association
keeps 68 readers and admits 7 compatible simultaneous folds: 134+68-7=195.
The 191-token diagonal AX word, all 3,700 primitive operations and their exact
ordinal successors, all formula parameters, and the register engine are
unchanged. The global quotient proof uses 22 incoming-history rows and 28
exhaustive two-cell cases, with positive durations 1, 3, or 5.

Comparison and evidence
-----------------------
comparison/frontier196_and_pa195.json has 25 supported archived 196-state
classes, plus the new 195-state result. Of those 25 prior classes, 23 have
complete evidence in their supplied reports; 2 archived tables received
their missing full contract or startup check in this audit.

comparison/196_classification.json classifies all 90 rooted 196-state graph
classes (268 occurrences, 131 literal byte strings). The other 65 classes
have partial, bounded, or negative evidence. No class is silently promoted
from finite samples to a universal refinement claim.

comparison/prior196/ contains all 25 normalized prior tables and the complete
state bijections. Their working states are 0..195, start 0, halt 196. These
labels differ from the original labels; exact mappings and hashes are in
manifest.json. It is not valid to interpret their rows using PA195's labels.

comparison/u208_census.json identifies 20 rooted U208 classes among 27
designated presentations. comparison/rejected195_census.json records the
earlier six candidate constructions, represented by 14 table occurrences,
which do not supply a certified smaller result. The archive/member census
covers all 27 incoming ZIP files at the pinned repository commit.

Optional comparison recheck:
    python3 -B comparison/check_two_additional196.py --extracted PATH

This optional command, unlike the self-contained PA195 checks above,
requires extracting the original conpa_tm_study_2026-11-13.zip and
pa_tm_research_2026-11-13 (2).zip into PATH, each under a directory named
after its ZIP stem. It replays the two newly completed prior 196 audits.
The pinned archive/member locators are in the frontier manifest.

Proof sources and verification status
------------------------------------
report/sections/pa_calibration.tex supplies both PA directions, including
uniform finite bit-comprehension proof generation, code freshness,
variable collisions, the truth-code and zero-stack aliases, the exact live
command-store invariant, and positive source-to-tape simulation.

report/sections/fold_proof.tex proves global halting equivalence of the
unfolded 202-state and folded 195-state tables for every initial tape at
their designated starts. The arithmetic application uses blank input.

reference_sources/ contains selected unmodified upstream Lean files with
pinned URLs and hashes. It is review material, not a complete new Lean
project. pa195/vendor/ contains the inherited compiler, symbolic executor,
reference fragments, and original licenses. No formal proof build is
required by, or falsely implied by, the executable certificates.

verification/ contains the independent checker, portable engine audit,
fresh package-run receipts, and separate mathematical/runtime reviews.

Build the article
-----------------
With a normal LaTeX installation containing the packages named in the
preamble, run:

    cd report
    latexmk -pdf -interaction=nonstopmode -halt-on-error pa195_conpa.tex

Alternatively run pdflatex with those flags twice. All source fragments
are included. No external figures or bibliography downloads are needed.

Source provenance
-----------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 906367250a7f96c923147b10df392294bced7be5
PA196 upstream: 407cdc356f6b586635e71ac92be394255f4bfea4
Inherited diagonal archive:
docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip
Archive SHA-256:
6fcb1cf2878eda152beda0b17cc0242c003908fa8adf07c81a2bbf49870f1866

The new work is the compatible physical association/allocation, its exact
certificates, the consolidated comparison, and the complete written PA
calibration for the resulting table. The diagonal-vacuity idea and its
191-token emitter are credited to the supplied incoming research.

SHA256SUMS at this directory level binds every delivered file except the
manifest itself. The inner pa195/SHA256SUMS is the frozen machine-packet
manifest. No claim is made that 195 is globally minimal.
