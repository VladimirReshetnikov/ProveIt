# Literal periodic Langton ant interface proof packet

## Result

The literal interface gate passes: one fixed doubly periodic RL-ant board, a fixed head start, an explicit finite input perturbation for each pair of finite nearest-head-first U15 tape words, and a fully specified head-port event equivalent to U15 halting. The entire infinite physical trajectory visits each cell at most twice. The ant continues after simulated halt.

The fixed rule is color0=right, color1=left, with turn/flip/move at the current cell. Snapshots and acceptance are before departure. The source alphabet and all geometry are explicit. The table has32 primary states, with J1=21; it does not inherit the separate34-state sandpile convention.

Qualitative periodic-background universality and the two-visit principle belong to Maldonado, Gajardo, Hellouin de Menibus and Moreira. This packet supplies a literal checked realization and interface. It does not claim a new qualitative universality theorem, finite-blank-background universality, or a fixed-site return gadget. See SOURCE_PROVENANCE.md.

## Exact interface

- Rectangular board periods:576000 by481238074400
- Fixed head:(288650,75,E)
- Input: finite binary words ell,r, both nearest-head-first; U15 starts in A scanning0, with every other tape cell blank
- Changed cells:2812+4(popcount ell+popcount r), including a fixed2806-cell anchor and the word-length-dependent endpoint marker
- Acceptance: heading S before departure, and either residues(546702,240606225650) or(258702,481225262850) modulo those two periods
- No color stencil is required

Only the second accepting clause can occur on valid primary-loaded runs. The first is retained as part of the uniform staggered two-phase interface and is proved harmless.

The fixed Boolean cell has862 NAND gates. Its601547591-row physical instruction program is specified exactly by a compact grammar with random access; neither its complete row list nor the dense board is materialized. The block width is576000, block height240619037200, with958 active storage columns. A conservative per-block control bound is15274393040715416 ant departures. These dimensions and costs are explicit construction bounds, not optimized claims.

## Read these first

1. `atlas/PROOF.md`: global simulation, all-history visit bound, marker controller, loader, observer exclusivity and quantitative scope
2. `copy/GLOBAL_GENERATOR_REVIEW.md`: independent global geometry and proof review
3. `copy/program_audit/ANALYSIS.md`: independent exact compressed-program audit
4. `atlas/generator.py`: literal color query for every integer coordinate
5. `atlas/compile_input.py`: public fixed loader; the caller cannot choose an anchor, program or hardware board
6. `atlas/observer_polarity_receipt.json`: uncomplemented h at the physical accepting DUP, checked on all16777216 Boolean cell inputs

All finite cell maps, legal histories, trajectories, source pins and independent receipts are included. Full downloaded articles, PDFs, source archives and rendered article pages are not packaged.

## Reproduction

Python3 with its standard library is sufficient. From any working directory, run the absolute path to the packet's driver, for example:

    python3 /absolute/path/to/packet/replay_all.py

The driver works in a fresh temporary directory with cwd `/`, executes only this packet's own scripts, and compares regenerated outputs byte-for-byte. It uses no network, upstream code, repository clone, dense ant board, or expanded601-million-row program. It runs28 own commands and compares39 regenerated outputs byte-for-byte. Its receipt gives each command's scope. The27 explicitly guarded entry points reject optimized mode; the two exceptions below are marked unsupported and not run under optimization.

Assertions carry checks. Do not use `python -O` or set `PYTHONOPTIMIZE`. The driver and all component commands with explicit rejection guards are tested to reject optimized mode. Two standalone commands, `copy/translate_anchor.py` and `copy/program_audit/verify_program_index_bounds.py`, have no explicit optimized-mode guard and are not run under `-O`; their supported replay is the unoptimized guarded driver. No optimized execution of them is claimed to pass.

To produce a concrete finite initialization, with the first character nearest the head:

    python3 atlas/compile_input.py --left 101 --right 0110 --output input.json

The empty-word example and exhaustive loader checks through length3 are included. Word lengths remain relevant for zero-only words; their endpoint marker is not discarded.

## Boundaries retained

- The fixed U15 table and pair-to-ant loader are implemented. An arbitrary-program-to-U15-pair compiler is not implemented; published U15 universality remains a separate dependency
- The matched north-facing bounded-board coordinate convention is given in the proof, but no initial arithmetic word, raw-input dilation,174-operation composition or improved universal arithmetic bound is claimed
- The companion one-visit lower-bound proof is a separate packet and must be reviewed in the precisely matching observation model before stating a sharp threshold
- Component receipts deliberately retain their local scope: a Boolean-DAG receipt, finite macro receipt or nonuniversal benchmark receipt alone is not the global theorem

This packet preserves the earlier sealed finite-gadget gate audit. No upstream code was executed and no public repository write was made.
