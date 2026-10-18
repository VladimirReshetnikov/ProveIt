# Routing245 coverage pilots

This is a source-only measurement plan. No supplied checker, symbolic execution, Lean compiler, guard or version query was run. SiteRouting245 is still an unselected provider in this plan. Its source retains margin 64 and checker fuel 4000. Seven independently bounded pilot units cover nine guarded cases; they do not assert complete 8,391-case coverage.

The selection parses the delivered `68-route245-certificate-sites_logical.json` and independently expands all 203 literal row definitions from the maintained, checked ProgramRouting245 source. The resulting 6,460 ordered leaves match byte-level metadata exactly. It also parses all 6,459 original Prog254 rows and confirms unchanged instruction/operand order, with 6,241 changed paths. No routing or machine simulator is imported or called. The complete source prefix tree has maximum depth 51, maximum zero run 6, and maximum one run 12. Zero-run length here describes instruction-pointer bits; arbitrary additional zero gaps remain a parameter of the symbolic soundness theorem.

| Suggested order | Leaf index | Role | Instruction | Depth | Previous depth | Guards |
|---|---:|---|---|---:|---:|---:|
| 1 | 1704 | Deepest increment | CI 1 | 51 | 33 | 1 |
| 2 | 1609 | Longest zero run, deepest such decrement | CD 2 | 42 | 25 | 2 |
| 3 | 1703 | Deepest decrement | CD 6 | 50 | 32 | 2 |
| 4 | 1705 | Deepest continue | CC 2 | 51 | 33 | 1 |
| 5 | 1720 | Deepest changed break route | CB 1 | 47 | 30 | 1 |
| 6 | 4730 | Longest one run | CC 2 | 35 | 27 | 1 |
| 7 | 6324 | Sole halt | CH | 13 | 13 | 1 |

The six nonhalt paths changed. The halt path did not; it still requires a check against the new literal machine. These choices cover every instruction kind, the two deepest leaves, a longest-zero-run path, an unusually long one run, and both guards of two decrement sites.

Each source imports only ProgramRouting245 and SiteRouting245. It defines one exact literal `path` and `instruction` and asks Lean to prove two statements with `decide +kernel`:

1. `twalk TreeRouting245.tree path 0 = some (instruction, exactDepth)`;
2. `SiteRouting245.checkSite path instruction = true`.

The audit calls both theorems and uses the checked `TreeRouting245.walk_eq_tree` to bind the first statement to the actual ProgramRouting245 root walk, retaining `program.nnodes + 1` symbolically rather than introducing the earlier numeral-transparency mismatch. Each decrement audit additionally obtains the zero and positive `runTo` equations via `check_decnz`. Thus the corresponding site check includes both guards; neither is omitted or inferred from a concrete register fixture.

There are two axiom probes per unit, three typed callers for each non-decrement unit and five for each decrement unit: 14 probes and 25 callers in total. The prospective imported closure has 22 project modules, with 17 exact existing objects and five explicitly unselected new Site-chain providers. Init and Omega are the external boundaries. The selected ProgramRouting245 proof record is the actual successful record with SHA `1efd9f64fc8067e85518fc9968752a9a10f78cdeb4f24aa8dd9e8c58d2a53c71`.

Root should run each pilot in a separate source/audit unit, retaining the established shared 120-second budget, `-j1 -M4096`, default proof limits, fresh source object captured before audit and exact input/provider checks. Start with leaf 1704 to measure a deepest changed route, then the zero-run and deepest decrement cases. If one site exceeds the budget or the fuel bound, preserve the failed attempt before choosing any successor. A timeout does not distinguish a false acceptance proposition from excessive reduction cost. If needed, a later explicitly scoped measurement may split a decrement's two `runTo` checks; both successful results are still required to reassemble its accepted-site theorem.

Do not freeze the full grouping or increase fuel from these source predictions. The seven actual results will inform a representative subtree pilot and the complete structural schedule. Every eventual whole-tree join must retain both children of TreeRouting245.tree; a successful handful of leaf checks does not imply `allSites`.

`pilot-plan.json` pins the data, checked Program source/record, original source, current Site source, every emitted source/audit and the prospective boundary. `history/metadata-parser-v1` retains an own-emitter parse failure on unparenthesized `.halt`; `history/metadata-selection-v2` retains the second own-emitter failure caused by an overstrong claim that the halt path changed. Its six already-emitted sources and audits were preserved and are byte-identical to their final counterparts. Both failures occurred in metadata preparation, with no proof or symbolic execution.
