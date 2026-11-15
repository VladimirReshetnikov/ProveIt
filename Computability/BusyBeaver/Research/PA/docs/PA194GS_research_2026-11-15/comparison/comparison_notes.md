# Pinned comparison of the PA consistency-machine designs

## Exact scope and counts

Pinned repository: `VladimirReshetnikov/ProveIt`, commit
`7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`.

The current tree has **100 filed packet directories** under
`Computability/BusyBeaver/Research/PA/docs` and **six current incoming archives**.
All 1,166 tracked PA `.tm` files were independently retrieved and checked against
the Git blob SHA in the pinned tree (5,904,962 bytes, zero fetch failures).
The six tracked PA ZIPs and six incoming ZIPs were also read recursively; repeated
archive byte payloads were inspected once, with reference aliases recorded.

Final fresh census (including the older tracked ZIPs):

| Measure | Result |
|---|---:|
| Filed packets plus current incoming packets | 106 |
| Tracked PA table files | 1,166 |
| Tracked PA ZIP files | 6 |
| Current incoming ZIP files | 6 |
| Unique recursively inspected archive payloads | 23 |
| Recognized table occurrences | 5,912 |
| Normalized table byte forms | 1,391 |
| Spanning whole action-graph classes, all sizes | 1,169 |
| Spanning 193-state classes | 61 |
| Spanning 194-state classes | 548 |
| Additional nonspanning 194-state diagnostic classes | 2 |
| Named 194-state positive-claim construction classes | 104 |
| Main-table parse errors | 0 |

The **548 + 2 = 550** recognized 194-state classes include experiments, reference
inputs, and diagnostics; this is not a claim of 550 proved consistency machines.
The two nonspanning diagnostics have been independently distinguished by a
one-round directed action/color invariant. They cannot be isomorphic to a
spanning 194-state candidate.

The 104-name ledger consists of 91 historical named classes (each identity
freshly matched to the recognized tables), plus the 13 principal/supplementary
constructions in the six current archives. Those thirteen are distinct from the
91 and from each other under exact action-graph equivalence.

Files:

- `comparison/summary.json`: main freshly computed counts.
- `comparison/occurrences.csv`: all recognized occurrences and explicit
  start-status annotations.
- `comparison/classes.json`: class identities, strong novelty identities,
  and immediate-action congruence counts.
- `comparison/class_occurrences.json`: source aliases per class.
- `comparison/frontier194/`: one complete literal representative per
  spanning 194-state class, sufficient for offline novelty comparison.
- `comparison/nonspanning194/` and `nonspanning194_check.json`: the two
  extra diagnostics and their exact nonisomorphism certificate.
- `comparison/named_designs104.csv`: per-name design, mechanism, source,
  role, and attributed proof-status ledger.
- `comparison/new_incoming_designs13.json`: actual dense-file identities
  and rooted graph hashes for the newest thirteen named constructions.

## Recognition and identity boundaries

`census_work/census.py` recognizes complete numeric five-column `.tm` files and,
inside archives, four explicit JSON encodings: whole-table strings, lists of
five-column rows, lists of row strings, and dictionaries keyed by state/read with
three-component transition values. It does not execute arbitrary generators or
infer tables from Lean or prose. The 12,346 direct tracked JSON files were not
all independently scanned in this run. Recent incoming reports contain broader
previous JSON audits and report no additional frontier classes, but that is
attributed evidence, not a newly reproduced all-JSON census. The direct JSON
recognition boundary should remain stated.

A declared `start N` comment is retained separately. Dense state 0 is recorded as
**a convention requiring provenance**, not treated as a fact of every file.
This matters for the HAZ packet, which shipped native tables densely relabeled
without moving the actual start to 0. Unknown native starts are not invented.
For structural novelty the comparison is stronger than a rooted comparison:
it checks all spanning roots, arbitrary control renaming, reflection, global
bit exchange, and erased write/move decorations on halt-entry transitions.
Global bit exchange is only a structural-novelty test; it is not asserted to
preserve behavior on an all-zero tape.

All 548 spanning frontier classes remain distinct under that enlarged
comparison. All 548 also have **194 classes in their greatest immediate-action
congruence**. Thus an ordinary transition-preserving bisimulation quotient
cannot reduce any of these exact tables. This finite fact says nothing about
contextual tape invariants, changed machine rows, or a universal state lower
bound.

## What the design families actually change

A useful comparison groups the constructions by independent design decisions,
not by packet title. Most are combinations within the same numerical-calculus,
unary-register-machine architecture.

1. **Original source and allocation.** Primary PA194 uses 67 reader controls and
   seven contextual folds. A second allocation uses 68 readers and eight folds.
   Both target the original ten-entry AX interface, separate diagonal calculus,
   and enumerative proof search. A lower raw reader count is not itself a lower
   final machine count; additional fold opportunities can offset it.
2. **Formula constructor coefficient.** M4R, M5, M6 and coefficient-five/six
   descendants change numerical formula coding and its grammar. This is a real
   source encoding change, requiring hereditary proof recoding and zero-alias
   handling, but the certified final implementations still have 194 controls.
3. **Modus-ponens cache discipline.** C/CS keeps the successful consequent in the
   cache and clears the visible top. N variants omit the dummy zero push while
   retaining the original sum guard. H variants use cache-only contradiction
   detection. The latter requires the proper final Pop sequence in the
   completeness compiler; testing only the visible top or only isolated MP
   calls does not establish all-store proof search.
4. **Symmetric comparison.** CS, HS, QHS, SUMS, AX11S/GHS, GDHS, and now H5XS and
   JH5XS exchange comparison operands and eliminate a restoration loop. The
   newest witness variants preserve the entire incoming-store command effect
   but need an extra fixed controller, paid for by another contextual fold.
5. **Logical-head presentations.** Q exchanges the curried premises of a
   distribution head. D/GD changes the diagonal selector. H5X introduces an
   independent witness consequent; JH5X additionally couples a first-head
   change. These need explicit syntactic translations, including a noncircular
   explosion bootstrap, and are not merely relabeled tables.
6. **AX11.** The eleven-entry, four-operand interface pushes the guard and falls
   through the complete MP operand reader. It shares existing reader/push
   machinery, but every selector and the fourth operand must be compiled.
7. **Generalization and diagonal operands.** G uses an explicit first AX operand
   as binder, shortening the command word. GD independently selects the binder
   and diagonal witness. AX11GDH/GDHS combine these with the eleven-entry
   interface and cache-only guard. Shorter words do not automatically yield
   fewer reader subtrees or fewer physical controls.
8. **Known-zero returns.** A/F/J/ZR/R/CSZ/CZ/HA/HAZ and the CSZA siblings replace
   selected jumps by decrements of registers proved zero. Correctness requires
   both an invariant at recurring source boundaries and a valid blank startup.
9. **Physical register placement.** AD/TDY/P5/HX/HR and the new HC4/C32 preserve
   logical commands but move logical registers among unary blocks and rewire
   selectors. These alter actual complete-tape behavior, rather than merely
   changing the names of controls. The HR placement substantially reduces
   startup time but does not reduce the state count.
10. **Reader topology and loop continuation.** B/4L/LC/QH4L/QH4R and the new
    OR/ORH/MP reassociate source trees while preserving resolved primitive
    instructions. A subtree entry can also have a hidden history-selector
    function; ORH's necessary repair is why its tempting 193-state precursor
    was rejected.
11. **History selectors and guarded shortcuts.** SEL/SF/F/LCG/LCGS/marker-separation
    variants exploit a known neighboring bit to share controls or replace three
    parent transitions by one child transition. They require a complete local
    tape identity and an inductively preserved predecessor invariant. The new
    LCSF3 and MF constructions are additional compatible compositions of these
    already introduced ideas.

These axes explain why there can be hundreds of graph-distinct tables but far
fewer independent mathematical ideas. The full 104-row CSV records every named
construction. Its 38 family strings are an editorial grouping, not an invariant
or a new mathematical count.

## The thirteen constructions currently in incoming

| Design | Main change | New proof relation as stated in its report |
|---|---|---|
| PA194ORH | Repaired operand reassociation on AX11H; 134 source addresses move | Exact source/physical relative iPRA equivalence to AX11H |
| PA194OR | Same repaired operand reassociation on primary source | Relative equivalence to primary PA194 |
| PA194AX11HC4 | Four-cycle of physical register positions, six selector rows | Relative full-frame equivalence to revised AX11H |
| PA194C32 | Three-cycle plus two-cycle, seven selector rows | Relative full-frame equivalence to primary source |
| PA194LCSF3 / LCAX11HSF3 | Third guarded return shortcut on LC+SF AX11H | One child step equals three parent steps in the affected context |
| PA194MP / AX11HMP | MP operand-tree reassociation; 87 addresses move | Complete source correspondence and polynomial positive clocks |
| PA194GD_SF | Selector and two shortcuts on GD | Positive local physical simulation |
| PA194GDH_SF | Same physical composition on GDH | Positive local physical simulation |
| PA194GDHS_SF | Same physical composition on GDHS | Positive local physical simulation |
| PA194H5X_MF | Separated marker plus two shortcuts on H5X | Halting witness maps bounded by 5t and 3t |
| PA194JH5X_MF | Same on JH5X | Halting witness maps bounded by 5t and 3t |
| PA194H5XS | Symmetric Shift on H5X | Exact command-store preservation plus physical simulation |
| PA194JH5XS | Symmetric Shift on JH5X | Exact command-store preservation plus physical simulation |

All are complete binary, two-way, single-tape, blank-start tables with 194
working states and a separate halt state, according to their source manifests
and directly checked literal row counts. Their reported absolute iPRA endpoint
inherits the revised AX11H mathematical calibration or, for OR/C32, the older
primary calibration. They do not supply a newly completed Lean endpoint.
The present census verifies graph identities; it does not independently certify
all transitive arithmetic proof translations in those manuscripts.

## Why the existing 193-state objects do not settle the task

There are 61 recognized spanning 193-state action graphs. They include the
well-known runtime193 cores, experimental scanner/operand folds, concrete
rejections, and additional bootstrap variants. Their existence is not evidence
of a valid blank-start PA-consistency machine. The newest packets explicitly
report no accepted sub-194 construction.

Specific useful counterexamples already supplied by the corpus:

- The symmetric witness runtime cores lose the blank initializer. At native
  start74 the standard primary core reaches an outward ray at state35 after92
  transitions. Runtime equivalence on a valid frame is insufficient.
- The ORH operand candidate without its history-selector repair fails the
  universal source-frame contract even though its source and contextual fold
  identities pass.
- A scanner193 candidate cannot distinguish a non-first zero register from
  header padding; its retained literal failure is at source site50.
- The `16_to_38` candidate in the newest LCSF3/MP archive enters an exact
  52-transition cycle from blank after28,217 transitions. That proves this
  particular machine has elementary nonhalting, not the desired consistency
  calibration.
- The latest H5X_MF/JH5X_MF packet records a marker/guard193 counterexample.

No negative bounded search, finite prefix, or source-site checker failure by
itself is a universal impossibility theorem. Exact repeated complete
configurations and verified outward rays are stronger, but concern their
specific tested machines and starts.

## Offline reproduction

From this extracted package, run `python3 -B verify_all.py --quick` or `python3 -B verification/check_novelty.py`. All 550 representative tables needed for the comparison are included under `comparison/`. The original raw corpus is not duplicated.

## Original research-workspace provenance

The following paths and scripts describe the original investigation workspace; they are not claimed to be self-contained package commands.

- `fetch_tables.py` retrieves all tracked .tm files with exact Git blob checks.
- `census.py` computes the corpus and novelty identities using only Python's
  standard library; it uses retained ZIP inputs and the verified local table
  snapshot.
- `build_design_ledger.py` binds all104 named designs to actual recognized
  graph classes, rejects duplicate new classes, and preserves attributed
  mechanism/proof-status metadata.
- `check_nonspanning.py` distinguishes the two194-state disconnected
  diagnostics by an exact isomorphism invariant, with no external package.

The raw input ZIPs are under `incoming_downloads`; extracted current archives
are under `incoming_extracted`; exact downloaded tracked tables are under
`census_work/repo_tables`; older tracked ZIPs are under
`census_work/repo_archives`. New compact delivery artifacts need only include
the generated census ledgers and frontier representatives, not all duplicate
research inputs.
