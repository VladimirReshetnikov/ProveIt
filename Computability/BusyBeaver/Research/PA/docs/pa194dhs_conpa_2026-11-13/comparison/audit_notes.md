# PA-machine inventory and comparison

Snapshot: `VladimirReshetnikov/ProveIt@3cc7fbf75ba111a0da696ef2f6001dd528891bd5`.
This note describes the exact current checkout, not a cumulative count of all
files that used to be in `docs/incoming`.

## Complete inventory and meaning of the counts

There are 47 filed research packets under
`Computability/BusyBeaver/Research/PA/docs` and four current incoming ZIPs:
**51 deliveries**. The new `packet_ledger.csv` records every delivery and its
reported contribution. The 47 filed packets include comparative and failed
research as well as proposed constructions.

The fresh literal scanner covers complete numeric five-column binary L/R
tables in `.tm`, `.txt`, `.tsv`, `.csv` and recursive ZIP members. Identical ZIP
payloads are visited once. It recognizes 1,811 table occurrences, 683 byte
forms, and 487 full transition-graph classes with a spanning root. Two
disconnected synthetic byte forms are kept separate. It does not extract
machines represented only by arbitrary JSON, program source or prose.

The graph comparison tries every root that reaches the complete graph. It
compares full canonical tuples. At 194 working states there are **34 classes**;
reflection and simultaneous read/write-bit interchange merge no further
classes. This is a deliberately stronger comparison than preserving the
specified blank/start convention. It is a finite graph-identity result, not
a semantic equivalence theorem or state lower bound.

The repository's historical `docs/MACHINES.md` instead counts 3,803 delivered
`.tm` files before filing/deduplication, 668 byte forms, 439 rooted classes and
42 unrooted classes. Its 30 classes of size 194 comprise 22 rooted and eight
unrooted classes. Its files are not counts of verified PA consistency
machines. After filing, duplicate machine files were removed and indexed in
`OMITTED.tsv`, which explains the smaller current occurrence count. Current
incoming material contributes four additional 194-state classes.

The 34-class annotated ledger has 21 reported constructions, nine auxiliary
or incompletely validated designs, and four explicitly rejected designs.
The classification describes the supplied evidence. The census did not
rerun every historical universal verifier or reprove every logical theorem.

## Exact duplicate findings

1. **PA194HS = PA194NS** byte for byte, despite distinct current incoming
   packets and names. Both dense files have SHA-256
   `19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1`.
2. **PA194N6** in `pa194n5_n6_conpa_2026-11-13.zip` equals PA194N6 in
   `pa194n6_research_2026-11-13.zip` byte for byte; dense SHA-256
   `36da42a81d605ccb8b5edae197c7cde311447bd95b9bf1ab771a3e726a41c6f4`.
3. Five principal PA194C packets repeat the same machine; dense SHA-256
   `d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b`.
4. **PA194X = PA194CSZ**, dense SHA-256
   `62e93098caf7c09ff2938d07064f0dbbb47c71ec369892968258fff708592269`.

The four additional current 194-state classes are PA194H, PA194HS/NS,
PA194N5 and PA194N6.

## Main construction families

| Family | Mathematical or implementation change | Consequence |
|---|---|---|
| U208 / U209 ancestry | Conditional tape context, entry context, three-cell and history-sensitive folds of the older unary-power-covering development | Multiple proofs and numberings often describe the same two main U208 graphs; no accepted U207 follows from those reports |
| Upstream PA196 | Numerical PA calculus and register/source compiler | Reusable source/physical framework; the pinned repository describes a formally established implication from literal nonhalting to PA consistency, not the full desired biconditional |
| 196-state source studies | Rebracketing, head permutations, separate or bundled diagonal heads, MP/cache controllers, known-zero decrements, integrated gates | Source size and physical state count frequently move in opposite directions; some strong source reductions compile to 197--206 states |
| Original PA195 | Bundled 191-token diagonal emitter; 134 fixed controls + 68 readers - seven folds | 3,700 primitive sites; detailed inherited ordinary PA calibration |
| PA195S / PA195C | Separate 190-token diagonal head; 67 readers and six folds; optional cached controller | PA195S source has 3,673 sites, PA195C 3,649 |
| PA195DC | Bundled diagonal emitter plus Combined/cached controller | 3,676 source sites; 195 controls |
| M195S8 | Eight folds with an added scanner state | 195 is valid; deleting the scanner compensation yields a rejected 194-state table |
| Primary PA194 | Separate head with 67 readers and seven folds | `134+67-7=194`; same resolved source as 195S |
| PA194 68/8 | Alternate association with 68 readers/eight folds | Different 194 graph, same separate-head source |
| PA194-AD | Physical A/D register exchange | Different control graph and startup, unchanged logical source |
| PA194C | MP result stays in cache H; Shift tests H=1 | Six native-row changes; same resolved source as 195C |
| PA194CS | Use destructive comparator symmetry to compare `(1,h)` instead of `(h,1)` | Three fewer source sites; extra reader offset by controller fold |
| PA194CZ, CSZ/X, A, F, J, ZR | Replace source jumps by decrements of registers proved zero; vary entry, final emitter, comparator returns | Useful invariant-guided physical changes; exact blank initialization remains an independent obligation |
| PA194R | Reassociate 44 of 67 reader subtree types plus final known-zero decrement | 1,111 source addresses change, resolved instruction graph remains that of PA194F |
| PA194D | Separate diagonal head changes from Gamma(A) to Gamma(D) | Revised proof selector; 69 readers/nine folds; source-calculus change, not a global parameter permutation |
| PA194Q | Exchange curried quantifier-distribution premises | 79 primitive instructions change; K/S proof translation preserves calculus |
| M4R, M5, M6 | Reassociated decoder; formula constructor coefficients 4,5,6 | M5/M6 require explicit proof and variable recoding, including unused residues and non-order-preserving recoding |
| PA194N | Successful MP retains consequent in visible top and omits dummy-zero push | Changes source/stack interface, not just timing; original Shift condition remains t+h=1 |
| PA194N5, PA194N6 | No-push MP composed with coefficient 5 or 6 | Two 194-state source/calculus compositions; N6 has two separate packet deliveries |
| PA194H, PA194HS/NS | No-push MP composed with cached-head-only Shift; HS/NS also uses symmetric comparison | New proof-word compiler is necessary because Shift can discard a contradictory visible top |

## Rejected frontier and transferable lessons

Three distinct known-zero comparator-return variants have freshly reproduced
blank halts at exactly **1,361 transitions**, with native initial state 74,
terminal 254, final head 1, and 14 one-cells. See
`rejected_startup_recheck.json`. Their source-invariant arguments do not
protect the bootstrapping phase, which reuses the same physical controls.

The fourth rejected 194 class is the seven-zero address scanner. It has
valid local fold cases and a complete source CFG, but fails the old scanner's
physical source contract. A plausible state-count formula is insufficient.

Other notable negative results include a 195-state warm-start machine trapped
in a four-step cycle; 196-state Shift variants halting after 43,563 steps;
and a top-only Shift/no-push composition in the latest NS packet whose
verified implementation costs 195 states. None proves a global lower bound.

## Proof status

The user asks for **PA-provability**. The packet-level ordinary mathematical
PA proofs must be assessed on their arguments; absence of an end-to-end Lean
or Rocq theorem does not itself refute them. Conversely, successful symbolic
execution, finite initialization, or a conditional iPRA endpoint does not
establish the logical calibration by itself.

The repository's top-level PA README expressly says neither machine-specific
direction of its desired **iPRA** equivalence has been established for the
primary PA194, original PA195 or PA196. Its new Lean source/clock/scheduler
bridges are reusable implementation ingredients, not a completed arithmetic
consistency theorem. The 194-state research packets generally retain the
original PA195 numerical-calculus calibration as an ordinary mathematical
dependency and add exact source, command, decoder and literal-tape arguments.

## Files and reproduction

- `census.py`: current-checkout literal-table scanner.
- `census.json`: complete recognized table locators and graph classes.
- `packet_ledger.csv` / `.json`: all 51 current deliveries.
- `frontier194_annotated.csv` / `.json`: all 34 frontier graph classes and
  semantic/evidence annotations.
- `frontier_tables/`: exact representative bytes for each frontier class.
- `compare_candidate.py NEW.tm`: standalone exact cosmetic-equivalence
  comparison against all 34 frontier representatives; tests full tuples,
  not hash equality. A negative control using NS correctly matches HS/NS.

No repository content was edited, no historical proof was silently promoted
to a stronger evidence level, and no new state lower bound is claimed.
