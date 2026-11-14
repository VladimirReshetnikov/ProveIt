# Comparison of the pinned PA corpus

## Scope and what the counts mean

The snapshot is `VladimirReshetnikov/ProveIt@317b07268681b44ff352d173a162e2a8c241b2fe`.
There are 51 filed research packets under `Computability/BusyBeaver/Research/PA/docs`
and three later archives under `docs/incoming`: `PA194NS_research.zip`,
`pa194haz_research_2026-11-14.zip`, and `pa194qn_research_2026-11-13.zip`.
The filed README's statement that no archives remain incoming is stale at this
commit; the new ledger includes all 54 deliveries. The imported PA196/PA209
developments and subsequent formalization directories are reviewed separately
from the packet count.

The fresh literal-table scan reads every tracked `.tm`, `.txt`, `.csv`, `.tsv`
and `.zip` file in the PA tree and all three incoming archives, recursively
including nested ZIPs. All 2,431 candidate files in the PA tree were compared
byte-for-byte with their pinned Git blobs. No file is missing, modified, or
excluded by the file enumerator. Identical ZIP payloads are visited once.
The scan recognizes 1,404 complete-table occurrences, 722 byte forms and 17
distinct ZIP payloads. The 194-state subset has 94 byte forms in 39 whole
action-graph classes, allowing all spanning roots, arbitrary state renaming,
global reflection and symbol complementation. These counts include research
seeds and rejected constructions. They are not counts of proven consistency
machines. The lower occurrence count compared with historical reports reflects
the repository's removal of 4,495 duplicated machine-file occurrences while
filing the 51 archives.

The supplied official `MACHINES.tsv` records 34 filed 194-state classes. The
three incoming archives add five literal classes: SUMS, sum-guard NS, HA, HAZ,
and QN. A further explicit auxiliary, N-AD, appears only as a complete table
string in the incoming NS audit JSON. It is included in the extended comparison,
although prior literal-file censuses omit it. The supplemental scan examined
6,735 JSON files, recovered 62 complete embedded table occurrences and found
exactly this one additional 194-state class. The combined frontier therefore
has 40 classes. `json_supplement.json` reports the exact scope. Neither scan claims to
execute arbitrary code or recover every conceivable transition-system encoding.

`packet_ledger.csv` lists all 54 packet contributions. `frontier194_guide.csv`
gives the individual mechanisms and evidence categories of the 40 named/explicit
frontier entries. Their descriptions report the packets' own evidence scope;
they do not present every historical proof as freshly rerun.

## The progression in actual design mechanisms

### The 208-state family

The older U208 packets mostly revisit one physical saving in the U209 register
interpreter: a decoder control can be removed using finite tape context or
incoming history. Three-cell, entry-context, finite-history and conditional-
context arguments often describe the same literal graph. The official
machine census identifies the plain U208 class `735b413e0795` in six named
packets, while `b6396833ab64` is the compatibility presentation. Later audits
and searches below 208 did not establish a smaller machine. Their alternate
allocations and rejected tables explain why the census contains many 207/208
graphs without corresponding accepted consistency theorems.

### The 196-state stage

The imported PA196 program supplies the numerical calculus, primitive-register
language, scheduler, and source-to-tape interfaces reused by subsequent work.
The later packets vary emitter factorization, diagonal-vacuity handling,
axiom-head placement, register allocation, decoder association, command
controller, and zero-valued returns. A source expression with fewer tokens or
primitive sites need not compile to fewer controls: its shared reader-subtree
structure can worsen. The explicit direct-negation experiments illustrate this:
an improved logical/source expression still compiled to 197 or more controls.

The original PA195 report distinguishes 25 supported 196-state classes from
65 other 196-state graphs that then had partial, bounded, or negative evidence.
That is a historical classification, not a current count of newly reverified
machines. The present exact census continues to retain rejected and experimental
graphs in its novelty comparison.

### The 195-state stage

Original PA195 keeps a 191-token bundled-diagonal emitter and its 3,700-site
source graph. Its count is `134 + 68 - 7 = 195`: a different association makes
seven contextual decoder folds simultaneously valid, rather than six.

The distinct PA195S machine uses the 190-token separate-diagonal emitter and
3,673 source sites, with `134 + 67 - 6 = 195`. PA195C uses the same compact
decoder with the cached-result/cached-head controller. PA195DC applies that
controller to the bundled-diagonal emitter. The follow-up M195S8 is a distinct
scanner allocation. The failed 194-state scanner in that follow-up remains
explicitly rejected, despite its small table size.

### The 194-state stage

Primary PA194 combines the separate emitter's 67-reader allocation with seven
compatible folds: `134 + 67 - 7 = 194`. Its A/D companion changes physical
register placement. A second PA194 reaches the same count as `134 + 68 - 8`.
These are genuinely different decoder graphs with the same numerical source
calibration.

The cached family C changes successful modus ponens to return its conclusion
in the cache and makes Shift inspect the cached head. CS shortens this guard
by exchanging the two operands of a destructive equality comparison. On its
nonhalting branch both operands are cleared, so the eliminated restoration
loop is unnecessary. The same principle applied to the original sum guard
produces the later incoming SUMS, which has a different command interface.

The zero-return families CZ, CSZ, F, A, J, R and ZR replace selected unconditional
jumps by decrements of registers known to be zero. Their differences concern
which invariant establishes zero, which source cuts are changed, and which
reader association realizes the modified source. The source proof does not
alone guarantee initialization: a rejected comparator-return modification
passes every source contract yet halts after 1,361 steps from the blank tape.

D changes the separately emitted diagonal head from Gamma(A) to Gamma(D), with
new selectors and a 69-reader/nine-fold decoder. Q exchanges the curried premises
of one quantifier-distribution axiom, changing 79 resolved source instructions;
its proof translates axiom instances through the inherited implication basis.
M5 and M6 change the formula-constructor coefficient and require an explicit
recoding of numerical formulas and variable labels. M4R retains coefficient
four but uses that family's different physical association.

N omits the dummy-zero stack push after successful modus ponens and returns
the visible consequent with its offset retained. Its proof compiler must
reserve and later remove the required zero explicitly. H and HS combine that
visible-top return with cached-head Shift; N5 and N6 combine no-push MP with
the coefficient-five/six formula encodings. Incoming sum-guard NS instead
combines N with SUMS, retaining the original `t+h=1` guard. QN combines N
with Q's premise-exchanged emitter. HA/HAZ combine the pre-existing auxiliary
MPH cached-result interface with A/D placement; HAZ additionally uses a known-
zero final AX decrement.

## Duplicates and naming hazards

Five nominally new PA194C packets deliver the same principal action graph.
PA194X is the previously supplied PA194CSZ. The filed PA194NS equals PA194HS;
both have 3,650 primitive sites and the cached-only guard. The later incoming
PA194NS is different: 3,651 sites and the symmetric original sum guard.
PA194N6 is delivered twice with the same machine. Names alone therefore do
not establish either identity or novelty. The comparison uses complete
transition actions and exact canonical tuples.

## What the new QS/QNS composition adds

The QS/QNS candidates combine the Q premise-exchanged emitter with the
symmetric **original sum guard**, rather than Q's cached-only controller.
QS retains the original successful-MP dummy push; QNS additionally uses
N's no-push return. These compositions were absent from all 39 literal
194-state classes, and neither matches the additional JSON-only N-AD
auxiliary. The extended comparison receipt states the final recoverable-
JSON scope separately. Both candidates also differ from each other.

The mathematical contribution is a compatibility/preservation result among
existing components, not a new calculus. The numerical-calculus/PA calibration
remains an explicitly inherited ordinary mathematical dependency. The changed
guard has an exact all-store argument, including arbitrary incoming scratch:
if `k=x+t+h`, the old comparator receives `(H,X)=(k,1)` and the new receives
`(1,k)`. Both halt exactly for `k=1`; otherwise both leave the same cleared
registers. This supports bidirectional finite-trace transport rather than
reasoning from a long finite simulation.

## Proof status and reduction conclusions

The current PA README explicitly states that neither machine-specific direction
of the desired iPRA consistency equivalence has yet been established for the
primary PA194, original PA195 or PA196. The developed Lean work proves many
source/clock/quotient interfaces in standard finite-run semantics, and parts
of their arithmetic interpretation, but it must not be described as a
completed end-to-end machine-specific consistency theorem.

The packet claims concern ordinary PA-formalizable mathematical proofs. The
new construction inherits the stated calibration and separately establishes
its own command/source/physical preservation. Python certificates are
implementation evidence with an explicit symbolic reasoning base; they are
not newly kernel-checked Lean or Rocq proofs.

The corpus and the new bounded searches do not establish impossibility below
194. Removing more source instructions is insufficient by itself; one must
improve the fixed interpreter or the net decoder budget while preserving
simultaneous folds, exact source jumps, positive progress and blank startup.
Those are the concrete remaining targets, rather than any claimed global
state-count lower bound.
