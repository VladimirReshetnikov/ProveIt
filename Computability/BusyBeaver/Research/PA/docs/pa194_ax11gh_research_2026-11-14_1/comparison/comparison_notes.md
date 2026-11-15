# Comparison at the exact input revision

The input is `VladimirReshetnikov/ProveIt@1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.
There are 82 filed research deliveries and four current incoming ZIPs. The
86-row `packet_ledger.csv` accounts for each delivery; repeated names at a
filed and incoming location are kept separate. In particular the incoming
AX11H archive is a later, materially expanded proof manuscript for tables
already present in the filed collection.

The mechanism-level roster has 63 distinct named principal or supplementary
194-state constructions, grouped into 22 families in `family_matrix.csv`.
These are attributed construction/evidence categories, not 63 freshly checked
consistency theorems. The separate literal census also includes experiments,
failed candidates, scaffolding, and diagnostic tables.

## What the exact census measures

The read-only census obtains bytes from the pinned Git objects rather than
trusting a working directory that may omit large files. It scans the PA tree,
all four incoming archives, and recursively encountered ZIPs. It recognizes
complete numerical five-column binary tables with a unique external terminal,
as well as the documented explicit JSON row arrays, action arrays, numerical
state dictionaries, transition-key dictionaries, row records, and embedded
whole-table strings. It does not execute arbitrary generators or infer a
machine solely from prose, a diagram, or an opaque binary encoding.

The scan recognizes 3,012 table occurrences: 1,563 text occurrences and 1,449
JSON occurrences. They normalize to 804 labeled transition tables. The
194-state frontier contains 110 complete, graph-spanning action-graph classes.
The previously described 94 classes grow by five new named constructions and
eleven auxiliary decoder/neutral-row experiments in the latest incoming
packets. Merely adding the five headline machines would undercount the novelty
comparison. There are also 53 spanning 193-state classes; their status is
rejected or uncalibrated research, not a state-count success.

All 94 of the official catalogue's 194-state classes are matched. The 19
official classes outside this recognizer's single-terminal convention are
explicitly accounted for: 17 have multiple external terminal labels and two
have no external terminal. They are small diagnostics or multi-exit fixed
engine fragments; the two no-terminal controls each have four working labels.
The exact paths, physical counts, maximal reachable counts, and external labels
are recorded in `census/excluded_official.json`. There is no missing official
194-state consistency construction hidden among these exclusions.

Across all sizes, there are 680 complete spanning classes and five additional
maximum-component classes of nonspanning diagnostics. The word “class” in the
raw official-compatible classification is weaker for a nonspanning table,
because distinct disconnected whole tables may share their maximal component.
The report therefore uses the unambiguous 110 spanning classes for its
194-state novelty statement.

The repository's official catalogue uses a maximum reachable component for
nonspanning diagnostic tables. Its “states” count is therefore not always
the number of working labels in a physical file. The current novelty check
uses every complete spanning 194-state table and separately excludes
nonspanning diagnostics by reachability. It does not treat a small diagnostic
component as a small consistency machine.

State zero is not automatically the intended blank start in all presentations.
Some native-numbered tables are accompanied by a separate start/label map, and
the HAZ packet contains dense renumberings whose state zero is not the intended
start. The inventory preserves this distinction. For 30 representatives whose
initial metadata said “unspecified,” an exact rooted graph isomorphism to the
principal retained dense presentation resolves their native start as 74. The
full graph comparison deliberately forgets the start, which makes structural
novelty stronger; a machine theorem still uses its expressly prescribed start.

## The main mathematical and operational axes

All frontier designs remain close relatives of the same unary register engine
and finite proof-command architecture. Most share the original budget
`134 fixed controls + 67 axiom-reader controls - 7 contextual folds = 194`.
The alternative 68-reader/eight-fold layout has the same total. A reduction in
primitive source instructions is therefore not automatically a reduction in
physical TM states.

Formula coefficients four, five, and six are a real change to numerical syntax.
Their use requires hereditary recoding and proof translation, including the
exceptional implication code zero. The Q family changes the order of the two
curried premises in the universal-distribution head. The D family changes
the separate diagonal from `Gamma(A)` to `Gamma(D)`. These transformations act
on emitted formulas and proof selectors; graph novelty alone cannot justify
them.

The original successful MP returns its consequent in the visible top while
pushing a dummy zero. N removes that push and retains the consequent and offset.
C instead returns the consequent in the cache and clears the top. Their proof
compilers have different stack obligations. The no-push compiler reserves an
appropriate zero before deriving MP premises; it must preserve arbitrary
underlying stores and account for Cantor's `[0;0]=0` alias.

The original Shift guard tests `t+h=1`. H tests only `h=1`. This changes the
command language: a plain Shift no longer detects a contradiction in visible
top with zero cache. A valid H compiler must finish with the appropriate Pop
word. Symmetric-comparator implementations reverse the two destructive
comparison operands, eliminating a restoration loop while preserving either
chosen guard. The sum-guard machine named NS in `PA194NS_research` is different
from the cache-only machine named NS in another packet.

The original AX interface saves ten stack entries, including the old visible
top. AX11 pushes its guard too, then falls through the complete MP operand
reader. Consequently it has eleven entries and four encoded operands; the
fourth operand is not optional. The G family independently changes the saved
generalization from `U(d,h)` to `U(c,h)`, making the first explicit AX operand
the binder and avoiding a separate offset-setting command when compiling
generalization.

Several families change only source returns, physical positions, or decoder
structure. Known-zero decrements require source invariants and a separate blank
startup check. Register permutations change recurring physical accesses while
preserving logical commands. Dedicated history selectors and four-increment
reassociations change the decoder's control topology. These are useful distinct
physical realizations, but are not new consistency theories.

## The missing combination used in the new construction

Before the new work, AX11G combines an explicit binder with an eleven-entry,
four-operand AX command but retains the sum-one guard. GH and GHS combine the
explicit binder with a cache-only guard but retain the ten-entry AX command.
The older AX11H/AX11QH interfaces use the carried offset as the generalized
formula's binder. Thus combining explicit binding, AX11, and the cache-only
guard changes a recurring command interface that was absent from the complete
named roster and all 110 concrete prior graphs.

This is a new composition of credited mechanisms. The individual G, AX11, H,
Q, no-push, symmetric-comparison, and decoder ideas are not new discoveries of
this investigation. The claimed advance is the exact new source protocol,
literal implementation, adjusted proof compiler, and replayable preservation
certificate. The strengthened finite-context shortcuts in the accelerated
physical versions are separate from that command-level composition.

## Exact novelty certificate

For a working control q define its structural profile to be the triple:

1. its indegree from working-control transition rows;
2. the number of its two transitions returning to q;
3. whether its two read-symbol transitions have the same successor.

The multiset of these triples is invariant under state renaming, change of
designated start, left/right reflection, global bit exchange, and any changes
to the write/move decoration of terminal transitions. The two unaccelerated
new tables have profile multisets different from every one of the 110 prior
classes and different from each other. This is an exact finite certificate;
it does not rely on a hash collision assumption. The general verifier also
contains a full rooted-tuple fallback for a reference sharing the invariant.
The complete four-table receipt records the corresponding result for the
accelerated implementations. All four are absent from the prior frontier. An
unaccelerated table and its own accelerated version share this profile, so the
verifier also compares exact canonical tuples over all 194 roots and four
symmetries (776 cases) to distinguish that pair. These are two new source
designs with two physical realizations each, not four new mathematical
families.

## Duplicate names and deliveries

Five headline C deliveries have the same transition graph. QN and NQ are the
same construction. The two QNS deliveries agree, and the standalone and paired
QN6 deliveries agree. CSZ and X name the same table. HS is the same table as
the cache-only NS mentioned above; the sum-guard NS is distinct. The incoming
AX11H and QAX11H tables repeat the filed AX11H and AX11QH tables byte for byte.
AX11QH5 also appears in more than one delivered report. Counting archive titles
as distinct machine designs would therefore substantially overcount.

## Why the previous sub-194 objects do not settle the task

The coefficient-three shortcut is a logically rejected numerical calculus:
an equality/implication collision leads to a supplied primitive derivation of
the designated contradiction. The all-offset extension rules out the specified
family of equality offsets while retaining the other heads. It does not rule
out all radix-three languages or all smaller machines.

The 193-state runtime core is a different issue. Its clean-frame source
contracts are available, but its tested blank initialization does not establish
the proof-search computation. The known unchanged starts enter outward rays,
and broad repair searches have not supplied a validated startup. A runtime
core with a nonblank required frame is not a 193-state blank-start result.

The exact selector obstruction also has a restricted scope: for a fixed raw
201-control parent, fresh direct selectors and disjoint reader folds cannot
save more than seven net controls under that model. It excludes neither
overlapping folds nor altered grammars, longer local simulations, different
initialization, or a different register engine. No global lower bound of 194
follows from that certificate or from the accumulated unsuccessful searches.

## Arithmetic proof status

The main PA README states that the primary literal-machine iPRA calibration
remains open in the formal development. Most historical packets give ordinary
PA proofs or relative iPRA preservation arguments. A standard finite-run Lean
simulation is not automatically a model-uniform weak-arithmetic theorem.

There is a material update in the latest input: the incoming AX11H archive
supplies an expanded written mathematical claim of the full iPRA equivalence
for its two existing tables. It has separate physical/source, source/command,
numerical-proof, Foundation-adapter, and I-Sigma-1 transfer arguments. It
explicitly does not provide a new end-to-end Lean build or an executable full
PA-proof compiler. This stronger manuscript must be reviewed on its mathematics;
the earlier filed README's relative-only status does not refute it, while the
mere presence of the manuscript does not turn its claims into kernel results.
The final report should name precisely which of its written calibration lemmas
are inherited by the new construction.

## Attribution and replay

The literal/JSON recognizers are reused from the attributed q-radix research
packet. The official table classifier is reused from the repository. The
historical mechanism descriptions are adapted from the GH comparison and
checked against the packet READMEs; this investigation adds the current four
incoming deliveries, reconciles current bytes, and verifies the new graphs.
Original James Chang, ProveIt, and Wade notices are retained in `licenses/`.

`census_git.py /path/to/ProveIt <pinned-commit>` reruns the byte-level census.
`novelty_pair.py <candidate tables...> --manifest <manifest.json>` replays the
offline frontier comparison. The manifest includes normalized checksums and
all 110 table representatives; the latter command falls back to files beside
the manifest if historical absolute paths are unavailable.
