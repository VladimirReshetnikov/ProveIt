# PA machine comparison at the pinned snapshot

Snapshot: `VladimirReshetnikov/ProveIt`, commit
`e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f`.

## Scope and evidence

The integrated PA documentation contains 93 delivered research packets. Five
additional current incoming archives supply eleven named principal 194-state
constructions, along with many further auxiliary/rejected/search tables. The
named ledger has 85 distinct table classes: 74 historical principal or
supplementary named constructions and the eleven current principal additions.
Each of those table identities has been freshly bound to literal bytes at the
pinned snapshot or a named member of a pinned ZIP. The mechanism descriptions
and inherited proof-status statements are attributed to the packets; this is
not an independent reconstruction of 85 PA calibrations.

The fresh census is broader than the named ledger. It scans pinned tracked
`.tm`, `.txt`, `.csv`, `.tsv`, `.json` and `.zip` payloads under PA and
`docs/incoming`, with recursive ZIP inspection and explicit JSON matrix
recognition. It checks every selected tracked file against its Git blob
identity. It does not execute arbitrary source generators, reconstruct tables
printed only in prose, or infer the semantics of arbitrary JSON. Its complete
scope and final counts are in `summary.json`: 522 spanning 194-state action
classes, 55 spanning 193-state research classes, and two nonspanning
194-control encodings. The two latter encodings share one start-free table
class. All 139 historical 194-state classes are recovered.

Table classes forget the designated start when deciding whether tables differ
only by state renaming; named machine starts are retained separately. Some
native presentations do not declare their start, and some historical densely
numbered tables use a nonzero start. Consequently a start-free class count is
not a count of blank-input behaviors. The additional cosmetic comparison also
allows tape reflection, global symbol exchange and erased terminal-entry
write/move actions. Symbol exchange is used only to strengthen the novelty
screen; it does not preserve the all-zero initial tape without also changing
the blank convention.

## What the many named designs actually change

The packet names describe combinations of a modest number of largely
independent mechanisms. The detailed 26-family inherited ledger is retained
in `inherited_families26.json`; the following grouping explains the important
tradeoffs.

1. **Arithmetic presentation and formula coding.** The radix-four/five/six
   families change the numerical implication constructor and related tags.
   The Q families reverse the two curried premises in the distribution axiom.
   D-family emitters use the adjusted diagonal index instead of the first
   operand. These changes need primitive-recursive proof translations,
   including alias, freshness and diagonal behavior; equal state counts do
   not make them mere state renamings.
2. **The MP store convention.** The original machine pushes a dummy zero
   after successful modus ponens. C caches the consequent and clears the
   visible top. N leaves the consequent visible and omits the dummy push.
   These conventions alter the all-store source compiler. They can be
   combined with different axiom presentations, but source words must be
   rebuilt for the actual convention.
3. **The contradiction detector.** The original detector uses `t+h=1`,
   whereas H checks only `h=1`. S variants reverse the destructive comparison
   operands to eliminate restoration work. The H compiler needs its final
   Pop/detector argument; simply deleting the visible-top test is not by
   itself a sound equivalence proof.
4. **The axiom interface.** AX11 retains every emitted head and the saved
   top, then falls through the complete MP reader. It consumes four operands
   and has an eleven-entry stack interface. A proof written for the earlier
   three-operand, ten-entry interface cannot be reused without this fourth
   operand and all eleven selector positions.
5. **The generalization index.** G uses the explicit AX operand `c` in
   `U(c,h)` instead of an inherited offset. This shortens a command compiler
   and changes its free parameter behavior. GH/GHS combine G with cache-only
   detection; AX11GH/GHS combine all three changes.
6. **Control flow and physical register placement.** A/F/J/ZR/CSZ families
   replace selected returns by decrements of registers known to be zero.
   AD/TDY/P5/HX/HR move logical registers to different physical blocks and
   retarget routing. These are recurrent implementation changes with source
   invariants and whole-frame initialization obligations.
7. **Decoder and return implementations.** B and SEL use finite history to
   redirect recurrent decoder paths. 4L, QH4L/QH4R and LC change associations
   of a constructor loop while preserving the fully resolved source graph.
   F shortcuts replace three physical steps by one under incoming-edge bit
   invariants. Disjoint edited rows do not alone prove that these changes
   compose: an earlier patch can alter the context needed by a later one.

These axes explain why a shorter source word, fewer source sites, fewer raw
reader controls and fewer final binary states are different measurements.
For example a new grammar can reduce one quantity while introducing extra
reader states or losing a simultaneous fold. The delivered 194-state tables
need the complete accounting `fixed controls + readers - compatible folds`.

## The five currently incoming deliveries

| Packet | Named principal tables | Contribution | Status |
|---|---|---|---|
| GD research | GD, GDH, GDHS | Independent explicit generalization binder and adjusted diagonal parameter, with three detector/comparator implementations | Each 194; written inherited calibration and operational certificates; no completed kernel endpoint |
| LCFAST/tagged research | LCAX11GHF, LCAX11GHSF | Loop reassociation composed with two guarded three-to-one shortcuts | Each 194; direct relative iPRA argument; absolute result imports revised AX11H |
| Loop-return research | LCG, LCGS | A third shortcut at native row 190/1, using a unique-incoming-edge left-neighbor invariant | Each 194; positive bounded-time relative transfer; same absolute dependency |
| Comparison/new designs | AX11H_SF, LC_AX11H_SF | Compatible selector plus accelerated return on AX11H and its LC companion | Each 194; direct threefold time bounds relative to the parent; same absolute dependency |
| Witness research | H5X, JH5X | A genuinely different fifth axiom head, optionally coupled to a different first head | Each 194; explicit Hilbert-template translations and physical certificates; same absolute dependency |

The GD source uses `U(c,h)` and `Gamma(d+x)` with independent indices. GD uses
sum detection, GDH cache-only detection, and GDHS the symmetric cached
comparator. Its original distribution head and plain structural returns
are deliberate; it does not silently borrow a conditional zero-return rule.

H5X changes the witness head from `U(D,E(H,D)->1)->1` to
`U(D,E(H,D)->1)->A`, with independent `A`. The old system supplies the new
instances by explosion and `A=1` recovers the old head. JH5X also uses
`(X->H)->H` in place of `(X->1)->H`, for
`X=U(D,U(D,H)->1)`. Its proof of explosion is rebuilt from the new witness
head, diagonal and distribution. This last qualification prevents a circular
argument that would continue to rely on the removed first head.

The LCFAST graphs were already among syntactically eligible patch combinations
in the newest SF archive's search corpus. Their promoted certified status is
valuable, but one should not advertise them as absent from every current
literal table. A new design must be compared with the full current census,
not only the historical 139-class catalog frozen by each incoming author.

## Duplicates and misleading labels

Five historical PA194C packets contain the same principal graph. QN and NQ
name one graph. The earlier HS is the filed NS machine with cache-only guard,
whereas a later NS/SUMS packet also uses those letters for sum-guard variants.
QNS has multiple independent deliveries; QN6 does too. AX11QGH is the same
principal graph as AX11GH, despite the different names. Several current
packets repeat revised AX11H under an old archive filename; the revised
calibration is the integrated directory ending `_2`, not the earlier packet.
The full named ledger retains these alias statements and exact table classes.

The integrated machine catalog's 15,317 table occurrences and 747 classes
are historical archival counts, not a fresh count of the current live tree.
Likewise its 139 194-control classes include research inputs, rejected
experiments and tables without a designated start. None of these counts
means that 139 independent Con(PA) theorems have been proved.

## The 193-state files are not a solution

The supplied corpus contains many syntactically complete 193-state tables.
They are rejected local quotients, diagnostic inputs or runtime-only cores.
The important Runtime193 example can implement register operations from a
specially prepared frame, but the tested blank starts fail to construct that
frame. A two-way binary blank-input machine cannot count a prewritten header
or externally supplied register list as free initialization. The witness
archive additionally checks a shorter-header variant; its specific fixed
splice still halts or reaches certified rays from the tested blank starts.
This is an obstruction to that splice family, not a theorem that every
193-state construction is impossible.

The tagged-three encoding in the LCFAST packet has a sound mathematical
recoding theorem but a 207-state implementation. Its earlier 203 score
counted four folds that were not simultaneously compatible. The tagged-two
prototype has an optimistic 206 score but fails a source contract. Neither
is a smaller accepted consistency machine.

The newest SF packet's 530-table corpus consists of 118 native presentations
from the then-current incoming material and additional syntactically eligible
loop/selector/return compositions. It explicitly withholds blanket
correctness claims for those compositions. Its bounded physical searches
include local quotient, incoming-edge bypass, common-future joins, recursive
folds and neutral-row-plus-fold experiments. Their empty results exclude only
those particular transformation classes, windows and step budgets. They do
not prove a global lower bound of 194 states.

## The exact formal-status boundary

The current PA README states that neither machine-specific direction of the
primary PA194 iPRA equivalence has been completed. There are substantial
checked components: ordinary finite-run source simulation, modeled scheduler
soundness/fairness, arithmetic encodings and all-model pieces of the proof
compiler. The physical-machine bridge over arbitrary model-length executions
and the full internal PA proof compiler are still open in that Lean project.

The later revised AX11H packet claims a complete **written** mathematical
iPRA calibration and includes explicit proof-completion manuscripts. Later
packets rely on that argument. It would therefore be inaccurate either to
call their claimed results completed Lean proofs or to deny that they supply
written absolute proofs. A fresh relative table-equivalence theorem can be
proved independently of the calibration; its Con(PA) corollary then has the
identified written calibration as a dependency. Checking source graphs,
finite symbolic contracts or local patches does not by itself discharge the
inherited arithmetic proof compiler.

## Practical recommendation for the next reduction

For a reduction below 194, the best comparison is against a fully specified
parent table, complete blank initialization and an explicit positive clock
simulation in both directions. The current packets have extensively searched
ordinary one-pair folds of the old parents. New source factorizations,
parameter representations, or whole arithmetic-block algorithms have more
room to change the state accounting. Reusing the small-machine methods from
ZFC should preserve their complete initialization and invariant obligations;
a source-only or runtime-only saving is insufficient.

For a same-size fallback, combining the new GD or witness logical source with
an independently justified physical continuation/return change can produce a
new recurrent implementation. Its novelty must be checked against the fresh
full census, including hundreds of unnamed SF patch combinations. The eleven
new incoming principals all postdate the catalog to which the packets' own
novelty claims were compared.
