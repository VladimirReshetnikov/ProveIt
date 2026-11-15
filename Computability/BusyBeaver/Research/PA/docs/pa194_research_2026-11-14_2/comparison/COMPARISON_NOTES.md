# Comparison of the pinned PA consistency-machine designs

## Scope and counts

Snapshot: ProveIt commit `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.
The repository's filed catalog covers 82 packets, 13,006 literal `.tm` occurrences,
and 682 catalog classes. Four current incoming archives were freshly extracted;
their 757 `.tm` occurrences contain 374 distinct labeled tables. They add 22
catalog classes: sixteen at 194 states, two at 201, three at 202, and one at 205.
The combined count is 704 classes, including 110 catalog representatives at 194
states and 53 at 193. These figures include rejected, diagnostic, and auxiliary
material; they are not counts of established consistency machines.

The 110-item frontier contains 56 reported principal constructions, seven
supplementary constructions, 36 research auxiliaries, four research seeds, and
seven rejected/diagnostic constructions. The five new principal graphs are
AX11G, GH, GHS, AX11QH4L, and AX11QH4R. The other eleven new 194-state graphs
are three B/4L/4R composition search inputs and eight screened neutral edits of
GH. Latest incoming AX11H supplies new proof text for two already-filed graphs.

All 94 filed 194-class representatives also occur among the current incoming
literal tables, which made a fresh exact graph comparison possible without
reconstructing every historical packet. The current files include 175 distinct
labeled spanning 194-state tables and two labeled nonspanning diagnostic tables.
The latter have only a three-state maximum reachable component and therefore
share the repository classifier's key with a catalog representative counted at
three states. The 110-item catalog count excludes that extra disconnected table
class. Spanning-root existence is invariant under the cosmetic transformations
used in the novelty audit, so these diagnostics cannot be isomorphic to either
new spanning candidate.

## Files and evidentiary boundaries

`frontier194_ledger.json` and `.csv` give all 110 names, exact source locators,
mechanisms, attributed proof status, and review scope; `FRONTIER194_LEDGER.md`
is the complete readable appendix. `packet_ledger86.json` and `.csv` cover all
82 filed packets and four current incoming archives. `MACHINES.tsv` and
`MACHINE_FILES.tsv` preserve the full filed corpus catalog. The 53 sub-194
frontier classes are separately listed in `frontier193_ledger.json` and `.csv`.

The descriptions and historical status for the filed 94-class frontier and
82-packet ledger were inherited from the AX11G delivery's comparative metadata.
The crosswalk to the pinned repository catalog, every current incoming literal
table, and both new-candidate graph comparisons were freshly computed. Earlier
calibration proofs were not all independently rebuilt. Each ledger row says so.
All source archives and inherited index files have pinned Git blob identities
and SHA-256 digests in `source_identity_manifest.json`; archive/member locators
identify the exact descriptive metadata being attributed.

The literal census recognizes `.tm` files. It does not claim an exhaustive
fresh parser of arbitrary transition tables embedded in JSON or prose. The
known historical JSON-only PA194N-AD candidate is included because the later
frontier exports it as a complete `.tm` table. No additional current incoming
JSON-only principal 194-state design was identified in the report-family review.
This distinction should remain explicit in any comprehensive-comparison claim.

## What actually varies between designs

The large number of names comes mainly from combinations of a small set of
independent ideas. Most preserve the same proof-search scheduler and the same
logical strength.

| Axis | Alternatives and examples | Consequence |
|---|---|---|
| Formula constructor | Coefficient 4, 5, or 6 (M4R, M5, M6, N5/N6, Q5/Q6 and compositions) | Changes arithmetic source and formula coding; requires numerical-calculus recoding. |
| Logical heads | Q exchanges the curried premises of universal distribution; D changes the separate diagonal from Gamma(A) to Gamma(D) | New emitter words with equivalently strong logical rules. |
| MP result | Original dummy-zero push; N visible consequent with no push; C consequent held in cache | Changes stack protocol and the exact proof compiler, including reserved zeros. |
| Shift guard | Original sum guard; H tests only cached h; S uses a symmetric comparison | H changes when a visible contradiction is observed; a final Pop can be necessary where a lone Shift fails. |
| AX arity and stack | Original ten entries and three parameters; AX11 eleven entries and a genuine fourth parameter | New continuation decoding and selector offsets. Treating AX11 as a mere padding change is incorrect. |
| Saved generalization | Original U(d,h); G saves U(c,h), where c is the explicit AX parameter | Removes an offset-setting command from the generalization compiler. |
| Known-zero source returns | A, J, ZR, F, CZ, CSZ and related variants | Replaces jumps by decrements, requiring source invariants and a fresh startup. |
| Physical register placement | AD, TDY, P5, HX and new AX11HR | Changes routing rows and blank startup while preserving the resolved source under a register permutation. |
| Reader grammar and folding | 67 readers/7 folds; 68/8; B history selector; reassociated 4L/4R helper | Changes the decoding implementation and reachable action graph at the same total state count. |

Important aliases prevent overcounting: QN=NQ; repeated QNS and QN6 packets
can be byte-identical; CSZ=X; several C packets share one principal graph;
cache-only HS is also named NS in one filed packet, while the original-sum NS
is a different graph. Latest AX11QH5 is a re-delivery of an existing graph.
The ledger distinguishes named claims from action-graph classes.

## The latest AX11H proof changes the dependency picture

The main PA research README still describes open all-model physical and
arbitrary-PA-proof compiler bridges in the Lean development. Earlier AX11G,
GH, and QH4 packets state relative/conditional consistency results. The latest
incoming AX11H packet is materially newer as a proof document: it claims a
complete written iPRA equivalence for AX11H and QAX11H, while explicitly
not claiming a completed Lean theorem.

The independent inspection recorded in `AX11H_AUDIT.md` read the new physical,
source-command, forward-calibration, term-leaf, Foundation-adapter, and final
composition arguments. No blocking flaw was found. In particular, it checks
model-uniform positive primitive-recursive durations, the exact four-field AX
protocol, quantifier-free bounded all-store compilation, finite-demand trees
instead of an illicit choice principle, the obsolete equality-vacuity repair,
the current/historical Foundation proof-code adapter, and the negative transfer
from the intermediate arithmetic to iPRA. This is a substantive written-proof
audit, not a kernel check or a claim to have re-audited every imported Lean file.
The audit file gives the exact finite suites freshly replayed and their status.

The new AX11QGH construction keeps the numerical calculus unchanged and changes
only its saved generalization command interface. Its source modification is one
CopyD-to-CopyA emitter substitution relative to QAX11H, with its independently
checked source and physical bindings. Its shorter Gen word and the new all-store
compiler compose with the identified written calibration. AX11HR instead keeps
the AX11H source exactly and changes the physical register placement. These are
two distinct kinds of relative construction and should be described as such.

## Sub-194 attempts and what their failures establish

No accepted 193-state blank-start consistency machine was identified. The 53
filed 193-state classes are research candidates, including the familiar runtime
fold and a family of attempted neutral edits/repairs. The runtime fold can have
valid initialized source contracts and still fail the blank-start requirement;
the cited GH study reports an exact outward blank ray from the usual start.
The 194-state rejected scanner and comparator patches likewise demonstrate why
source correctness and startup correctness must be proved separately. The unchanged-tag coefficient-three shortcut has the explicit collision `E(1,0)=6=I(0,1)`; the QH4 report explains how the resulting unchanged-head calculus derives contradiction. This rejects that shortcut, not all possible three-residue encodings.

The incoming GH study reports zero complete-frame hits in its bounded bootstrap
repair searches and no local quotient under several finite-context models. It
also reports a nine-register interference obstruction for one conservative
liveness abstraction. These are useful exclusion results for the stated search
spaces, not lower bounds on arbitrary Turing machines. The ledger does not
promote a bounded failed search into an absolute impossibility claim.

The most promising remaining reductions therefore require a structural change:
a new bootstrap compatible with a 193-state runtime fold, a stronger contextual
invariant enabling a fold not visible to finite-radius screens, a different
representation or semantic register reuse, or a source/compiler redesign with
less arithmetic/decoder overhead. Permuting registers can improve startup and
yield materially different 194-state realizations, but does not by itself remove
a working state. Diophantine and concise-calculus alternatives need a complete
explicit binary-TM state budget before they can compete with the measured 194
frontier; replacing the theorem name alone gives no state-count reduction.
