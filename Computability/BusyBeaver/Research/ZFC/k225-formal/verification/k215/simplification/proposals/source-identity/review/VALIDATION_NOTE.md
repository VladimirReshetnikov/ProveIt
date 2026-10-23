# Independent mathematical validation

Review pin: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

These are simplification proposals, not newly compiled proofs. The supplied independent
checker reads saved source as inert text, implements its own parsers, and does not import
either proposal audit. No upstream generator, Lean/Rocq compiler, or proof checker was run.
Source identity is checked against the supplied pinned-source receipts; this is distinct
from a fresh proof-assistant build.

## 1. AX inference: logically conservative, conditional on rechecking

The soundness argument is valid without a theorem about the extractor. The preserved
theorem `axWordRun` has the shape

`axWordCheck n word = true -> Clean st -> Rn (.node n) st (axWordEval word st)`.

It applies to every word, irrespective of how that word was produced. Thus a newly
kernel-checked `axWord_checked` supplies the entire source-binding obligation. The
extractor is merely a candidate producer. Its partial decoder, fuel bound and `getD []`
do not become trusted semantic assumptions. In particular, failure produces the empty
word, which the old checker rejects at start node 236 because 236 is not terminal 457.
Retaining the old theorem's *text* is not enough: its proof must elaborate again with
the changed definition, as must `ax_eval` and all affected endpoints.

Independent full-row parsing, including primitive overrides, recovers both 156-atom
words exactly. They differ only at positions 7 and 8: Dom has `readp1, cons`, whereas
Perm has `cons, readp1`. The audit verifies every edit is exactly the added import,
13-atom decoder and computed-word definition. All checker, run, effect and downstream
semantic proof text is unchanged. Negative controls cover insufficient fuel, a cycle,
an unknown macro, a non-node override, comments, malformed constructors and duplicate
rows. The original proposal audit now also handles non-node overrides.

The exact textual accounting is 13,039 bytes before, 11,520 bytes in the two edited
modules, plus the 732-byte helper: **787 bytes saved**. Source lines instead increase
from 310 to 316. This is removal of maintained literal data, not a demonstrated reduction
in kernel proof size, checking time, or every measure of source length.

Static Lean review found no definite typing defect in the fuel recursion, Nat decoder,
namespace use or default. The unchanged `simp only` proof of `ax_eval` now relies on
reduction through the extractor and list search. Elaboration, reduction limits and cost
remain acceptance tests, not established facts.

## 2. Decoder: a representation deletion, not a new execution proof

Independent parsing confirms 202 source nodes comprise 179 forks and 23 primitive
labels. The j-th fork maps to actual program node j, with all 179 adjacency squares
commuting and root 201 mapping to 178. The proposed role array changes only these
source labels and removes primitive IDs: physical actions, states, suffixes, internal
role indices and block references are retained exactly. Counts remain 234 roles,
281 blocks and 468 branches, of which 371 are internal and 97 primitive. The roles must
not be collapsed to 179: a source node alone does not identify the required suffix.

The independent finite audit reproduces 4,751 leaf walks, the specified unread-suffix
and trailing-zero tests, and the count 6,176 obtained by splitting decrement leaves
into two outcomes. **The last number is a count, not 6,176 checked guard or runtime proofs.**
Finite suffix tests are not a quantified theorem about all bit lists.

The pilot terminal check establishes only that the source edge is non-internal and
the current physical transition equals the stored action. It does not establish that
this action implements that source opcode. Indeed, changing a source `.inc r` edge
to `.decnz r` leaves that terminal check unchanged. This is appropriate for a theorem
ending *before* primitive execution, provided the routed-entry witness retains the
exact source edge and existing primitive residual/return contracts are subsequently
applied. It would be unsound to use this check alone as a full simulator certificate.

The needed generic theorem must follow the successful `RegisterPath.walk` equation,
preserve the arbitrary tape and entire consumed path, respect implicit zero extension,
and yield the exact terminal source edge and physical port. Its induction and endpoint
adapters are not supplied by the finite mapping. The existing `source_tree_eq` was
already a kernel-checked bridge; replacing it reduces representation overhead rather
than repairing a trust gap. Keep the old bridge until the replacement and its callers
compile. The pilot still imports the old data module, so no dependency-closure or net-byte
reduction has yet been demonstrated.
This is a decoder-prefix component migration: the current `KSim`/`checkEdge` route and
all 105 site blocks remain unchanged. It does not by itself shorten that production
endpoint dependency closure.

## 3. Rocq loop reuse: small and well targeted

For `z465`, the existing `sem_while` theorem is instantiated with register 5,
body `EContinue 1`, identity body transformer and final state `set m 5 0`.
The six obligations are precisely the literal row, register bound, continue rule,
identity preservation, zero-field identity and repeated-update identity. They match
the maintained `w199` application because rows 199 and 465 are identical. No theorem
at node 199 is incorrectly applied directly at node 465.

Discarding the initial equation `get m 5 = a` is legitimate: the generic theorem works
for every state. Keeping that premise in the public statement preserves clients.
Independent textual comparison confirms the same statement and a change from 9 lines /
475 bytes to 5 lines / 171 bytes. These are per-declaration counts, not multiplied
production savings. The producer patch and regenerated consumers still need a build.

The older 89-node transport is not a new result: archived component-checked prototypes
already exist. Their reported checks should be attributed to those artifacts, not to
this review. Shared-state/interface and maintained producer/endpoint integration remain
real work and cannot be erased by a nominally similar wrapper type.

## 4. Shared subtype interpretation: sound abstraction, integration unproved

The proposed generic interpretation has the correct binding obligations:
`slot (next c) 0 = 0`,
`slot (next c) (i+1) = slot c i + 1`, stability of the environment invariant,
and exact interpretation of the guard in the *post-push* environment. A structural
induction gives the advertised satisfaction equivalence. Quantifier witnesses are
constructed from the guard proof, so neither choice nor an inhabited subtype is needed.
Subtype equality follows from equality of values.

For the tagged adapter the marker at position d shifts to d+1; for the well-founded
adapter the slot map is identity and context is `Unit`. These are mathematical special
cases of the generic theorem, subject to the exact syntactic adapter equalities and
existing theorem interfaces being compiled. No claim is made for the distinct named-
variable Constructible interpretation or for a new ProfileComposition theorem.
The draft adds an abstraction and comparison clients; without deleting/replacing the
old proofs and rebuilding their clients, it does not establish net source savings.

## Acceptance decision

The three concrete source-level opportunities are credible, with Rocq `z465` the
smallest-risk patch and the decoder change the largest structural simplification.
The common-subtype theorem is a plausible additional consolidation. None should be
reported as integrated or formally verified in this packet. Adoption requires the pinned
toolchains, exact public-endpoint comparison, printed assumptions, retained machine tables,
producer consistency, and separately measured source/proof-object/build-time deltas.

Reproduce the independent data results with
`python -I -B review/independent_data_check.py` from the packet root.
The receipt is `review/INDEPENDENT_DATA_CHECK.json`.

## Scope of the AX size comparison

The 787-byte saving shares the new helper across both Perm and Dom modules. For the K215 Perm lane alone the reduction is only 27 bytes after counting the entire 732-byte helper, and it adds a module. The generator template also remains to be updated and compiled. This is a representation-maintenance pilot, not a large demonstrated K215 endpoint reduction.
