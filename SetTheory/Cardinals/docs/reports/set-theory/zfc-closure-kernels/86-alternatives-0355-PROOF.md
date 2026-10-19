# Exact-step guarded component packing

## Result and scope

Two emitted multi-entry libraries preserve their source component contracts:

- Retained query133 + native edge68 + writer11 + comparator29: 241 original
  working roles become **216 working states**, 432 rows, and five distinct
  external return ports.
- Omitting comparator29: 212 roles become **187 working states**, 374 rows,
  and three distinct external return ports.

All original nonhalting failure states remain distinct singleton classes and
are counted. These are actual finite binary transition tables. They have no
single blank-tape entry, no global halt, and no implemented caller connecting
the external ports. They therefore give no complete consistency-machine bound.

The standalone native edge quotient has **62 states** instead of68, with all
136 original rows preserved after projection. This latter claim holds on
arbitrary tapes and heads, independently of any read guard.

## Generalized guarded-congruence theorem

Let Q be a finite disjoint union of component working-state sets, and P a set
of pairwise distinct external ports disjoint from Q. Each original transition
has the form delta(q,b)=(w,d,t), with t in Q union P. Component entries form a
specified set of entry configurations. Their ordinary inductive contract
proofs give allowed-read sets A(q), and establish that every original execution
from any permitted entry reads a symbol in A(q) whenever its state is q.

Let pi map Q onto quotient working classes, map each port to a distinct new
port, and never identify a working state with a port. Require that, for each
quotient class C and bit b, all original states q in C with b in A(q) have the
same triple (w,d,pi(t)). Set the quotient row on (C,b) to that triple. If there
is no admitted original row, any totalizing row may be used. All initial
entries and every transition target are projected by pi.

Then, until the same external port is reached, at every step n the quotient
configuration is exactly (pi(q_n),h_n,tape_n). For continued nonterminal
executions, including a nonhalting failure sink, this identity holds for all n.

Proof is induction on n. The entry correspondence proves the base case. The
source invariant supplies b in A(q_n). The finite row-congruence condition
therefore gives exactly the same write and move as the source, and the next
state is its projected next state. Tape and head equality are maintained. No
new guard assumption about the quotient itself is needed: the induction
constructs its entire execution from the original one. Port separation gives
both directions of the matching terminal-port claim.

This includes complementary-symbol packing as the special case of two
members with disjoint read domains. It also permits three-member classes,
compatible same-symbol rows, and target-congruence closures. There is no
restriction on incoming-edge patterns. The mathematical justification is the
checked row condition, not the search heuristic that discovered pi.

## Ordinary proof basis for read guards

The recorded guards are not inferred from finite trace coverage:

1. The retained query's reverse-copy induction establishes its two marked-zero
   roles and four forced-one roles for fields of lengths3/4 and a length5
   sentinel. Four rule bits precede an exact complete leaf path. Rules are
   restricted to3..11. This makes selector states124 and128 forced one and
   state123 forced zero. Prefix000 is proved unreachable from the documented entries using the admitted-row graph, so its domain is empty.
2. The mirrored oracle consumes exactly that leaf path. The caller must reserve
   original-frontier cells c-1,c-2,c-3 as zero. The reverse copier never reads or
   writes these cells. The11 leaf emitters consume them monotonically, proving
   their forced-zero guards. Arbitrary exterior tape is allowed beyond those
   three explicitly reserved cells.
3. The native edge's copy, tag-check and locator inductions establish four
   forced-one and eight forced-zero roles, including mismatch executions. Its
   actual reject state conservatively retains both symbols. The entry requires
   a valid finite three-field arena, in-range references, zero immediately
   left of the counter, enough gap, and a valid seven-cell mode header.
4. The writer contract has exactly16 combinations of old/new header mode and
   reads only the seven header cells. Exhaustive symbolic replay of those16
   complete cases, or its three-case ordinary proof, establishes four
   forced-one states for arbitrary exterior tape.
5. The comparator's source-marker and counter induction proves seven
   forced-zero roles. Its contract requires a loaded counter gap of at least
   two and keeps EQ and NEQ separate. This216-state artifact does not assume
   the stronger three-cell gap of the optional smaller comparator.

The independent guard reviews are in ../../verification:
retained_template_query_133_guards_reviewed.json,
encoded_native_edge_68_guards_reviewed.json,
anchor_mode_writer_independent_audit.json, and
compare_biased_counter_29_guards_reviewed.json.
Component source/table hashes are recorded in provenance.json.

## Six unconditional native folds

These old-native state classes have exactly matching full binary rows after
all targets are projected:

- {23,25}: copier after_anchor and find_ones;
- {34,36}: locator anchor_advance and ones_advance;
- {38,50}: locator skip_left and reset_anchor;
- {39,51}: locator skip_right and reset_filler;
- {40,52}: locator mark_next and reset_mark;
- {45,47}: locator anchor_done and ones_done.

The last three reset states form a chain which shares the locator's existing
field-skipping chain. All other states, the return port, and reject54 remain
separate. Structural verification of all136 rows proves an unconditional
literal-step bisimulation, not merely valid-frame equivalence.

## Certificates and testing

Each manifest contains the complete source-to-quotient projection, every class,
entries, distinct ports, guard domains, state roles and a full state ledger.
row_projection_certificate.json records every mathematically admitted original
row. rebuild_certificate.py independently reconstructs the quotient rows from
the original tables and saved partition, verifies all admitted rows and all
protected ports/failure states, and reproduces the exact table hash without
rerunning the heuristic search.

The216-state library additionally passes5,224 whole-component calls and
2,269,330 literal step comparisons. The187-state library passes3,280 calls and
1,965,106 comparisons. They include all152 oracle leaf paths, all16 writer
mode cases with exterior variation, native successes and mismatches at minimum
gap, and all three comparator outcomes. These tests supplement the ordinary
proofs and finite structural certificate; they do not replace unbounded guard
or component semantics.

## Unlinked obligations

Every library port remains unlinked. A caller must produce validated prepared
frames, position the head, choose the writer entry, preserve the query path,
connect repeated edge traversals, handle logical leaves and both freshness
gates, implement arena/proof enumeration and validation, distinguish ordinary
rejection from invariant failure, and bootstrap all tape contents from blank.
The no-comparator library still uses the native edge's original three-field
records. It does not implement proposed per-record saturation flag suffixes;
those change the scanning invariant and require new transitions and proof.

All these are missing machine-construction obligations, not free operations.
The result is a rigorously packed component library, not a sub246 consistency
machine or a proof that a complete implementation will fit the remaining count.

## Separately certified unreachable selector role

The final libraries additionally remove the singleton role query127, the
selector prefix000. Before changing its domain, a complete finite reachability
calculation traverses every admitted row from every documented component entry.
It does not reach query127. Exhaustive incoming-edge inspection finds exactly
query124/read0, which is forbidden by the independently proved forced-one guard
for query124. Thus no original permitted execution enters query127. Its allowed
read domain may be empty, and it may be absorbed into query121 without imposing
any row obligations. The finite reachability certificate is saved separately.

This does not delete or share any failure state. The216/187-state witnesses are
obtained from the retained217/188-state witnesses by precisely this one dead
role identification. Future callers may enter only the documented component
entry states; a new internal entry at query127 invalidates this reduction.

## Independent audit status

The independent verifier reconstructed the source tables and reviewer read
maps without relying on the producer's guard declarations, verified every
projected row and both state-count controls, and recomputed the exact admitted
reachability certificate for the final216/187 delta. It also checked all full
binary rows for the native62 quotient. Results are recorded in
../../verification/packed_libraries_independent_audit.json; no defect was found.
This is an independent computational certificate audit supported by ordinary
component proofs, not a proof-assistant kernel theorem for a complete machine.
