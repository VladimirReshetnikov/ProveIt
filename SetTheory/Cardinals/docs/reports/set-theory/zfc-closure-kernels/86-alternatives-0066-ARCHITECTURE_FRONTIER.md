# Native-tape architecture frontier

## Result

No complete sub-246-state consistency machine has been produced by this lane.
The executable artifacts below are literal binary one-tape components and a
complete high-level exact proof-search reference. Their prepared frames, return
ports, and unmet caller obligations are explicit. A component library count is
not a count for a complete blank-tape machine.

The most useful closed component is a **133-state retained-path template query**:
it nondestructively copies a unary source path into a reversed binary query,
selects one of the nine trusted templates, and runs the mirrored template oracle.
Its single-entry table preserves the source path. A separate **172-state blank
probe** writes its entire 39-cell frame and halts in 350 steps. That probe always
halts and has no consistency-search claim.

A **68-state single-entry native edge step** reads a mode from a fixed header,
checks the selected constructor bit, copies the selected child reference,
reinstalls the first-record marker, and locates the child. Every reset and head
adapter in that operation is charged. Exact quotient/guarded-packing work is
maintained separately under `../machine_encoding/component_packing/`.

## Trusted logical basis and original complete finite algorithm

`oracle_search.py` retains the exact C254 calculus, both bundle disequality gates,
strict backward arena references, zero normalization, and fixed falsity endpoint.
Its fair finite-word enumeration is inherited from the source codec. Its only
logical change is replacing structural fixed-pattern matching with the oracle
path test. On validated arenas that replacement is extensionally equivalent:
every internal occurrence is visited along both branches among all leaf paths,
so its two tag bits are checked; parameter and zero leaves check exact IDs.
Virtual zero has tag0 and children0,0. Duplicate denotations at different IDs are
permitted in the original protocol; exact repeated-parameter ID matching is
intentional, and interned certificates supply existential completeness.

This is an executable finite-algorithm reference, **not a compiled TM**. It
preserves the source calculus's consistency calibration. Tests include 264
complete controls, 1,056 malformed mutations, and every binary word of length
at most17 (262,143 words). Resource exhaustion is not treated as logical
rejection.

## Artifact ledger

| Artifact | Literal working states | Scope / tests |
|---|---:|---|
| `template_oracle_102.tm` | 102 | 91 shared constructor states +11 leaf emitters; 152 leaves |
| `unary_locator_18.tm` | 18 | Destructive unary-index record locator; 12,016 tests |
| `oracle_locator_pipeline_134.tm` | 134 | Selector, oracle, seek, first lookup; 760 tests |
| `bounded_oracle_locator_135.tm` | 135 | Same plus one output-boundary marker state; 760 tests |
| `tag_edge_16.tm` | 16 | Four-entry tag check and selected-child marker; 10,000 tests |
| `native_edge_step_67.tm` | 67 | Four-entry unbiased reference edge cycle; 12,272 tests |
| `encoded_native_edge_68.tm` | 68 | Single-entry, biased references, fixed mode header; 12,272 tests |
| `reverse_path_copy_19.tm` | 19 | Source-preserving reversed raw query copy; 2,533 tests |
| `retained_template_query_133.tm` | 133 | Copy + mirrored selector + mirrored oracle; 456 tests |
| `blank_retained_query_probe_172.tm` | 172 | All-blank initialization charged; always halts after350 steps |

All halts/returns are separate from these working-state counts. Independent
reviews are under `../verification/`. The final reverse copier and retained
query passed independent universal whole-tape audits and 1,065/1,368 additional
literal tests respectively; the 68-state edge passed 2,112 independent calls,
including 192 successive uses without repairs. Tables are total on binary reads, but
component invariant-failure loops must not be mistaken for fair rejection of a
wrong proof candidate or wrong template instance.

### Current frame conventions

* Native arena record: unary tag length t+1, then unary left/right reference
  fields of lengths L+3 and R+3, each followed by0.
* Record0 may physically be (tag0, child0, child0), representing normalized
  virtual zero. All later canonical records use earlier children and omit that
  duplicate zero constructor.
* Native edge workspace: a counter1 whose immediate left neighbor is0, then
  a sufficiently large blank gap, then a fixed seven-cell mode header
  `1^k 0 1^(5-k) 0`, where k=1+2*branch+expected-bit.
* Exactly one selected record has its first tag1 erased. Successful edge calls
  move only that marker, returning on the erased tag cell. The selected child
  reference r needs gap at least r+2 before copying.
* Retained query workspace: frontier1, blank gap at least source-length+2,
  anchor11111 followed by0, and source bit fields of lengths bit+3. Source
  contains four rule bits then the exact leaf path. Initially the last1 of its
  final field is erased. The copy restores every source cell, writes the reverse
  bit string and a new frontier1, and returns on the last copied bit.
* The mirrored selector/oracle then reads left. Its three leaf-emission reads
  are0 only because the query source ends at an exact leaf and the preceding
  query cells were blank. That guard is narrower than arbitrary prepared input.

## Why the original certificate controller is not yet competitive

An unpacked inventory consisting of retained query133, edge68, mode writer11,
and comparator29 is241 states **before linking the controllers**. Exact and
forced-read packing reduces this substantially, but does not supply missing
control. The certificate version still requires:

1. Complete template-leaf path generation, iteration, restart and termination.
2. Transfer of each retained branch and observed bit into the native mode header.
3. Root restoration between paths and leaf-ID equality/parameter extraction.
4. Certificate parsing, all non-template proof rules, bounds/normalization, and
   both semantic disequality gates.
5. Fair candidate generation, rejection cleanup, workspace capacity, and blank
   initialization.

The edge consumes the copied absolute index. Its returned marked record alone
is not an uncharged numeric-ID register. A counter/field comparator does not
solve that missing connection by itself. Similarly, an oracle output-boundary
marker preserves depth but cannot reconstruct the destroyed branch word; the
retained-copy component was built specifically to solve the latter problem.

No credible complete <=245-state implementation of this certificate design is
currently available. This is an engineering assessment, **not a lower-bound
proof**. Unimplemented roles have no certified state count; assigning them the
remaining state budget would not establish feasibility.

## More promising whole-machine target: canonical monotone saturation

A genuinely different exact semidecision program can avoid supplied proof
certificates entirely:

* Generate the canonical native-Cantor term arena, or the proved equivalent
  square-shell arena, in a deterministic growing prefix.
* Maintain a persistent proved bit per record, initially true only at zero.
* Repeatedly sweep the entire current prefix, apply exact axiom recognition,
  GEN and MP, then grow the prefix. Halt when falsity record1 is proved.
* The proved set is monotone. Soundness follows by induction over markings.
  Completeness follows by finite-proof induction plus eventual appearance and
  repeated visitation of every needed finite record. No fixed-point detector,
  malformed certificate parser, proof-row ordering checks, or candidate proof
  enumerator is needed.

The exact finite reference and calibration proof are being developed under
`../logical_routes/`. Canonical injectivity turns denotational equality and
inequality into record identity tests. Generator state costs are not free.

### Concrete marker encoding that eliminates the comparator

Append the fixed eight-cell suffix `1 b 1 c 1 r 1 0` to every record:

* b: persistent proved bit;
* c: temporary selected-parameter mark;
* r: current candidate-root mark.

All zeros stay isolated, so existing doublezero marker scans remain sound.
Changing a flag never shifts the arena. The record locator must explicitly skip
these eight cells, and flag scanning, updates, clearing and root restoration
must all be charged.

One c track suffices for exact template matching. Sweep all leaf paths separately
for Z/P0/P1/P2/P3. For Z, put c on record0. For each parameter class, clear c,
mark its first encountered actual leaf, and require every later occurrence to
reach c=1. Other leaf classes are ignored in that sweep; constructor tests may
be repeated. For the bundle, process P2 last and leave its c mark; one further
path sweep requires P0 and P1 leaves to have c=0. This enforces both original
freshness gates without numeric parameter registers or path witnesses. The
root r mark restores the candidate root between paths.

This removes the 29-state comparator from the saturation inventory and avoids
the lost-index reconstruction problem. It does **not** create a completed
state bound: the fixed-suffix locator variant, flag handlers, class/path loop,
query observation transfer, canonical generator, growing sweep and boot are not
implemented as one literal table.

## Concrete next milestone

Build and independently audit a **closed native axiom recognizer** over a supplied
canonical arena with the b/c/r suffix. It must have one ordinary call entry,
explicit accept/reject returns, preserve proved bits, restore all temporary
markers, enumerate every required template path, and account for every source
query, mode update, root return, parameter class and gate test. Its literal
transition table and exact count will determine whether adding a canonical
record generator and monotone saturation controller can plausibly beat245.
A useful engineering target is a closed recognizer at no more than220states,
reserving25 for generator/saturation/boot. This is a target, not a demonstrated
allocation or a claim that either part fits.

Until that milestone, neither the packed component library nor the all-blank
component demonstrations solve the requested consistency-machine problem.

## Final measured packing frontier

The component-packing lane produced two exact, port-preserving libraries:

* Certificate inventory A: 241 raw roles to **216 working states**, 432 rows,
  five distinct unlinked return ports; 5,224 exact projected-trace tests.
* Comparator-free inventory B: 212 raw roles to **187 working states**, 374 rows,
  three distinct unlinked return ports; 3,280 projected-trace tests.

Their files are `../machine_encoding/component_packing/final_with_compare/` and
`final_without_compare/`. Failure states remain separate and charged. The
edge subtable has an unconditional exact quotient from68 to62 states. The final
one-state improvement also uses a separately certified unreachable rule-prefix
role under the documented rule3..11 query-entry contract. These
results materially improve the component baseline. They do not include the
b/c/r suffix or any completed saturation controller. B therefore leaves58
working-state slots under a245-state cap, not58 states of implemented control.

The unresolved saturation blocks are:

| Block | What the present table does not yet do |
|---|---|
| Flag-aware records | Skip the fixed8-cell suffix, read/set proved and c/r bits, clear temporary c marks, restore the candidate root |
| Path controller | Construct the source leaf path, establish exact-leaf padding guards, visit every leaf, advance/restart/end the iteration |
| Query/edge connection | Decode the leaf result, transfer branch/observation to the fixed mode header, and terminate the correct number of edge steps |
| Parameter/gate controller | Run the Z/P0/P1/P3/P2 classes with first-occurrence state and final bundle disequality sweep |
| Canonical generator | Maintain pair/tag counters and append variable-length reference fields while preserving the source counters |
| Saturation/boot | Grow fair prefixes, sweep current records, apply GEN/MP and flag updates, provision scratch gap, and initialize from blank |

No credible literal implementation fitting all of these within58 added states
has been established. No mathematical lower bound says it cannot be done.
The unlinked return/failure relationships also cannot be erased merely by
adding component counts. The complete requested machine remains unsolved.

The saturation finite reference now exists at
`../logical_routes/forward_saturation.py`: 2,565 single-marker recognition
crosschecks, 129 growing sweeps and three sparse AX/MP sweeps, with independently
exported C254 derivations. This supports semantic exactness, not a binary-TM
state bound. Scratch capacity can be increased by moving the counter sentinel
one cell left per appended record while keeping the arena fixed; the literal
growth controller is still unbuilt.
