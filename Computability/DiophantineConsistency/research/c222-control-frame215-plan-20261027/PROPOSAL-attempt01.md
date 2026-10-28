# Actual 215 canonical entries and represented control frame

27 October 2026. Read-only proposal: no Lean source, private import overlay,
compiler command or prerequisite refresh is created by this packet.
The proposed pair is `DiophantineConsistency.ArithmeticControlFrame215`
and its focused `Checks`, importing exactly `ArithmeticSite215` and
`BusyBeaver.ZFC.ArithmeticControl215Table`.

Site215 is now ROOT accepted. Select `/tmp/site215-root-1ub48_h4/lib`
directly, retaining its author history. The accepted table provider is
`/tmp/control215-table-peer-_nt2n9b9/lib`, accepted in commit 048399e422.
The complete source, object, header and package-provider union is recorded
in `cache-plan.json`; this is a proposal for that union, not launch approval.

## Exact first checkpoint

The first pair constructs the actual finite catalogue, fixed represented
entry graphs, full consumed-path rebasing and canonical-entry instruction
contracts. Its proof target is a real use of `spec215`, not a theorem
conditional on supplied table/site correctness. Estimate 500–750 lines
including finite catalogue adapters, formula realizations and six cases,
plus approximately 70 lines of focused checks. A substantial change to this
boundary or a need for another import must return for scope review.

All numeric file contents, spare counts, gaps and execution clocks range
over an arbitrary `ORingStructure V` satisfying IΣ1. Only the actual source
tree, paths and finite control index are external syntax. Work at arbitrary
universe here. No internal value or time is replaced by a natural number.

### Actual catalogue and physical file

Define `entries := ControlCatalogue.leafEntries KSource215.t215`,
`Control := Fin 4751`, `source i := entries[i.val]`, and `number i := i.val+1`.
Derive the entry count from the accepted `table215_eq_catalogue`,
`table215_length` and length of map. Every `source i` is `LeafAt` by
`leafEntries_sound`. Site215 then derives length ≤48, exclusion of `.node`,
and logical/physical register bounds for INC and DEC.

The exact table row at `number i` is
`rowOf KSource215.t215 (source i)`. Derive its packed `rows215` lookup from
the existing list equality and the definitions of `PackedTables.table`
and `rowsOf`; use `spec215` with this lookup. This reuses every accepted
one of the 4,751 rows, including both successor fields and the complete
high-bit bound. It introduces neither another packed numeral nor a new
4,751-case executable certificate.

For arbitrary finite input path P, closed `KSites215.all_sites` and
`SiteCoverage.allSites_walk_total` give an actual successful walk of the
literal p215 (root 178, 179 nodes). `ControlCatalogue.entry_at_crank`
identifies the ranked slot with `(consume P d,e)`. Define
`resolveControl P := crank (annotate t215) P` with that derived bound.
Thus `source (resolveControl P) = (consume P d,e)`, not `(P,e)`.
`nextControl i branch` is the actual `successorOf` field, and for nonhalt
entries is exactly `number (resolveControl (outgoingPathOf ... branch))`.

No new `ControlTableBinding` import is needed. The small generic reverse
`LeafAt`→`twalk` proof is a structural induction on the existing three
constructors, as in that source-only guide. Combining it with
`RMBisim.walk_root` and `walk_follow_consume` proves `follow` for an actual
source path. `entry_at_crank` and nodup can also supply self-resolution;
there is no assumed rank or successful-walk oracle.

The file is already in physical order:
`values file p := ArithmeticControlFile.regValue file p`, p:Fin 9.
The table constructor has already applied
`Permutation252Frame.physOf` to each logical INC/DEC register. Prove its
nine-way agreement with `KSim.physOf` at the source-derived r<9; the map
is `[6,2,0,4,3,7,8,5,1]`. Do not apply either physical permutation to the
packed file a second time. `reg_write_same`/`reg_write_other` identify the
written file with `Function.update (values file) r newValue`.

### Fixed graphs and exact entry code

Define the following syntax before ambient-model parameters:

* `pcRows := List.ofFn (fun i : Control => (bitsNat (source i).1,
  bitsNat (source i).1))`; `pcDef : Σ0.Semisentence2` specializes the
  existing `lookupDef (compactRows 0 pcRows)` at branch 0.
* A fixed Σ1 graph for `block value suffix =
  2*bitPrefix true (value+1) suffix`, using the accepted `bitPrefixDef`.
  A finite external fold over `List.finRange 9` composes this graph with
  `projectionDef 8 i`. Its value is exactly the existing `file` of the
  nine physical register values, with an arbitrary untouched suffix.
* `spareDef : Σ1.Semisentence2` is `repeat3Def out k 6 0`.
  Its realization is `repeat3 6 k 0`; the underlying public graph's order
  is `(out,n,d,z)`, not `(out,d,n,z)`. This covers k=0 syntactically.
* `entryDef : Σ1.Semisentence5` composes those graphs, two false prefixes
  and the actual pair graph. It realizes

```text
entry q file k gap = frameSparse 84 1
  (pcValue q + bitPrefix false 64
    (bitPrefix false gap (2*plain (values file) k+1))).
```

Sparse 84 is arithmetic state 24, not 85. `entryDef` uses that literal 24
after the accepted sparse-code equality; all formulas are fixed and
independent of V. Export total Σ1-function instances and their Δ1 graphs,
including the finite-fold and lookup realizations. Positive k is required
only by the execution contracts, not by numeric graph totality.

`pc_at i` is obtained from `compact_lookup_at`, with no linear per-row
proof search. The numeric affine prefix equality identifies
`entry (number i) file k gap` with Site215's actual `startValue` for
`source i`, using length ≤48≤64. Invalid q has total lookup default 0;
that default does not identify a live control.

Also prove the precise support guard needed later:

```text
opcodeValue table215 q ≠ 0 → ∃ i : Control, q = (number i : V).
```

This follows from `compact_lookup_supported` on `opRows`. It must not be
asserted for every nonzero q. The actual halt row has opcode 4 and is a
valid live entry until its next instruction; malformed control codes are
excluded rather than silently interpreted as live paths.

### Suffix-preserving consumed-path rebasing

Let `budget ovf extra := 64+ovf.toNat+extra` and
`padded P N := P ++ replicate (N-P.length) false`.
For a clean outgoing P with length ≤64, coverage gives a real next leaf
Q=`consume P d` and d≤48. `RegisterPathClean.Clean` gives every bit of
`P.drop d` false. Apply `gap_consume P (budget-P.length) d`, whose bound
holds since both P and d fit within 64. Obtain equality of the *entire*
padded lists at the same budget. This includes d>P.length (implicit zero
extension), d<P.length (only proven zero suffix removed), and P=[] cases.

Prove `pathValue_append`, `pathValue_replicate`, and the affine identity

```text
pathValue P z = binaryValue P + bitPrefix false (P.length : V) z.
```

These are finite list inductions using the already-proved internal prefix
algebra. Apply the padded-list equality with the whole arbitrary internal
suffix `bitPrefix false gap header`. The resulting identity is

```text
frameSparse 84 1
  (pathValue P (bitPrefix false
    (gap + ((budget ovf extra-P.length : Nat) : V)) header))
 = frameSparse 84 1
  (pathValue Q (bitPrefix false
    (gap + digit ovf + (extra:V) + ((64-Q.length : Nat):V)) header)).
```

Here every subtraction is of bounded external naturals before casting;
the arbitrary internal gap remains additive. No truncation identity is
used without its bound. This equality preserves marker, all register data,
all spares and every trailing bit of `header`; equality of just numeric
path bits would be insufficient.

For actual source entries, derive Clean of each outgoing path from
`execute_clean`. Dummy Nat registers 0 or 1 select only the finite DEC
branch; actual internal register values remain arbitrary and enter only
the corresponding zero/nonzero execution premise. Break/continue count 0
and empty stripped paths are legal. Derive outgoing length≤source length
with `KSim.incPath_length`, `breakPath_length`, and `stripPath_length`.
No source run/reachability premise is needed to prove this local Clean.

### Actual canonical instruction package

Compose the accepted six Site215 source clients, the full file-write
identity, and the rebase equality. None of the public instruction clients
assumes a desired binary endpoint or successful-checker premise.

| Actual operation | Physical file | Spares | Added internal gap |
| --- | --- | --- | --- |
| INC r | write r (value+1) | k+1 | digit(allOnes Q) |
| DEC r, value 0 | unchanged | k | digit(allOnes(stripPath false1 Q)) |
| DEC r, value≠0 | write r (value-1) | k | digit(allOnes Q)+1 |
| break j | unchanged | k | digit(allOnes(stripPath false j Q)) |
| continue j | unchanged | k | 0 |
| halt | full terminal tape retained | — | first(config)=0 |

The r column denotes the once-mapped physical index. INC appends one
value-one spare; positive DEC adds a blank cell on the left and does not
append a spare. Every next entry uses the actual packed successor, whose
canonical path need not equal the outgoing path. The same positive clock
from moved=false Site215 is retained; numeric rebasing introduces no run.

Export the six readable cases plus finite-index `entry_step`/`entry_halt`:
for i:Control and arbitrary file,k,gap with k>0, let
`next := stepValue table215 (liveValue (number i : V) file)`.
If next≠0, derive actual j:Control, file', k'>0, gap' and clock>0 with
`next=liveValue (number j : V) file'` and the binary run reaching
`entry (number j : V) file' k' gap'`. If next=0, derive a positive
clock with terminal first projection 0. These follow by the actual source
edge cases and `spec215`; the impossible `.node` branch is excluded by
the accepted source certificate. They do not assume the step result's
validity or a caller-selected next canonical path.

The first pair may expose `entry_active` (first projection24) and the
finite support lemma. It does not define the global Related invariant or
prove its all-time simulation, its boot instance, or a PA/HA endpoint.

## Focused checks and next composition

Checks should retain the fixed formula arities and realized total graphs,
all internal parameters, zero gap/k=1 execution, graph k=0, repeated and
zero register values, all nine physical positions, source halt activity,
invalid control 0/4752, and full suffix examples on each side of consumed
length. A finite actual first-source client should recover DEC logical 8/
physical 1 and row `(2,1,3,2)` without expanding the whole catalogue.
No test should identify terminal scalar config with0.

The next separately scoped leaf can define the genuine Σ1 invariant

```text
Related l b := l≠0 ∧ opcodeValue table215 (controlValue l)≠0 ∧
  ∃ k gap, 0<k ∧ b=entry (controlValue l) (fileCodeValue l) k gap.
```

The support theorem selects a finite i for arbitrary internal l. The two
finite instruction clients then discharge the actual positive-clock
`related_step` and `related_halt`; `related_active` uses state 24. Together
with full halt absorption and actual control/run graphs, accepted generic
`ArithmeticPositiveSimulation254` supplies both internal halting directions
by its genuine Σ1 clock invariant. No clock upper bound or new IΣ2
assumption is expected.

Boot is a separate concrete binding: control 1 has PC bits 0; physical
file=`fileValue ![0,0,0,0,0,0,4,0,0]`, k=40, gap=1. The 64-cell margin plus 1
is the accepted 65-cell blank prefix. Symbolic's Nat sepsR/plain identity
and fixed numeric casts identify this entry with Tape215.bootCode.
Use the accepted 95714-step boot theorem, not another long execution.
Then the target is actual `run215` halting at that seed iff actual
`ArithmeticMachineRun215.run` has first projection 0. Accepted control
bisimulation and DagRuntime connect this to actual EnumPerm222 separately.

The final displayed-equation HA proof is still open. In addition to the
remaining runtime composition, actual source-ZFC proof calibration and
internal Pell/polynomial witness equivalence must be completed and bound
to the exact current ports before applying the PA-to-HA proof transfer.

## Authenticated union and provenance

The proposed union has 191 cached modules, including 95 Foundation modules,
476 cached artifacts,41 package primaries plus 123 companions, hence 640
first artifact providers. There is zero refresh and no new Foundation
module. Relative to the173-module Site prerequisite inventory, add Site's
accepted ROOT main, 16 existing table-side modules, and the accepted table
main. Shared selected sources and primary bytes agree between the two
inventories; retain all original provider and execution records.

The existing source-identical unequal KZip alternative belongs to Site's
inherited history; it is not relabeled identical or newly selected here.
The generic physical-map module imports some old 253 definitions, but no
old 252/253/240 execution or simulation theorem is used. Rotation240
catalogue/frame/rebase sources are planning guides only, explicitly
outside the selected import graph. Reuse actual215 accepted certificates
and the genuinely generic path/prefix contracts described above.

The planner recomputes every source header, complete reachable DAG,
topological ordering, source/object pin, imported package boundary and
first artifact provider. It authenticates both accepted packets/manifests
and the table's existing PackedTables/DagControl provider supplement.
No shared project-cache fallback is permitted. The future two commands,
if approved, use pinned Lean 4.32, fresh regular outputs, M6000/j1/async=false
and the 512MiB guard. Snapshot both inputs before each attempt and retain
all failures. Pin one immutable prerequisite inventory rather than copy
its complete profile into every attempt.

This agent authored Site/Home/Symbolic/Boxes/Tape and the actual table and
several earlier runtime dependencies. This is a source-bound implementation
proposal, not an independent review of those authored prerequisites.
