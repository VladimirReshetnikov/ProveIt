# Independent ordinary-proof review: saturation, canonical arenas, square coding

## Decision

The ordinary exactness arguments in `forward_saturation.md`,
`canonical_arena.md`, and `square_pair_conjugacy.md` are valid with their stated
abstract interfaces. In particular, grow-and-sweep saturation semidecides the
EXACT native C254 endpoint1. Combined with the previously reviewed native
calibration, ZFC proves its nontermination equivalent to Con(ZFC). Neither
this review nor its finite Python evidence supplies the missing literal
binary controller, blank bootstrap, or a complete sub246 machine.

Reviewed source versions and fresh tests are hash-bound in
`saturation_and_canonical_independent_audit.json`. The independent matcher in
`audit_saturation_and_canonical.py` uses direct full-tag tree unification,
not the producer's path/tag-bit oracle or representative-path extraction.

## 1. Canonical arena theorem

Take record0 with value0 and positive records (tag,l,r), tag<4, l,r<i.
Exclude (0,0,0) and repeated positive triples of ABSOLUTE child IDs. Set
v(i)=4P(v(l),v(r))+tag. Strong induction on the largest record proves
injectivity: a positive value0 forces tag0 and both child values0, hence by
the prefix induction both children0, excluded. Equal positive values force
equal tags and child values by pairing injectivity; prefix injectivity gives
equal child IDs, so uniqueness gives the same record. Thus ID inequality
exactly means native numerical inequality. F is exactly the unique positive
record with triple(1,0,0), if present, independently of its arbitrary arena ID.

Hash-cons normalization preserves denotation by induction, and therefore
preserves accepted source proof certificates after arguments and conclusion
IDs are remapped. Premise-row indices remain unchanged. The claim is
preservation of ACCEPTED certificates and equivalence of existence of a
refutation; it does not say all malformed witnesses remain rejected after
being discarded. Conversely unequal canonical nodes have a distinguishing
path: at zero-versus-positive or unequal tags stop; otherwise choose unequal
children. The maximum positive ID strictly decreases. The source witness
checker accepts these terminal conditions. Virtual Imp(0,0)=0 is treated
explicitly, never as an additional positive node.

Every natural numeral has a finite hereditary decomposition because each
positive constructor child is at most floor(n/4)<n. A finite native proof
therefore has a finite canonical arena, including all numerical parameters,
not just well-formed formula codes. Gate replacement introduces no extra
axiom or semantic freshness assumption.

The square-shell generator emits unique triples in square-code order. Its
children exist before each shell: before shell m>=1 there are4m^2>m records.
Every finite hereditary term eventually appears by induction on its children.
Its IDs need not equal native denotations; the latter equal f(ID) below.

The native diagonal generator is simpler logically: at pair(m-r,r), its
next IDs are exactly4(tri(m)+r)+tag, omitting only initial tag0 because record0
already exists. Before m>=1 there are4tri(m)>m records, so every emitted child
exists. Induction gives v(ID)=ID, and all naturals appear without omissions or
duplicates. Every partial prefix, not just every completed diagonal, satisfies
backward-reference closure.

The optional sparse adjacent-order criterion is also sound. Strict increasing
keys(max(l,r),l,r,tag) imply uniqueness. In priority topological reindexing,
newly available records contain the just-emitted child i and therefore have
max-child i, whereas the previous output had max-child at most i-1. Already
available keys were no smaller than the chosen minimum. Hence reindexing
produces strict key order and preserves all denotations. Physical comparisons
and reindexing costs are not free; raw backward distances cannot stand in for
absolute IDs.

## 2. Exact axiom recognition, including virtual zero

For a finite expanded template E, following a path to a parameter occurrence
in a genuine value E(a) returns that parameter's ID. At a positive
constructor, inversion is unique. The only zero constructor value is
Imp(0,0), whose actual virtual tag and children are exactly0,0,0. Consequently
path recovery also holds through zero, for arbitrary numerical parameters.
Every current formal parameter occurs at least once, as checked against the
pinned templates, so the inferred argument tuple is unique.

Direct matching is equivalent to: every template internal node has its full
expected two-bit tag, each literal-zero leaf reaches ID0, and occurrences of
each parameter reach one common ID. Complete leaf paths enforce both tag
bits: each internal node has a leaf below each child, and deterministic path
following reaches the same actual node at their common prefix. One path or
one representative does not suffice, but the procedure checks ALL leaves.

The one-marker algorithm implements exactly these conditions. On the Z pass
its sole temporary marker is fixed at record0. On each parameter pass the
first occurrence places that marker; all later occurrences require that same
marker. Clear it between passes. Empty unused classes are harmless. The
order Z,P0,P1,P3,P2 leaves the bundle's P2 marker present. A final pass requires
its absence at every P0/P1 occurrence, exactly enforcing a2!=a0,a1. Those
classes already have constant values and nonempty occurrence sets. No
parameter store or gate-path witness is assumed. Fixed-path depth bounds
make virtual-zero cycles harmless. In the reference the last gate pass
need not recheck tags because it changes no arena structure and previous
passes already established them; the document's stronger wording is safe.

These statements require a canonical arena, distinct root/temporary/persistent
proved marks, and physical preservation of all fields and marks by each
edge routine. The reviewed old native-edge contract does NOT automatically
prove a new flagged-record layout. That interface must be reproved in the
literal composition.

## 3. Saturation soundness and completeness

Maintain a growing identity-denotation native prefix and persistent proved
bits. Initially only0 is proved, using precisely C254.truth. For each finite
scan: accepted tag0 templates mark exactly one of the eight rho axioms or the
bundle with its exact two gates; tag2 records All(i,A) are marked from A by
unconditional C254.gen; a proved tag0 record Imp(A,B) with proved A marks B
by C254.mp. Record0's virtual implication only re-marks0. By induction on
individual updates, every bit set has a C254 derivation. In-scan use of a newly
set bit is sound. No other rule, axiom, or semantic validity test is added.

All nine primitive templates have outer tag0, whereas GEN outputs tag2.
Neither can output numeral1, whose tag is1. Initial0!=1. Therefore only a
successful MP can first mark1, and checking for halt only on that path is
correct. A marker mismatch merely rejects this fixed template, then scan
control must continue; it must not halt as a refutation or loop forever.

Every finite scan terminates at the abstract level: finite prefix, nine finite
templates, finite leaf paths, closed finite lookup targets. Appending the next
record also terminates. Unless it has halted, the prefix grows by exactly one
record after each scan, so every fixed record is eventually present and is
then scanned infinitely often. Marks persist. Induction on a finite C254
proof gives eventual marking: truth initially; axiom on its first available
scan; GEN on a later scan after its matrix is marked; MP on a scan of its
major implication after both premises are marked. The conclusion ID is
already in the prefix by the strict child bound. No current-prefix fixed
point is needed. An earlier halt is already a successful conclusion.

Thus Halt(Saturation) iff C254_native(1). All objects and inductions are finite
or arithmetically coded, and the argument is formalizable in ZFC. Composing
with ZFC's previously reviewed native calibration gives

    ZFC proves: Nonhalt(Saturation) iff Con(ZFC).

This is a proof about the specified finite algorithm. To transfer it to a
binary table requires a positive, terminating simulation of every finite
operation and the exact blank initialization. It does not assert that ZFC
proves either side, and it needs no PA endpoint, stronger theory, transitive
model, or assumed soundness of ZFC.

## 4. Square-code transport

The square pairing inverse using m=floor(sqrt(q)), d=q-m^2 has the stated two
branches, and S(a,b)>=a+b. Both code systems therefore have strictly smaller
children. Course-of-values definitions f and g can be implemented by ordinary
primitive recursion accumulating prior values; they are primitive recursive,
not merely partial recursive. Their constructor intertwining identities
include the sole zero exception Imp(0,0). Strong induction gives gf=id and
fg=id, and fixes0 and1.

Structural induction transports every source constructor expression, including
F=1 and every occurrence of the SAME parameter c as formula matrix and as
variable label in bundleG. Injectivity transports both exact inequalities.
Induction on proof objects transports all twelve rules both ways, giving
C254_square(n) iff C254_native(f(n)), in particular equivalence at1. There is
no appeal to well-formed formula codes or a separate freshness side condition.
The optional decoder renaming statement is compatible with the truth0
convention because f fixes0. Strict child bounds justify fresh labels by new
code+1 if a separate syntactic proof needs them.

This conjugacy does not preserve addition, ordering, stacks, or enumeration
states. The document correctly denies registerwise conjugacy and separately
reuses only abstract MP-first/reset-success contracts. Native diagonal
saturation does not depend on square coding at all.

## 5. Remaining acceptance obligations

The accepted ordinary algorithm narrows the design target but supplies no
literal binary generator, mutable proved-bit format, root/temporary-marker
handling, finite template/class controller, scan transitions, or blank
bootstrap. Each must be charged, composed with proved contracts, and shown
to terminate when its abstract finite operation terminates. A packed open-port
library cannot substitute for those obligations. The resulting complete table
must have fewer than246 working states, with one separately specified halt,
and be linked by the blank-run simulation/calibration checklist already saved
in `acceptance_checklist_and_transfer.md`. Missing Lean infrastructure is a
separate mechanization limitation, not a defect in these ordinary proofs.
