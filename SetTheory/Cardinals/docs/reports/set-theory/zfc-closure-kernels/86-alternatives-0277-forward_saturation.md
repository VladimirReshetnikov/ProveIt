# Growing forward saturation: exact C254 proof search without certificates

## Result and boundary

A deterministic growing arena with one persistent proved bit per numeral,
repeated finite scans, and exact fixed-template recognition halts iff native
C254 derives the fixed numeral 1. No proof-certificate parser, proof-reference
validator, disequality witness, duplicate checker, proof-length enumerator,
or fixed-point detector is required by this design.

This is an ordinary exact finite-algorithm theorem. Under the established
ordinary native C254 calibration, its nontermination is equivalent in ZFC to
Con(ZFC). `forward_saturation.py` is a working high-level reference, not a
complete binary table or a claim of fewer than 246 states. The generator,
mutable flags, scans, lookup/copy helpers, template controller, and blank-tape
bootstrap all still require charged literal implementation and simulation.

## 1. Generated arena and zero

Generate record 0 first, followed by Cantor diagonals

    (m,0),(m-1,1),...,(0,m), m=0,1,2,...,

with tags 0,1,2,3 at each pair, omitting only tag0 at (0,0). Each record ID n
is exactly its native numeral:

    n = 4 P(left,right)+tag.

The children of every positive record are smaller than its ID. The
`canonical_arena.md` proof gives identity denotation, canonicality and complete
coverage of N. A prefix is therefore a total finite lookup structure for all
of its records' children, even when a lookup follows several edges.

Record0 is the special truth code. For constructor traversal its virtual tag
is0 and both children are0. It is the only allowed self-reference. A finite
path traverses precisely its finite number of edges, so virtual-zero cycles
do not make a template query diverge. The physical convention may use the
existing zero record with unary field lengths(1,3,3).

## 2. Infer parameters rather than enumerate them

Each trusted axiom template is a finite binary tree whose internal nodes are
the four constructor tags and whose leaves are literal zero or a named
formal parameter. Derived connectives, including F=Rel(0,0), have already
been expanded. The nine templates are exactly rho1,...,rho8 and the bundle;
all formal parameters occur at least once in each template.

Choose one representative root-to-leaf path p_j for each parameter j. For
candidate root n, let a_j be the record reached by following p_j from n,
using zero's virtual children as necessary. Run the existing **complete**
fixed-template matcher with this inferred argument tuple. For the bundle
also require a_2!=a_0 and a_2!=a_1. No guessed argument tuple is supplied.

**Parameter-recovery lemma.** If n is the value of a template E at arguments
(a_0,...,a_k), following any path of E to its parameter-j leaf reaches a_j.

Proof is induction on the finite path. Constructor inversion is unique for
positive values. At zero the only possible constructor equality is
Imp(0,0)=0, so the inverse children are exactly0 and0, agreeing with the
virtual record. Thus each descent follows the value of the corresponding
subexpression. The parameter leaf returns its argument. This proof does not
assume any parameter is a positive or well-formed formula code.

**Exact-recognition lemma.** Recognition succeeds at root n iff n is an
instance of that axiom template with its required gate.

For the forward implication, the complete fixed-template matcher establishes
n=E(inferred arguments); canonical identity IDs make the two gate comparisons
exact numerical disequalities. For the reverse implication, parameter
recovery gives exactly the witnessing arguments, then complete template
matching accepts and the gate holds. The argument tuple is unique because
every parameter occurs. If a future template had an unused parameter, assign
it0 and separately inspect any gate referring to it; no such exception is
needed for the current source templates.

### Concrete representative paths

The reference chooses shortest paths, breaking ties lexicographically, with
0 meaning left and1 right. In parameter order:

- rho1: 00, 0101
- rho2: 00, 010, 011
- rho3: 00, 01, 100
- rho4: 00, 10, 011
- rho5: 01, 101, 00
- rho6: 000, 1
- rho7: 01, 101, 00
- rho8: 01, 110, 000, 001
- bundle: 0100000, 000000, 0001000

The bundle paths have lengths7,6,7, considerably shorter than selecting the
first depth-first occurrence. They are computed from the exact pinned
source templates, not guessed. The existing oracle still verifies every
leaf occurrence and every constructor tag after these parameters are read.
One representative alone is never treated as full verification.

### One temporary marker instead of parameter stores

The production reference now also implements the architecture worker's
single-marker recognizer, and uses it by default. Keep a root marker r on the
candidate record and one independent temporary marker c. Make five complete
leaf-path passes in the order Z, P0, P1, P3, P2. At each pass, clear the old c
mark. For Z, set c on record0; for a parameter class, leave c absent initially
and keep one Boolean saying whether its first occurrence has been seen.

On every leaf path, check all its expected constructor bits. Ignore the leaf
value if it belongs to a different class. For the selected parameter class,
mark c on the first actual leaf record, then require c to be set on every
later actual leaf record in that class. For Z, require the actual leaf to
carry c, which is fixed on record0. The unused parameter classes of a smaller
arity template may be passed over harmlessly. All loops are bounded by the
finite template leaf list; no actual proof term is recursively traversed
without a fixed path bound.

After the P2 pass on the bundle, c is on its inferred parameter2. Perform
one further enumeration of the template leaf paths. Follow every P0 or P1
path and require c to be absent at its actual leaf. No other leaf needs to be
followed and no constructor bits need to be rechecked in this final gate
pass, because the previous passes verified them and the arena structure
remains unchanged. This enforces exactly c!=a and c!=b because those classes have already
been made internally constant and each has at least one occurrence. No gate
path witness, stored tuple of four parameters, or representative-path table
is needed by this version.

**Marker-recognizer theorem.** The marker procedure accepts exactly the same
roots as the representative-path recognizer. Each parameter pass succeeds
iff all occurrences of that parameter have one common actual ID. The Z pass
succeeds iff every zero leaf reaches0. Complete path passes check every
constructor tag, since each internal node occurs on leaves below both its
left and right edges and the oracle checks the corresponding two tag bits.
These conditions are precisely complete fixed-template matching for the
uniquely inferred arguments. The last bundle pass is precisely its two gates.
This proves equivalence to the exact-recognition lemma above, including the
virtual-zero case.

A physical implementation must distinguish c, r and the persistent proved
bit, preserve them across edge traversals, clear/reposition c, and implement
the class/first-occurrence controller. These are charged requirements, not
free auxiliary symbols or free lookup operations. `recognize_by_markers`
models them explicitly as a single mutable marker set plus a bounded-class
controller; its array operations are not a binary transition table.

## 3. Exact search algorithm

Initially the arena contains only record0, with its proved bit set. All later
records are appended with their proved bit clear. Never clear a proved bit.
At outer stage N, records0 through N exist. Scan them in increasing order.
For each current record n:

1. If it has tag0 and is unproved, try each of the nine axiom recognizers.
   Mark n if one accepts.
2. If it has tag2, say n=All(i,A), and A is proved, mark n.
3. If it has tag0, say n=Imp(A,B), and both n and A are proved, mark B.
4. Halt as soon as the marking target is1.

After this finite scan, append recordN+1 and repeat. At zero, item3 is the
harmless implication0=Imp(0,0), so it only re-marks0. Tags1 and3 need no local
axiom, GEN or MP action; their proved bits can still be set by an MP at an
implication record elsewhere.

All nine axiom templates have outer implication tag0. Hence the tag0 filter
loses no instance. Trying recognizers only when n is unproved also loses no
information; the future uses of a theorem depend on its proved bit, not on
which proof established it.

There is no requirement to reach a fixed point on the current prefix before
extending it. Old records are revisited at every later outer stage. The
program only appends one record after a completed finite scan, regardless of
whether the scan added any theorems.

## 4. Soundness

Invariant: every marked native numeral has a C254 derivation.

- Initially only0 is marked, by C254.truth.
- A successful recognizer marks exactly a primitive C254 axiom instance,
  including the exact gate for the bundle.
- Marking All(i,A) uses C254.gen and the inductively sound bit of A.
- Marking B at an implication record uses C254.mp, with the inductively sound
  bits of A and Imp(A,B).

The order of updates within a scan does not matter: each individual update
uses already sound bits. The invariant holds after every step, not just at
stage boundaries. A halt at target1 therefore implies C254(1).

For additional implementation simplification, only successful MP can first
mark1: initial0!=1; all recognized axiom roots have tag0 and GEN roots have
tag2. Thus a correct implementation may check for target1 only on the MP
mark path and omit a separate end-of-scan lookup of the F bit.

## 5. Completeness and termination of finite work

Each finite stage terminates: the prefix has finitely many records; the nine
templates and their representative paths are finite; lookup targets remain
within the prefix; each fixed-template traversal has a finite bound. Literal
binary routines must implement these total finite operations, but no search
for an unknown witness occurs inside the abstract scan.

Unless the machine has already halted, N increases after every stage.
Consequently every fixed record is created and scanned infinitely often.
Marks persist. Induct on a finite native C254 derivation:

- Truth0 is marked initially.
- An axiom output n is recognized on its first scan, once record n exists.
  Every inferred argument is reachable down its finite template paths and
  is therefore already in the prefix.
- For GEN, the matrix A is eventually marked by induction; a later scan of
  the record All(i,A) marks the conclusion.
- For MP, both A and Imp(A,B) are eventually marked by induction. A scan of
  that implication after both events marks B.

Thus every C254 theorem is eventually marked unless an earlier halt already
occurred. In particular C254(1) forces a halt. Combined with soundness:

    forward_saturation_halts iff C254_native(1).

A useful bounded formulation is available: once the prefix contains every
formula code in a given finite derivation, at most its derivation height plus
one further complete scans suffice, using one scan per induction layer.
No computable bound on a contradiction proof is presumed; this is only an
argument for each fixed finite proof.

The entire construction, finite-stage computation and induction on proof
objects are formalizable in ZFC. No step requires ZFC to assert its own
consistency or the truth of every ZFC theorem.

## 6. Executable evidence and cost handoff

The high-level reference computes all shortest representative paths from the
pinned source templates for the reference recognizer and audit witnesses.
Its default production search uses the marker recognizer and does not store
a tuple of recovered parameters. Audit witnesses are optional diagnostics. Its tests include:

-261 generated template instances, with846 recovered argument coordinates;
-2,304 candidate-root/template checks on a canonical native prefix;
-2,565 equivalence checks between marker and representative recognizers;
-32 finite virtual-zero paths and explicit all-zero rho8 recognition;
-129 growing scans, each exported as an optional diagnostic derivation and
  independently checked by the canonical certificate checker;
-a sparse positive propositional instance and repeated delayed MP firings,
  avoiding the enormous native prefix needed to exercise that instance by
  numerical ID in a short test.

Diagnostic proof rows exist only in `audit=True` testing. The production
reference needs nodes, proved bits and scan/generator control, not stored
proofs. No complete consistency refutation is expected or manufactured.

Compared with the proof-certificate design, this proposal removes untrusted
proof records, rule/premise/argument parsing, candidate proof enumeration,
reference-acyclicity checks, and both gate paths. In exchange it pays a
persistent writable bit per generated record, an endlessly growing native
record generator, repeated prefix scans, parameter extraction and exact
axiom recognition, plus two-child flag lookup/update for MP and one-child
lookup for GEN. The fixed template oracle and literal edge/locator components
may be reused only after their changed physical contracts are proved.

A complete binary transition table and end-to-end blank-tape theorem are
still missing. This document identifies an exact smaller-controller target;
it does not establish a numerical state saving.

## Independent review

`../verification/saturation_canonical_square_review.md` accepts the ordinary
proof and records an independent full-tag tree unifier agreeing with both
recognizers on21,717 cases, plus720 reconstructed distinguishing witnesses
and280 independent sweeps. These are additional finite diagnostics and an
ordinary independent review, not a literal binary-machine verification.
