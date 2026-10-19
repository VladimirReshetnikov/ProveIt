# Canonical arenas: eliminate disequality certificates, with the cost charged

## Result and scope

A finite, canonical term arena makes node-ID disequality equivalent to native
Cantor-code disequality. Consequently the two bundle freshness witnesses can
be removed from the direct certificate protocol. A deterministic square-shell
arena generator is an alternative to checking global uniqueness. Neither
option is free: the former needs duplicate detection, the latter needs a
literal generator and writer. No binary state saving is established here.

`canonical_arena.py` implements the first checker, normalization, and the
second generator as finite algorithms. It uses the exact twelve-rule source
calculus and fixed-pattern oracle of `../architectures/oracle_search.py`.
The following argument is ordinary mathematics, formalizable in ZFC, not a
Lean-checked theorem or a literal binary-machine simulation theorem.

## 1. Arena conditions and injectivity

An arena consists of record 0, denoting the numeral 0, and records

    node i = (tag, left, right),  i > 0,

where tag is in {0,1,2,3}, both children are less than i, and the triple
(0,0,0) is excluded. Write

    P(a,b) = (a+b)(a+b+1)/2 + b,
    value(0) = 0,
    value(i) = 4 P(value(left),value(right)) + tag.

Add the requirement that no two positive records have the same triple
(tag, left ID, right ID). IDs here are absolute identities, not unadjusted
backward-distance fields.

**Lemma.** The value map is injective on every prefix.

Proof by induction on the last record. First, no positive record has value 0:
this would require tag 0 and both child values 0. Prefix injectivity forces
both child IDs to be 0, the excluded triple. If two positive records have the
same value, reduction modulo 4 gives equal tags. Injectivity of Cantor pairing
gives equal child values. All their children belong to the earlier prefix,
so its injectivity gives equal child IDs. The two triples coincide, contrary
to uniqueness unless the records are the same. This proves the induction.

It follows immediately that c != a and c != b as node IDs give exactly the
native numerical side conditions for the bundle. The other eleven rules are
unchanged. Truth is ID 0. The fixed contradiction endpoint is the unique
record (1,0,0), when present; it is not a caller-selected endpoint.

### Virtual zero is essential

The constructor operation must return ID 0 for Imp(0,0), even though there
is no positive record for this triple. Pattern traversal from ID 0 uses the
virtual tag-0 node with two children 0. Only this zero node may self-reference;
all positive records are strictly backward. A finite fixed-template path
through zero remains finite, irrespective of the virtual self-loop.

The architecture worker's physical zero record already has tag 0 and both
references 0: unary field lengths (1,3,3), or raw biased counters (0,2,2).
`encoded_native_edge.py` supports this representation. Literal-zero leaves
still compare against exact ID 0. No extra physical zero-traversal states
are claimed or needed by that existing component's convention.

## 2. Normalization of existing certificates

Given any valid source arena, process records in increasing order. Maintain
an old-to-new ID map and an interning dictionary. Map the children first;
map (0,0,0) to zero, reuse an existing identical triple, otherwise append it.
The input validator currently excludes positive (0,0,0); including this
collapse in the mathematical procedure also handles a more permissive input.

Induction on old records proves:

1. every mapped positive record is well founded;
2. the output arena satisfies the three conditions above;
3. mapped nodes have exactly the old numerical denotations.

Replace every proof argument and claimed output ID by its mapped ID. Proof
premise-row indices stay unchanged. Delete the two gate paths. A source
accepted certificate remains accepted:

- truth maps to zero;
- a constructor equation remains a constructor equation after interning,
  including the virtual Imp(0,0) case;
- fixed-template matching is preserved by induction on the finite template;
- a successful source disequality path implies unequal numerical values,
  hence unequal normalized IDs by injectivity.

This implication assumes that the **source certificate was accepted**. An
arbitrary invalid witness is not preserved as an invalid witness, since the
normalizer removes witnesses. We do not claim acceptance equivalence for all
malformed source certificates.

Conversely, the canonical checker is sound for native C254 by induction on
proof rows and the injectivity lemma. If an old-format certificate is desired,
reinsert a finite distinguishing path for each unequal pair: stop when one
node is zero and the other positive, or the tags differ; otherwise descend to
a child whose IDs differ. Such a child exists by uniqueness, and the maximum
of the two positive IDs strictly decreases. The original path checker accepts
the resulting witness. Thus the two **existence-of-refutation** statements are
equivalent.

For completeness independent of a supplied source certificate, take any
finite numerical C254 proof, collect all its argument/output numbers and all
of their recursive base-4 Cantor children. For every positive code, both
children are smaller than that code. This closure is finite. Assign IDs in
increasing native-value order, with zero first. It is a canonical arena and
represents the whole proof. Every native numerical parameter, including
nonformula numerals and the truth alias, is covered by this construction.

## 3. Deterministically generate the arena instead

An untrusted certificate need not supply any arena if the machine generates
its canonical prefix. Begin with zero. For each m = 0,1,2,..., visit the pairs

    (0,m), (1,m), ..., (m-1,m), (m,0), ..., (m,m).

For each pair, append tags 0,1,2,3 in order, omitting only tag 0 at (0,0).
Before shell m >= 1 there are exactly 4 m^2 records, so children at most m
already exist. After shell m there are 4(m+1)^2 records. Each triple appears
exactly once. Hence every generated prefix is valid and canonical without a
runtime duplicate search.

Every finite hereditary constructor term appears: by induction its two
children already have finite IDs; shell max(left ID,right ID) emits the
constructor. Since every native natural has a finite hereditary constructor
decomposition after treating 0 as the base, every native natural appears
exactly once as a denotation. Therefore any finite C254 proof is representable
in a sufficiently long generated prefix. Enumerating a prefix-length bound
and finite proof records gives the same refutation-existence statement.

The emitted ID is exactly

    4 S(left,right) + tag,
    S(l,r) = l^2+l+r if l >= r, and r^2+l otherwise.

The omitted constructor would have ID 0, already supplied by the zero node.
This explains the square-pairing code algebra in `square_pair_conjugacy.md`.
It does not identify the generated ID with its native Cantor denotation.

### Alternative: native Cantor-diagonal generation

Instead visit (m,0),(m-1,1),...,(0,m) in stage m, with the same four-tag
cycle and the same omitted zero alias. Before stage m>=1 the arena contains
4*tri(m) records, more than m; hence all children are already present. The
ID of the next constructor is exactly 4*P(left,right)+tag. Induction now gives
**value(ID)=ID** for every generated record. This generator represents every
native numeral directly and needs no recoding isomorphism at all.

The two options differ in finite control: the Cantor diagonal decreases its
left coordinate and increases its right, whereas a square shell has two
phases with a fixed coordinate. A literal state count must choose between
them. Both avoid a runtime duplicate checker and justify ID-based gates.
`generated_prefix(..., pairing='cantor')` implements the native option.

## 4. Concrete implementation choices and costs

The proposed uniform proof record has type + four argument references + two
premise references + output + two witness pointers, ten fields. Canonicality
allows eight proof fields and removes both disequality-path-cell types (16
and 17). This is a representation simplification, not a numerical state bound.

**Option A: supplied arena plus duplicate check.** For each positive record,
scan earlier positive records and compare tag and both child identities.
Worst case is quadratic in arena length, with a tag comparator, two reference
comparisons, and nested scan/restore control. Absolute references can reuse
ordinary ID equality. Backward distances require rebasing or dereferencing
both to their target identities. For current-record positions i,j and stored
distances d,e, equality means i-d = j-e, not d=e. In a uniform stream the same
point applies even if proof records are interleaved with term records. The
checker must also check reference bounds and target types. Charging these
loops can erase any saving from deleting two path fields and their traversal.

**Option A2: sparse supplied arena with adjacent ordering.** Require positive
term records to have strictly increasing keys

    K(tag,left,right) = (max(left,right), left, right, tag).

An adjacent lexicographic comparison suffices. Because the key contains all
three constructor fields, strict order implies uniqueness, and the same
injectivity and ID-gate theorem applies. This replaces the quadratic
all-pairs duplicate scan by a linear number of adjacent-key comparisons.
Computing max, comparing unary references, restoring positions, and checking
strict backreferences are still charged. Raw backward-distance fields cannot
be compared as absolute IDs; the earlier rebasing warning applies unchanged.

This stronger condition preserves certificate completeness. First hash-cons a
finite source arena. Then emit canonical nodes by priority topological order:
among nodes all of whose children have been emitted, choose the least key
computed using their new child IDs. At each step at least one node is available,
by acyclicity. Already-available keys remain unchanged and are no smaller than
the selected minimum. Every newly available node contains the just-emitted
child ID i, so its maximum child ID is i; the node just emitted had maximum
child ID at most i-1. Thus every newly available key is strictly greater than
the previous output key. No two canonical nodes have equal keys after an
injective reindexing. Induction proves the output keys strictly increase.

The reindexing preserves every denotation and hence all proof arguments,
constructor equations and gates. The checker need not implement this sort;
it only verifies the supplied order. The sorting procedure is an offline
existence/normalization proof. `priority_reindex` and the trusted
`ordered=True` checker mode implement this exact reference. Sparse arenas
remain possible, avoiding the potentially astronomical complete prefix length
of deterministic generation.

**Option B: generated arena prefix.** Candidate input contains a finite bound
and proof records; a trusted generator supplies all term records. It needs
shell and pair counters, a four-tag cycle, a record writer/copy routine, and
prefix-bound termination. A concrete macro design can keep counters m,
within-shell position, and next record ID, with temporary copy/restore storage
shared with reference lookup. It must translate absolute child IDs into the
chosen physical reference fields if those are backward distances. It avoids
untrusted-term validation and duplicate checking but still pays every
initialization, generator, lookup, and writer state. Existing lookup and unary
writer primitives may be reusable; no complete composition has been priced.

**Option C: square-coded arithmetic.** Treat generated IDs directly as the
new numerical formula codes and replace only formula constructors/unpairing.
Proof/scheduler/stack pairing may remain Cantor. This removes the arena from
that architecture but brings back arithmetic constructors. It is a distinct
compiler experiment, not a free consequence of Options A or B.

## 5. Executable evidence and remaining obligations

`canonical_arena_results.json` records 264 source controls, 528 normalizations
(including a duplicate of every positive record), 498 accepted-control
preservations, 528 fixed-F negative controls, 300 random denotation-preserving
normalizations, and 12 generated square prefixes containing 3,448 tested records, plus
12 Cantor-diagonal prefixes containing another 3,448 records whose denotations
are checked to equal their IDs.
The ordered mode also passes528 certificate normalizations,498 accepted-
control preservations and300 random denotation checks. All pass. The finite tests supplement the ordinary proofs above; they are not
an unbounded machine verification.

A sub-246 claim would still need a complete binary table, charged blank-tape
bootstrap and generator/parser, exact physical contracts, termination of each
finite rejected-candidate check, fair enumeration, and a proof connecting the
literal table to this checker. None is supplied by canonicality alone.
