# Nested formula holes defeat root-array repairs of the parity-free opener

## Claim and limits

In the existing shifted sorted-arity certificate language, removing the opener's sort-parity multiplier is unsound even if (i) every template used by the replacement branch must have an array at its root, and (ii) every semantically active formula node in every nonadministrative checked goal and retained context entry must be an array. A single scalar hole nested immediately under a paired binder suffices.

This strengthens the particular scalar-root attacks in the inspected Chapter 11, section “A rejected saving.” It is not an obstruction to an opener whose **pre-substitution formula templates are recursively checked at every active formula position**, nor to completely different typed encodings. On canonically sorted templates the parity-free and original openers agree on all semantically active positions. The proposed strengthening is local to the inspected sources; no literature-wide priority claim is made.

## Exact shifted codec

Fix floor k=0 at the root. A formula at p protected numerical slots is traversed at depth 2+2p; a term at p slots is traversed at depth 5+2p. The child of an r-entry array has depth d+5-r.

At a formula position, an array of arity 1 reads D_xy of its child, arity 2 reads equality of the two numerical children, and arity 3 reads Q_y of its last child; the first two children of a ternary formula are ignored annotations. Other arities read truth. At a term position, arity 1 reads successor, arity 3 reads the scalar iterator I(counter,initializer;state.body), and arity 2 reads zero with its children ignored. The scalar zero reads numerical zero. The shifted code of slot j is 5+2j. A successor node contributes two dummy slots; the counter/initializer of an iterator contribute one dummy slot, and its body contributes its state slot.

The ordinary formula meanings are Q_y B = (B(0) -> forall y B(y)) and D_xy B = exists x (B(x,0) -> forall y B(x,y)). A scalar at a formula position reads truth.

For finite integer/list trees, define the original **eager** opener E_k(a;t,d) recursively:

1. If a is an r-entry list, return [E_k(b;t,d+5-r): b in a].
2. If a is an integer in [k,d), return a.
3. Otherwise first validate v=E_k(t;missing,5), and return (d mod 2)*v, with the language's ordinary integer/list multiplication. A missing image rejects.

Thus an out-of-range scalar at even formula depth becomes 0 when its validated image is an integer, or [] when its validated image is a list. Both have the formula reading truth. This is the exact eager variant in the current 461-byte checker, not the older lazy variant that always returns scalar 0 at even depths.

The weakened opener W_k deletes only the multiplier in case 3 and returns W_k(t;missing,5) unconditionally.

## Five raw objects

Define

    E = [[7,0,0],[7,0,[0]]]
    H = [0,0]
    S = [0,E,H]
    F = [6]
    A = [E]
    M = [S,E].

All names above denote raw trees; in particular S is a name for this specific raw tree, not the successor constructor. To avoid that overloading in typeset prose it may be called R instead.

At formula root depth 2, A has one D node. Its matrix E is therefore read at depth 6, its equation children at term depth 9, and their iterator children at depth 11. In each iterator counter, code 7 refers to slot j=1: the inner dummy slot is j=0, and the D-index variable y is j=1. The D-witness variable x is unused. Consequently A is the canonical guarded public formula

    D_xy ( I(y,0;u.0) = I(y,0;u.S(0)) ).

Its zero instance is 0=0; its successor-one instance is 0=1. Therefore A is false in the standard natural-number model, independently of x. This alone establishes that a sound iPRA presentation cannot accept A.

At the **term** root depth 5, E is a binary array and denotes 0. H likewise denotes 0. S denotes I(0,0;u.0), hence 0. The equation M=[S,E] is literally the raw zero-computation instance I(0,E;u.H)=E; no equality axiom about ignored annotations is needed to prove it.

At a **formula** position S is a ternary Q node with last child H. Thus [S] reads D_xy Q_z(0=0), which is a theorem. Its numerical x,y variables do not occur in the active reading. Although S's first two children are ignored formula annotations, their traversal is in scope: the supplied code 7 always stays below the relevant depth. The actual checker replay below verifies these exact scope facts, rather than erasing the annotations informally.

## The wrong replacement

F has an array at its root, namely a D node. At formula depth 2 its scalar child is traversed at depth 6. The integer 6 is out of range there, so the weakened opener inserts the supplied image:

    W_0(F;E,2) = [E] = A,
    W_0(F;S,2) = [S].

Both E and S validate unchanged at root term depth 5, so the numeric-image check succeeds and no further substitution occurs while validating either image. As a numerical term E has no free variable at all: its binary root reads zero. When this same tree is inserted into a formula position under D, its annotations acquire the formula reading E(y), including the bound y. That change of sort is the defect; numerical closedness does not assert formula closedness. The original opener instead gives

    E_0(F;E,2) = [[]],

which is different from A. Its nested scalar is erased to a truth-formula code, as required by the sorted reading.

The weakened replacement branch therefore derives the false A from the true [S], using the legitimate zero-computation major M. The mistake is that a formula-position scalar, whose ordinary reading is constant truth, is allowed to become a whole formula merely because the same raw image was validated under its term reading.

The post-substitution premise [S], conclusion A, and major M all have arrays at every semantically active formula position. That check does not detect the original scalar leaf in the **template** F. Recursively checking formula positions in F itself would reject F and blocks this example.

## Complete six-record input

The pinned 461-byte checker consumes packets [source,target,template,major] by popping from the end; its final header is [goal,initial_floor]. Let Z=[0,0,0,0]. The full JSON input is

    [Z, Z, Z, [0,E,H,0], [S,E,F,M], [A,0]].

The execution consumes the transport packet, its zero-computation major packet, an introduction packet for [S], the administrative neutral-major packet, and the hypothesis-closing packet. The three Z rows supply those last three operations. The outer call's new floor is -1; the introduction continuation has floor -2. All actual free names remain protected, and the false goal is closed.

The supplied program `test_nested_template.py` generates this input and independently checks the two openers' exact trees. It runs the byte-identical upstream checker and three deliberately unsound variants:

| Program | Observed result |
|---|---|
| Original 461-byte checker | Rejects |
| Delete parity multiplier only | ACCEPT |
| Delete multiplier; replacement template root must be an array | ACCEPT |
| Also require every active formula node of each nonneutral checked goal and context entry to be an array | ACCEPT |

The original rejects by exhaustion of the deliberately insufficient certificate, not by a special detector. The point is its soundness and its failure to execute the invalid replacement. The variants all finish normally and print exactly ACCEPT.

## Provenance and novelty check

Pinned source: ProveIt commit 7a7633980dbca7f599322a5e7f1e65fb1cddb7c8, `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts/prefix_conditional/code/checker_bytes461.py`.

Source SHA-256: e587d311a76e7b1ac9a292883ff57a139ad7ddf8dceff8d39d489a033f29525e. It is preserved byte for byte in `pinned_checker461.py` and distributed under ProveIt's MIT No Attribution license.

The integrated Chapter 11 gives the unshifted scalar-root template 0, shifted scalar-root template 2, and their complete false-goal packets. Searches across all eleven chapter sources and the four pending November 13 archives' new reports and notes found no stated root-array repair or the nested-template construction F=[6]. This is evidence of difference from the inspected proposals, not a proof of absolute novelty.
