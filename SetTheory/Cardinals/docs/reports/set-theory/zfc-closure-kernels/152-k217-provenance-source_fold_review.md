# Independent review of the 217-state source rotations and final fold

## Scope and result

The standalone `audit_combo217.py` imports only Python standard-library modules. It independently reads the dominated-rho8 218-state predecessor and the proposed 217-state files, reconstructs the three rotations and final deletion, and checks all finite premises described below. It does not import the construction script, source-language library, decoder allocator, or runtime verifier.

The final native transition table has SHA-256
`b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088`.
It has 217 working states and 434 transition rows, with native start 0 and halt 254. Every working state is graph reachable. The source has 4,751 primitive occurrences and 203 distinct subtrees, maximum depth 45 and maximum consecutive zero run 6. Its SHA-256 is
`9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655`.

## The source operation

At the affected source root, identify five closed, halt-free factors D, A, B, C, E, with respective numbers of primitive leaves

```
D: 14, A: 27, B: 53, C: 374, E: 3682.
```

The old and new parenthesizations are

```
(D, (((A, B), C), E))
((D, A), ((B, C), E)).
```

Both execute the same closed factors in the same order. The concrete realization uses these three rotations:

1. Native parent 210, child 188, left-child rotation:
   `((A,B),C) -> (A,(B,C))`.
2. Native parent 213, child 210, left-child rotation:
   `((A,(B,C)),E) -> (A,((B,C),E))`.
3. Native parent 201, child 213, right-child rotation:
   `(D,(A,((B,C),E))) -> ((D,A),((B,C),E))`.

Each participating physical decoder is a pure right-moving bit-preserving pair. The rotated child has exactly one incoming transition from its parent, and each decoder has exactly one logical subtree role. The independent checker verifies these facts at the appropriate intermediate table, not only at the initial table.

The checker also verifies the literal complete primitive word and independently resolves every ordinal control edge after every rotation. Thus no guarded branch or continue target is assumed to survive merely from a leaf-count comparison. Each intermediate source's complete decoder relation is compared with the expected transformed relation, including the changed role of the rotated child. After the final fold it compares the complete relation with the union of the two merged roles.

The third rotation exposes native state 213 as the decoder for `(D,A)`. Its two transitions are

```
213/0 = 0 R 92
213/1 = 1 R 90.
```

The existing continuations satisfy

```
92/0 = 0 R 104
90/0 = 0 R 105.
```

This source reassociation creates the exact two-way selector needed by the final fold without adding a state.

## All-tape fold lemma

Write T for the rotated 218-state table. The candidate U deletes state 400, redirects its sole incoming target to 69, and changes one further row:

```
69/0 = 0 L 213.
```

The corresponding old rows are

```
69/0  = 0 R 105       400/0 = 0 R 104
69/1  = 1 R 31        400/1 = 1 R 31.
```

The only incoming transition to old state 69 is `53/1 = 1 R 69`; the only incoming transition to old state 400 is `224/0 = 0 R 400`. Consequently, at every occurrence of either state in a run starting in state 0, the cell immediately behind the head is an origin marker: one for 69, zero for 400. This is an invariant from the literal predecessor transition and does not constrain the initial tape.

Suppose the current head is h, the current symbol is zero, and the previous symbol is the origin marker m. The candidate executes

```
(69,h) -> (213,h-1) -> (92,h) -> (104,h+1),  when m=0;
(69,h) -> (213,h-1) -> (90,h) -> (105,h+1),   when m=1.
```

All writes preserve their cells. These three transitions visit only h and h-1 and finish with the exact entire tape, head, and continuation of the corresponding old one-step transition. When the current symbol is one, the two old transitions already agree and are reproduced by the candidate in one step.

Define phi(400)=69 and phi(q)=q for every other state. Every original transition outside the merged pair has a one-step mapped counterpart. Every transition in the pair has the one- or three-step counterpart just proved. The origin-marker condition is re-established whenever a matched transition enters the pair. Concatenating the positive finite blocks gives an infinite candidate run whenever the old run is infinite, and maps every finite old halt to a candidate halt. Conversely, candidate runs beginning at matched boundaries follow exactly these deterministic blocks; no block has more than three transitions or an internal halt. Therefore a candidate halt also corresponds to an old halt.

Thus, for every initial tape tau,

```
Halt(T, state 0, tau) <-> Halt(U, state 0, tau).
```

The lemma does not assert this correspondence for an arbitrary initial state in the merged pair without the origin-marker invariant. That stronger statement is unnecessary for blank-tape initialization.

## Remaining compositional premises

The audit establishes the exact source/control-graph transformations and the final all-initial-tape fold. It does not itself establish primitive-runtime correctness for the rotated parent, the blank-start frame, the dominated-rho8 theorem, or the source-calculus calibration. Those are separate components of the full 217-state consistency theorem and must be supplied by their corresponding independent verifications. No proof-assistant endpoint or minimality conclusion follows from this audit alone.
