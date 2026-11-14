# A weaker source reassociation theorem

This is a new, verified generalization of the sufficient source-rotation rule used by the supplied packages. It is a theorem about the structured numerical program, not by itself about a shared physical decoder.

Let A, B, C be source subtrees. Write F(X) and B(X) for the escaping forward and backward control-depth bounds given by `source_language.boundary`. The two trees

    ((A,B),C)   and   (A,(B,C))

have the same ordered primitive instructions and the same ordinal control graph whenever

    F(A)=0 and B(C)=0.

There is no closure requirement on the middle factor B. A may have escaping backward controls, and C may have escaping forward controls. Halt occurrences do not invalidate the theorem. The supplied builders used the stronger sufficient condition that all three factors were completely closed and halt-free.

## Proof

The source code implements a forward command by finding a specified zero edge among the primitive's ancestors and jumping to the end of that edge's parent interval. A backward command analogously finds a specified one edge and jumps to the beginning of its parent interval. Ordinary successor steps and positive decrement branches move to the next primitive in the unchanged ordered word.

Inside A, forward controls never escape A by F(A)=0. Its backward controls see prefixes `00` before the rotation and `0` afterward; this changes no one-edge ancestor. Thus backward targets agree.

Inside B, compare its old prefix `01` and new prefix `10`. Its first escaping forward command sees the end of the whole `ABC` interval in either tree: the old first zero edge belongs to the whole root, while the new first zero edge belongs to `BC`, and these parent intervals have the same right endpoint. Its first escaping backward command sees the beginning of `ABC` in either tree: the old parent is `AB` and the new parent is the whole root, which have the same left endpoint. Every later relevant ancestor lies outside the changed region and is identical.

Inside C, backward controls never escape C by B(C)=0. Forward controls see prefixes `1` and `11`, which change no zero-edge ancestor. Their targets therefore agree.

Controls staying entirely within one factor are unchanged. The primitive word is unchanged, so all ordinary successor edges agree. This proves the theorem in both directions.

## Executable check

On class A, the rule admits 58 pure-selector rotations with a unique incoming edge to the inner physical selector, compared with 51 admitted by the older all-three-closed rule. Every one of the 58 was checked against both independent source CFG resolvers:

- interval/ancestor unwinding;
- arithmetic binary increment/cut, including all 5,084 no-stray-suffix target checks.

All 58 preserve the exact 3,909-primitive word and ordinal CFG.

This does **not** certify the physical table: source selector states are also entered by arithmetic routines. The new rule adds seven rotations to the initial search space. Only `(225,210,right)` passes the fresh 5,084-case finite canonical runtime screen among those seven, and it does not remove a state. The other six have explicit finite failures. Full runtime induction is required before any new layout can inherit the machine calibration.

## Further searches and their limits

1. The earlier closed-rotation breadth-first search examined 24,321 distinct tables through three rotations. Fifty allowed an exact duplicate-state contraction to 207. Every one failed a finite primitive case; all contain the same invalid 85/154 suffix merge.
2. A connected directional search examined 939 class-A layouts through depth 12 (four new source-region seeds) and 5,729 class-B layouts through depth 9 (all initial seeds), with capped per-seed frontiers. No exact duplicate contraction appeared. This is a bounded heuristic search, not a minimum-state theorem.
3. All 42 binary parenthesizations of the six closed factors that distinguish A and B were considered. Nine obey the required zero-entry tags for factors 158 and 220. The arithmetic return of 220 was retargeted to the parent whose zero branch enters 158. Of these nine literal constructions, only the original A and B associations passed all 5,084 finite canonical cases. None removed a state.
4. A directional beam search with width 20 through 20 rotations examined 19,136 tables. It reduced the number of source leaves containing six consecutive zeros from 33 to 17, but never reduced the maximum zero run below six. Hence it did not justify deleting the origin-detector state 34. Many intermediate layouts were not physically valid; these were exploratory source-level transformations only.
5. A simultaneous-parent rotation search also considered shared inner selectors. No refactor with at most one new suffix helper saved a state. Of twelve larger fan-out refactors in each class, rotating state 168 at its three parents passed all finite primitive cases, but increased the table from 208 to 210 states. A subsequent radius-seven contextual-fold screen by the other research agent found no reduction on either expansion.

All tests deliberately distinguish finite canonical regression, exact source-control equivalence, literal state counts, and universal physical runtime correctness. None of these negative searches is a lower bound on the state count.
