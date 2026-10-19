# Independent review: binary template-path oracle

18 October 2026. Reviewed `architectures/pattern_oracle.py`, both emitted tables, the result record, and maintained `term_patterns.match_pattern` / `term_circuits` definitions. This review does not modify the producer's files.

## Verdict

The 102-state binary component correctly emits the claimed observations for each fixed template path. Together with the high-level all-leaf traversal and exact node-ID comparisons, it recognizes exactly the same instances as the maintained fixed-pattern matcher, under that matcher's explicit input-validity prerequisites. No algorithmic defect was found. The universal result follows from the elementary lemmas below, not from finite test success.

This is not a102-state full matcher or consistency-search machine. The126-state blank demonstration performs one fixed probe and halts after50 transitions. Its count includes23 writer states and one adapter in addition to102 oracle states. Neither table is a solution to the target consistency problem.

## Exact assumptions and definitions

Let a template be a finite full binary tree with internal tags in `{0,1,2,3}` and leaves `Z` or `P_i` for `0≤i<4`. The retained templates arise by unfolding a fixed acyclic backward-wired DAG. Equal template subtrees may share machine states; occurrences in the unfolded tree remain distinct obligations.

An actual arena is a finite list with node0 equal to `['z']`; every positive node is `['b',tag,left,right]`, with tag in0..3 and child IDs strictly smaller than its own ID. The positive record `(tag,left,right)=(0,0,0)` is prohibited. The arguments and output are valid arena IDs, with the exact template arity. Duplicate positive records are allowed. For traversal only, node0 has virtual observation `(tag,left,right)=(0,0,0)`.

Define structural matching recursively: `Z` requires actual ID0; `P_i` requires exactly the supplied argument ID; an internal tag requires the actual/virtual tag to equal it and both children recursively to match. This is precisely the retained stack matcher's meaning. It is not denotational equality modulo arbitrary duplicate parameter IDs.

## Reusable universal lemmas

### 1. Literal path transduction and complete tape effect

Starting in the state assigned to a template root, at position h whose next d cells contain a root-to-leaf path `b₀...b_(d−1)`, the component takes exactly d+3 transitions and halts with head h+d+3. At each internal occurrence with tag t, it writes `(t >> b_j) & 1` at h+j and enters that child. At the leaf it writes its fixed three-bit code:000=Z,001=P0,010=P1,011=P2,100=P3. It changes exactly the visited interval `[h,h+d+3)` according to those outputs; every other cell is unchanged.

Proof: induction on path length to a leaf, followed by induction on the length of the emitter suffix. Each transition moves right, so no previously written cell is read again. Leaf emitters ignore their scanned symbols. Thus the three initially occupied output cells may contain arbitrary bits; both exterior contexts are arbitrary and preserved. The path itself is overwritten. The extra constant26 in the Python runner is an independently checkable depth cap for these fixed templates, not a general theorem for arbitrary input templates.

### 2. Exhaustion by incrementing the consumed path

Start with empty prefix, extend the current prefix by zeros until a leaf is reached, and then replace the rightmost0 in that leaf path with1 while discarding the suffix. If the path has no0, stop. This visits every leaf exactly once in lexicographic order.

Proof: the all-zero extension reaches the leftmost leaf below a valid subtree prefix. Incrementing at the rightmost0 returns to the nearest ancestor whose right subtree is unvisited; its zero extension is the next leaf. If no0 exists, all right subtrees have been exhausted. Equivalently, leaf paths partition all infinite bit streams into disjoint prefix cylinders, ordered lexicographically. Finiteness gives termination. The enumeration must use the path *read before overwriting*, as the Python trace does; the output tag bits are not a replacement for that path.

### 3. Two-bit observations recover every constructor tag

Assume every leaf query has the expected edge-bit output and the required terminal node ID. Then structural matching holds. For every internal template occurrence at path u, its left and right subtrees both contain a leaf. Queries through these two children observe bit0 and bit1 of the **same** actual/virtual node reached from the unchanged actual root along u. Equality of both bits forces equality of its tag in0..3. Apply induction to each child; at a leaf, the required exact ID is already checked. Conversely structural matching immediately makes all edge-bit and leaf-ID tests pass.

The same actual arena/root must be restored or preserved between queries. Checking two branches against different destructively modified candidate data would not satisfy the premise. Fixed-template subtree sharing does not invalidate the proof because all unfolded occurrences are queried.

### 4. Normalization and repeated parameters

For actual node0, both observations are0 and every child remains0. It therefore behaves exactly like the virtual normalized `B0(0,0)` used by the retained matcher. A positive-tag expectation is rejected on at least one outgoing edge. No additional normalization assumption is needed inside the finite template induction.

Each occurrence of `P_i` requires `actual_id=args[i]`. Consequently repeated occurrences necessarily use the same ID. Distinct equal-valued duplicate IDs are rejected at parameter leaves, while distinct copies of a fixed internal constructor pattern may be accepted. This is intentional and agrees with the maintained matcher. A future completeness proof for proof enumeration can choose suitably shared parameter representations; this component does not prove that every semantically equivalent arena representation will be accepted.

## What the state count does and does not include

The complete literal table contains91 constructor states and11 distinct nonempty emitter suffix states,204 rows and separate halt102. Its nine roots are different control entries. Choosing a root from a proof-row rule, traversing/recovering actual candidate nodes, testing exact IDs, enumerating paths, distinguishing the final three output cells from constructor outputs, comparing observations and returning for another query are external Python operations. They are not encoded in this table.

In particular:

- Entry states do not provide a free runtime dispatcher. The published component chooses the bundle entry11 only as its nominal table start.
- The component always halts at a leaf. A composed matcher must replace halt by a verified return protocol and account for its state/tape requirements.
- The apparent zero padding after a prepared prefix is used to descend to the next leaf. Three output cells need not be blank, but a caller must maintain the path-generation and boundary contract.
- The high-level generator recovers the consumed path from an execution trace. The physical table does not preserve that trace or a copy of the input path.
- Arena syntax validation, backward references, zero-alias exclusion, bounds/arity checking, fixed falsity endpoint, proof-history references, truth/MP/GEN rules, both bundle inequality witnesses, candidate enumeration/fairness, and a blank initializer for that whole program remain outside this component.
- The normalized constructors encode natural-number formula codes, not a newly substituted set theory. The high-level equivalence is to the existing matcher; a full runtime would still need the established certificate soundness/completeness bridge and ZFC calibration.

The fixed longest bundle path has length23. The blank demo uses102+23+1=126 working states; its start102 is a counted writer state and halt126 is separate. It writes the path while moving left, uses the adapter to enter the root, then overwrites that path with the oracle output. The complete final support was independently checked: positions `[-17,-13,-8,-4,-2,0,2,3]`, head4,50 steps. All other cells are zero.

## Fresh verification and minor harness issues

The original suite was run with `python3 -B ... --output verification/pattern_oracle_fresh`. Results and both emitted tables reproduce the producer's bytes exactly. The original suite checks261 positive assignments,13,500 random-arena comparisons,3,198 mutations and152 blank probes.

The independent `audit_pattern_oracle.py` adds:

- Separate structural DFS for all152 leaf occurrences and expected tag-bit outputs.
-456 literal whole-tape probes at translated origins with nonblank left exterior and immediate right suffix.
-2,664 deliberately duplicate-ID assignments, including758 accepted cases with duplicated newly constructed records.
-6,144 controls rejecting substitution of a different equal-valued parameter ID.
-Independent parsing/counting of both emitted tables and sparse replay of the blank126 demo.

See `pattern_oracle_independent_audit.json` and its log. These tests supplement the universal proofs above.

The producer's `main` does not explicitly reject optimized Python. Running with `-O` strips its assertions and can print apparent successful evidence without checks. Reproduction must use assertions enabled; a guard like the independent audit's `if not __debug__` is advisable. This is a verification-harness issue, not a discovered defect in the transition table. The producer pins the specification hash but does not separately pin imported circuit/matcher source; portable release evidence should bind those dependencies too.

The ordinary component lemmas use only finite trees, finite lists and induction and are formalizable in ZFC. No Lean theorem or complete binary verifier is claimed by this review.
