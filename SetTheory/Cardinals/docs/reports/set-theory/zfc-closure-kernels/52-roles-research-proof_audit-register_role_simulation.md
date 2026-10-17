# Register-role transfer elimination: theorem and proof obligations

This note supplies an ordinary mathematical simulation theorem for the proposed compiler transformation. It also reviews the current `dynamic_renaming.py`, `static_coalescing.py` and `allocation_certificate.py` experiments. It does not assert that a new binary machine below 252 states has been produced, or that a new Lean proof has passed.

## 1. Exact zero-destination move theorem

Let logical and physical registers both be indexed by `{0,...,8}`. Let P be the physical value vector and let sigma be a bijection from logical register names to physical slots. Decode by

```
R(r) = P(sigma(r)).
```

Consider the complete source macro

```
while S > 0:
    S := S-1
    D := D+1
```

with distinct logical registers S and D. For any input vector R this macro terminates and returns `S=0`, `D=oldD+oldS`, with every other register unchanged. Termination follows by induction on oldS, which decreases once per iteration. The literal source occurrence must also include and execute its final zero-test and control exit; its exact instruction clock can be checked from the original decoder graph.

**Role-swap lemma.** If `R(D)=0` at entry to the complete macro, its final logical vector is obtained without changing P by swapping the two entries sigma(S) and sigma(D) in the decoding map.

**Proof.** Let sigma' equal sigma except `sigma'(S)=sigma(D)` and `sigma'(D)=sigma(S)`. Then the new decoded S is `P(sigma(D))=0`, the new decoded D is `P(sigma(S))=oldS`, and every other decoded register is unchanged. These are exactly the macro outputs under oldD=0. The transposition preserves bijectivity. QED.

If S=D, the positive-input source macro would diverge because decrement and increment cancel. It must not be treated as a general move. The special case where the common register is provably zero can be erased as a zero-test-only macro, but this needs its own guard. Keeping the distinctness condition in the general transformation is simpler.

The physical table does not learn a new decoding map for free. The map must be reflected in the compiled control state and every subsequent register selector, or be represented as charged data interpreted by the runtime. The theorem is an identity on represented values, not an uncharged hardware instruction.

## 2. External entry and loop backedge are different phases

The premise D=0 is required before the complete macro is entered. It normally fails after one iteration, when D has become positive. Therefore the transformation is not a rewrite of an arbitrary visit to the decrement header. It is a replacement of the entire loop occurrence, including its backedge.

A finite source certificate should identify each eligible occurrence by its actual decoder path and verify:

1. the header is the intended decrement/test on S;
2. its positive branch reaches exactly the increment on D;
3. that increment reaches the actual continue returning to the same header;
4. its zero branch reaches the claimed macro exit;
5. no reachable edge from outside the occurrence enters an interior increment or continue leaf;
6. every edge entering the header from outside the occurrence establishes D=0;
7. the source invariant includes the actual initial state and is closed under every feasible source transition.

For the simple three-leaf move shape, the internal path can be checked literally; the macro effect and termination are then proved once for arbitrary natural register values. A path-prefix test used to classify incoming edges is a convenient implementation device, but its equivalence to these exact boundary conditions should be checked, not assumed.

The strongest entry invariant is formed from the abstract postconditions of *external* predecessors only. Reusing that entry invariant on ordinary loop backedges would be unsound. Once the complete loop is replaced by one macro edge and no external interior entry exists, each visit to the compressed macro node is a genuine external entry, so the stronger invariant is appropriate.

## 3. Safe canonicalization of a decoding map

Suppose a source phase invariant proves that all logical registers in a set C have the same value. Permuting the physical-slot assignments among names in C preserves the entire decoded logical vector. Thus one can sort those slot assignments to choose a canonical representative without changing tape or logical state.

The current abstract masks distinguish exact values 0 through 31 and one class for values at least 32. Equal masks do not in general prove equal values. Equal singleton masks for an exact value below 32 do suffice. A singleton high-class mask does not: the represented values might be 32 and 100. `dynamic_renaming.py` correctly excludes that high singleton when forming canonicalization groups.

Canonicalization must use an invariant valid at the exact current phase. An external-entry invariant can be used at a compressed loop node after the boundary proof above; otherwise use the ordinary site invariant. Canonicalization is best treated as normalization of representation metadata within an edge, not as an additional machine operation or an additional zero-time source step.

## 4. A practical static version: allocate value lifetimes

Carrying arbitrary permutations to every source control occurrence can multiply the control graph. The inspected dynamic exploration reached a 1,500,000-node cutoff with 47,626 nodes still pending, while visiting only 449 underlying source sites. This is evidence of code expansion in that exploration, not a lower bound or a complete compiled candidate.

A more useful representation stores an allocation at each source control site. A logical register known to be zero need not own a dedicated slot at that site. Let `L_q` be the logical registers whose abstract mask is not exactly zero, and let `a_q : L_q -> {0,...,8}` be injective.

Define the full physical representation

```
Frame(q,R,P) iff
    R(r)=0 for every r outside L_q,
    P(a_q(r))=R(r) for every r in L_q,
    P(c)=0 for every physical slot c outside the image of a_q.
```

The last condition is essential. Graph coloring alone does not ensure that a newly allocated register starts at zero if unused slots can contain old garbage. The proposed compiler must retain this exact zero-unused-slot invariant. All-zero primary registers satisfy it for every allocation.

This partial allocation can always be completed to a full bijection sigma by assigning the remaining logical zero registers to the remaining physical zero slots. Thus it is a compact representation of the same role-renaming principle; the map among zero-valued fields is immaterial.

### Static allocation transfer theorem

Suppose a finite source macrograph is equipped with a proved source invariant, an allocation at every site, and one physical-vector operation for every feasible edge. Require the following exact edge contract for every source vector and every entire physical vector:

```
source_guard(R) and source_invariant(q,R) and Frame(q,R,P)
  -> Frame(q', source_effect(R), physical_effect(P)).
```

Require also the correct source successor, exactly preserved halt labels and a represented actual initial vector. Then the allocated macrograph simulates the original macrograph and has the same halting behavior. Induct on macro steps, applying the edge contract. Each complete move macro is known to terminate and its output equals the original loop output, so replacing the original loop by that macro preserves halting as well.

The transformation of each kind of edge is elementary:

* If an increment starts from a logical field known zero, use its **successor** allocation. Its slot is zero by the frame and edge contract. If the field is allocated at both endpoints, the continuous value lifetime uses the same slot.
* A positive decrement uses its **source** allocation even when its result becomes a known-zero field. The freed slot becomes physically zero. A known-zero decrement must follow the zero branch; it can be lowered directly as control or read any unallocated slot proved zero.
* An unaffected nonzero field retains its slot. Changes of allocation for fields that are zero on this edge are harmless because the old and new available slots are zero.
* A complete move uses the source field's allocation before the edge and the destination field's allocation after it. If they are the same slot, no data motion is needed. Otherwise the target physical slot must be proved zero and an actual terminating physical transfer moves the value and clears the old slot.
* If the two physical slots are equal, do not emit a physical self-transfer loop: it would diverge on a positive value. Erase whenever the assigned slots coincide, including a coincidence caused by coloring without explicit live-range union.

Both branches of one physical decrement test must use the same physical operand. A branch-dependent choice would be circular because the branch is not known before that test runs.

## 5. What finite allocation certificates can prove

The current certificate represents each slot as an affine expression in the nine source values and one constant component. Exact-value mask facts and the zero/positive decrement guard specialize these expressions. It symbolically applies the allocated operation, then compares all nine physical output slots with the expected target encoding.

Equality of these coefficient vectors is a universal identity, not a sample test. Positive-decrement subtraction is used only under a guard ensuring the natural register value is positive. The source data can be arbitrarily large; no bound of 31 is imposed on it. The mask class `>=32` overapproximates all such values and remains symbolic.

`allocation_certificate.py` checks the zero-unused-slot condition in both endpoint encodings, the zero destination of every retained physical move, injective allocations, initial zero-vector encoding, and the common decrement operand. The inspected artifact passes all 5,480 macrograph edges over 4,520 source sites, with these physical recipes:

| Recipe | Count |
|---|---:|
| Increment | 1,631 |
| Zero decrement branch | 961 |
| Positive decrement branch | 961 |
| Control-only source edge | 957 |
| Retained physical move | 372 |
| Erased data move | 598 |

The 598 erased moves consist of 596 nontrivial coalescences and two zero-source cases in the then-current allocation. They are erased register macro occurrences, not 598 binary machine states.

A complete certificate packet should also check color bounds `0 <= color < 9`, all original mask transfer inclusions, all extracted macro boundary facts, and the direct macro-effect inclusion in the target masks. It must identify actual halt sites explicitly: a source node with no retained outgoing edges must not automatically be treated as a halt merely because all branches were filtered out.

This affine check is independent of the heuristic choice of coloring in the important sense that the heuristic may be wrong and the final edge equations will reject its output. It still shares the extracted source macrograph and masks, so those inputs need their own certificate.

The subsequently written independent `audit_role_inputs.py` supplies that finite-input audit. It first unfolds the 203-node shared decoder DAG and compares all 6,460 instruction leaves, including every opcode and operand, with the literal source's 6,459-node tree. It uses a separately implemented abstract transfer function and checks all 8,391 original source cases: 8,384 feasible nonhalting transfer inclusions, one actual halt case and six infeasible guards. The actual all-zero initial vector is included. It checks all 972 extracted move occurrences for distinct operands, literal decrement/increment/continue shape, exact zero exit and absence of external interior entries. Exactly 970 have certified zero destination at external entry; each compressed macro's output masks are included in its target phase masks. `role-input-audit.json` records a PASS and source hashes. The general soundness argument for these masks is induction on actual source steps, using the elementary soundness of the abstract transfer rules. The source decoder's identification with the Lean semantics and new binary compilation remain separate from this finite annotation audit, and no new Lean-kernel verification is inferred.

## 6. Eliminating zero-time edges without losing halting reflection

Erasing data motion does not mean a literal binary Turing machine has a zero-time jump. A mandatory-L/R transition cannot preserve both head and tape in one move. The compiler may fuse a role/control change into an adjacent transition, or realize it by a positive segment whose exact effect is proved. A claim of a single free no-op would violate the machine model.

Three sound proof styles are available.

### A. Keep positive binary segments

Use an abstract step boundary only where the compiler supplies a segment of at least one actual binary transition. Then instantiate the repository's generic `RuntimePerm252.PositiveSimulation` with the allocated state/tape relation. Its active-endpoint, actual-halt and no-accidental-stop obligations give halting equivalence. This is the simplest proof if the backend already emits actual control-routing transitions for an erased source move.

### B. Normalize deterministic epsilon chains

Treat erased moves as deterministic epsilon edges of the finite compiled control graph. Resolve each chain to a retained operation or to an actual halt. If a chain is acyclic, ordinary finite graph traversal supplies a bound on its length and allows it to be fused into the next retained operation.

Do not discard an epsilon cycle as an unreachable or invalid program. An infinite sequence of zero-destination source moves can represent genuine nonhalting. Each original move still takes finitely many positive source steps, including its final test, so a cycle consisting only of such macros cannot reach a halt. Map a detected epsilon cycle to a real nonhalting binary sink, whose states and transitions must be charged to the machine, or retain a physical transition on that cycle. A single binary state with both branches writing the read symbol, moving right and returning to itself is one possible sink, if a new state is necessary.

After chain normalization and cycle handling, the retained graph has positive binary progress and can use the generic simulation theorem. A small finite epsilon subgraph is an exact certificate; bounded execution is not needed to guess whether epsilon closure terminates.

For the frozen 598-erasure allocation, `epsilon_progress_audit.py` independently checks this graph directly from the affine certificate records. Treating both erased moves and ordinary control-only edges as epsilon gives 1,555 edges: 598 erased transfers and 957 control edges. Every epsilon source has exactly one outgoing edge in the full graph. There are no epsilon cycles, and the longest epsilon chain has length four. The explicit rank is the remaining chain length: among the 4,520 sites, ranks 0 through 4 occur 2,965, 1,243, 251, 60 and 1 times, respectively. The checker verifies `rank(source) = rank(target) + 1` on every epsilon edge and records the exact source-certificate digest in `epsilon-progress-audit.json`.

This proves that zero-step normalization for this exact abstract graph has finite progress and needs no divergent-cycle sink. It does not determine the binary implementation or its state count. Any later recoloring, graph rewriting or alternative lowering requires retaining or rechecking the corresponding rank fact.

### C. Allow zero segments with a ranking function

Generalize the positive simulation by allowing a segment length k=0 only when an explicit natural-valued rank strictly decreases. Positive segments decrease a proposed finite remaining binary halting time; zero segments decrease the secondary rank. Lexicographic well-founded induction on `(remaining_time,rank)` then proves halting reflection. This supplies the missing anti-stuttering argument without a uniform global clock bound. If no such rank exists because of an epsilon cycle, use the cycle treatment above instead.

Canonicalization of equal-zero roles should normally be done inside representation normalization, so it introduces no additional source transitions and requires no separate progress accounting.

## 7. What is still needed for a state-count claim

A smaller register graph is not automatically a smaller binary transition table. Per-occurrence register allocations can destroy DAG sharing that made the original program compact. The actual backend must emit and minimize the whole table, count all working states and provide an actual blank initializer. The new selector paths and register layout require new frame/instruction proofs unless literal table identity permits reuse.

The final compilation experiment measures this cost directly. The 203-node original decoder DAG becomes a 917-node allocated DAG; deleting all 598 explicit no-op leaves reduces it to 778 shared nodes. The independent `audit_compacted_control.py` reimplements path arithmetic and checks all 5,999 guarded successor cases, the initial control entry, the unique halt, preservation of increment/decrement operands and clean unconsumed path suffixes. Thus the compaction has a concrete finite source-control certificate, rather than a presumed equivalence from the new tree's appearance.

Under the same pinned Mira backend and its fully charged compact zero-register initializer, the original source compiles to 314 working states and the allocated/compacted source to 888 working states. Their saved tables pass the backend's full affine site diagnostics and literal initial-frame replay. These are comparison controls, with no newly checked Lean simulation or internal consistency endpoint. They are not smaller candidates: this tested role-allocation route saves unfolded data transfers but increases binary decoder cost substantially. A different allocation or backend would need its own total-table measurement.

The useful source invariant in this experiment was computed from the original all-zero root. It cannot automatically be applied to arbitrary dirty roots allowed by the Foundation semantic-seed method or by `DirtyReset254`: those states might violate the zero-destination and exact-value premises. Any attempt to combine a larger startup family with this optimized runtime must reestablish the relevant source invariant for that family.

Once a new binary machine is proved halting-equivalent to the original zero-root source search, its consistency equivalence can reuse the old native/ZF/ZFC argument unchanged. That final composition is straightforward; generating a genuinely smaller table and proving its full binary simulation are the remaining substantive obligations.

## 8. Focused alternative if dynamic maps expand too much

One can seek a single decoding map per source control vertex modulo the stabilizer of equal-valued fields. Each ordinary edge asks that the map be preserved up to such harmless permutations; an erased move asks for the corresponding transposition. Around a control cycle, the composed permutation must act only on fields known equal, or some physical transfer/reconciliation must be retained. This is a finite constraint problem on maps and selected move edges.

Static live-range allocation with explicit zero-unused slots is one concrete way to avoid carrying all possible permutations. Other selective schemes can keep fixed conventions at joins, erase only moves whose maps reconcile there, or optimize small regions where two role swaps cancel. Any added reconciliation cost belongs in the emitted table comparison. These are compilation proposals, not uncharged semantic shortcuts.
