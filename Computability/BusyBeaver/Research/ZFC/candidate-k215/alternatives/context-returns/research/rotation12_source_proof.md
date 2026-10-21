# Exact source equivalence for the recompiled 215-state companion

The literal source and machine audited here are:

* Source SHA-256: `c85089b913dcf446da5039843a43c15129efe88c8ee47a673b5b74600ae42ace`.
* Native table SHA-256: `7dafe445beb74f66b24d4e540136b5a47d0dfc6c1b877dcb8edce1526a608537`.
* Pinned baseline: ProveIt commit `75716498437bfc7291d5900cab2983a11fd54bac`, `candidate-k215/sites215.json` and `candidate-k215/k215.native.tm`.

The exact audit is `audit_rotation12.py`; its output is `rotation12_audit.json`. It does not trust the source optimizer or the allocator to establish source equivalence.

## A one-line source construction

In the baseline tree, take the node at path

    11010010011101010110011100

and write it as `((A,B),C)`. Replace that node by `(A,(B,C))`. This reconstructs every byte of the emitted `sites.json` using the packet's canonical JSON serialization. No other node is replaced. In particular, no primitive operand and no `CB`/`CC` control depth changes.

The three factors are closed, nonhalting source blocks. Their leaf counts are respectively 539, 380 and 123. Consequently both parenthesizations execute the same sequential composition A;B;C, including the same internal loops. This is an ordinary compositional proof of the rewrite's validity.

There is also a direct independent certificate. The 4,751 leaves, in ordinal order, have exactly the same primitive labels and operands. Two graph resolvers—one using binary successor/cut arithmetic and one walking ancestor intervals—both produce the same instruction graph for the old and new source. This includes both guarded successors of every decrement, not merely the default fall-through successor. Each arithmetic resolver checks all 6,176 relevant successor cases and their no-stray-suffix conditions.

## All-natural equivalence lemma

Represent a source configuration by an instruction ordinal i and a tuple v of nine natural registers. For every i and every v, the old and new source have the same next configuration, or both halt. Proof: their resolved instruction effect and every guarded target are equal. For an increment, the same component of v is incremented. For a decrement, the same natural register selects the same zero/positive branch and receives the same update. Branch and continue instructions have the same identity effect and target. The halt ordinals coincide.

Induction on the number of source steps gives identity of all finite source trajectories. It follows that the two source programs halt on exactly the same initial register tuples. This statement quantifies over all natural values; it is not an inference from testing a bounded collection of inputs.

The pinned K215 source calibration therefore transfers verbatim: all-natural command soundness, finite derivation compilation, candidate draining, and cofinal padding above any startup cutoff have exactly the same source executions. No new object-level proof calculus is needed for this companion.

## Binding to the literal 215-state binary table

The table has 215 working states, all 430 state/symbol rows, and a distinct halt target 254. The fresh runtime receipt is bound to the exact table and source hashes above. It proves all 6,176 guarded primitive cases, with independent natural primary register values, arbitrary natural gap, arbitrary nonempty finite spare list, and the complete zero exterior. The separate mathematical runtime checker uses induction over unary runs and spare-list length; its construction bounds do not bound machine execution or register values.

The audit independently replayed all 95,740 steps of the supplied blank startup using a separate table reader and simulator. It reconstructed the resulting complete frame directly, rather than relying on the startup parser's report: dispatcher 84, head -8, root program counter, header cell 57, extra gap 1, logical registers `(4,0,0,0,0,0,0,0,0)`, forty unit spare blocks, and exactly 95 one cells with zero elsewhere. The source theorem applies to that seed. The audit also checked that the runtime receipt covers every source guard exactly once and matches the current checker/helper hashes.

Combining the source equivalence lemma, the pinned source calibration, this quantified runtime proof, and the literal blank prefix gives the ordinary mathematical theorem, formalizable in ZFC,

    M halts on the blank tape iff ZFC has a finite contradiction proof.

Equivalently, ZFC proves that M does not halt on blank input iff Con(ZFC), for the same syntactic consistency predicate used by the inherited calibration. No proof-assistant kernel verification was performed in this work.

## What is materially different

The source still has 202 distinct subtrees and 4,751 primitive occurrences, but 1,042 leaf paths change. The sum of all leaf path lengths decreases by 416 and maximum source depth decreases from 47 to 46; maximum consecutive zero run remains 6. The literal transition table differs from the baseline in 191 rows.

The rooted binary transition graphs are not related by a state renaming. A short invariant witness is the edge-label word `000000`: starting at the distinguished initial state and following six edges labeled zero, the old and new tables produce different write/move actions at the sixth edge. In the baseline this is `(write 1,right)`; in the new table it is `(write 0,left)`. An isomorphism preserving the start state, read symbols, write symbols and directions would preserve every such action sequence. The witness is a graph certificate; it need not itself be the read-symbol sequence of a physically realizable tape run.

This companion is a recompiled implementation of the inherited calculus, with a different source bracketing, decoder allocation and runtime provider. It is not a reduction to 214 states, nor a new foundation for set theory. The separate transfer-plus-cache source and membership-atom alarm results explore changes to the calculus interface and consistency witness.
