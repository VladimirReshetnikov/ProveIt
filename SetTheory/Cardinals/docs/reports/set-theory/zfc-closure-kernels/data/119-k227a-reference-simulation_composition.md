# From the K230 theorem to a smaller literal machine

## The conclusion and its meaning

Let `M` denote the exact optimized binary table, with its declared initial state, blank symbol 0, two-sided tape, and a distinct halt state. Let `P` be its exact decoded structured source. Let `P230` be the source literally defined by `p230_tab` in the pinned K230 checkout. The appropriate proof chain is

\[
\begin{aligned}
 M\text{ halts on blank tape}
 &\iff P\text{ halts from }R_0\\
 &\iff P_{230}\text{ halts from }R_0\\
 &\iff \operatorname{StandardZFC}\vdash_{\mathrm{TC}}\bot.
\end{aligned}
\]

The initial logical register vector is

\[
 R_0=(3,0,0,0,3,0,0,0,0).
\]

Negating the chain yields nonhalting if and only if ordinary syntactic consistency of ZFC. No premise asserting consistency of ZFC occurs in the biconditional. A proof of the biconditional neither proves its nonhalting side nor proves `Con(ZFC)` separately.

The first equivalence is supplied by exact blank initialization and universal instruction simulation of the final table. The second is supplied by source identities and exact source reconstruction. The third is the inspected K230 source theorem, through `Main230.prog230`, `Seed230.seed230_iff_thm`, and `Consistency230.thm230_iff_standardZFC`. A direct final-table runtime proof makes a separate conditional state-fold invariant unnecessary for this chain.

## A precise progress lemma

Consider a deterministic source transition system with a designated successful halt predicate and a deterministic TM that has no outgoing transition from its halt state. Let `I(s,t)` relate a reachable source configuration `s` to an interpreter boundary configuration `t` of the TM. Assume the following facts.

1. An exact finite blank run reaches some `t0` with `I(s0,t0)`.
2. Each reachable source configuration is either at its designated halt or has a next source step. There are no other stuck cases.
3. If `I(s,t)` and `s -> s'`, then there are an integer `k >= 1` and a configuration `t'` such that `t ->^k t'` and `I(s',t')`. Every transition of that block is a genuine transition of the literal TM. In particular, there is no hidden interior halt.
4. If `I(s,t)` and the source is at its designated halt, then the literal TM has a finite run from `t` to its halt state.

These conditions imply halting equivalence.

For source-to-TM halting, induct on the number of source steps before the source halt. Concatenate the finite TM blocks, then the final halt block, and prepend the finite bootstrap.

For TM-to-source halting, suppose the TM halts in `h` steps from a related interpreter boundary. If the source is already at halt, the claim holds. Otherwise condition 3 supplies a block of positive length `k`. The block cannot run beyond the observed TM halt: determinism would force its purported continuation to execute a transition from a halt state. Thus `k <= h`, and induction on `h`, with the smaller remaining bound `h-k`, gives a source halt. This proves the reverse implication without assuming a time bound for an individual source instruction, without assuming a model of either theory, and without invoking an infinite-run compactness principle.

The same lemma applies to a direct fold from one finite TM to another. In that application, every reachable old TM row must have a positive simulated new block, and the old terminal state must correspond to a new terminal state. An externally asserted bit guard is a premise of that argument until proved on all reachable configurations. A final-table universal interpreter proof is an independent route around such a premise.

## What the universal instruction proof quantifies over

The interpreter frame, in the inherited labels used by the ordinary checker, has state 96, a 1 immediately to the left, and right tape

\[
 Q\;0^{n+64-|Q|}\;1\;B(v_0)B(v_1)\cdots B(v_8)B(a)B(A),
 \qquad B(v)=0\,1^{v+1}.
\]

The tape is zero outside the displayed finite words. Here `Q` is a leaf path, `n` is an arbitrary natural extra gap, the nine primary values are independent arbitrary naturals in the stated physical register order, `a` is an arbitrary first spare value, and `A` is an arbitrary finite list of further spare values, including the empty list. Specifying the first spare separately guarantees the nonempty extension used by the invariant.

The checker proves one contract for each non-decrement leaf and two contracts for each decrement leaf. The two decrement cases are exactly value 0 and value `1+x`, with `x` arbitrary. Their union covers every natural register value. It compares the entire normalized output tape, the output state, the source successor path, and the net head displacement. It also proves a strictly positive total number of literal transitions. Increment appends a spare block of value 1; the induction invariant therefore continues to have a nonempty spare tail.

The symbolic rules have elementary induction proofs:

- A literal step is one row lookup, write, and head move in the supplied table.
- A unary self-loop over a run of length `v` is justified by induction on `v`, including `v=0`.
- A list traversal is justified by structural induction on an arbitrary finite list after verifying the one-block schema with arbitrary untouched left and right contexts against the actual table.
- Normalization uses equality of finite words. The only nontrivial list identity is `C(A)1 = 1B(A)`, where `C(v)=1 0 1^v`; its empty and cons cases are elementary word equalities.

The affine duration variables describe unbounded natural values and the actual total width of the arbitrary spare list. The list itself remains a symbolic list, so two tails are not identified merely because they have the same width. A construction budget of 4,000 symbolic rule applications per site bounds the effort to find and check the finite derivation. It is not a bound on an actual TM run, a register value, a gap, or a spare-list length.

Testing all sites at a finite set of concrete register values would not imply these quantified contracts. Visiting every literal row would not imply them either. The mathematical work is done by the sound symbolic induction rules and by exhaustive coverage of the finite set of sites and decrement branches.

## Closing the source-to-frame invariant

The runtime contracts are phrased for exact leaf paths. A reachable source instruction pointer can instead contain fewer bits, interpreted with trailing zeros, or have extra zero bits beyond the leaf depth. The source invariant must account for that representation.

For a finite acyclic complete source tree, every pointer walk reaches a leaf within its height. The generic `RMEquiv.no_stray` theorem says that after any finite reachable source run, all pointer bits beyond the depth of the selected leaf are zero. Therefore the stored pointer plus the following zero gap can be rewritten as the exact selected leaf path followed by a new zero gap. A depth bound of 40 and an available frame span at least 64 make this rewriting valid for every reachable source configuration.

The complete invariant used in K230 is of the form

\[
 \exists P,R,k,A\ne[],\quad
 \operatorname{rm\_run}(P_{230},N,([],R_0))=(P,R),\qquad
 |P|+k\ge64,
\]

with the TM at its interpreter boundary and tape `1 | P 0^k 1 B(vregs(R) ++ A)`. The same induction applies to a new source after its finite well-formedness, register bounds, and depth bound are checked. For exact source rewrites with no escaping break or continue, preservation of the structured semantics gives the required source halting equivalence for the actual `R0`.

The posttest edit is particularly simple. At each of its four exact occurrences,

`((CD6,(CI5,CC2)),CI5)` becomes `(CI5,(CD6,CC2))`.

For arbitrary input values `R6=n`, `R5=m`, both fragments terminate normally with `R6=0`, `R5=m+n+1`, and every other register unchanged. Each takes `3n+2` primitive source steps. The base `n=0` takes two steps; the successor case takes three steps to reduce to the induction hypothesis with `(n,m+1)`. Their boundary escape numbers are both zero. The separate exact source certificate names all four occurrences and preserves the source outside them.

## Exact upstream provenance

The pinned K230 commit is `3142e4dd980f0be12f4abb636c4ae2528afc17eb`. The independent parser `check_k230_literal_bindings.py` reconstructs all 5,125 primitive leaf occurrences from the 5,124 literal cons entries in `coq/tm/Prog230.v` and compares every path and opcode with `machine/sites230.json`. It also recomputes every entry of the three exported height/break/continue tables. The root has height 40 and escape bounds zero. The 212 distinct source DAG nodes comprise 189 cons subtrees and 23 distinct primitive leaves.

Separately, the same parser reads all 460 transitions from `coq/tm/Table230.v` and compares them with `machine/k230.tm`, validates the table wrapper and initial state, and checks that no target is changed by bounded-state clamping. This is a stronger literal binding check than merely noticing matching hashes in a comment. The companion source audit validates the 101 pinned local proof-source hashes and inspects the exact endpoint chain. Neither check is a fresh Rocq build.

The frozen upstream table reaches its initial interpreter frame in 408,419 literal steps. The optimized tables currently verified by the parent runtime driver reach the same mathematical seed and 181-cell gap in 409,835 steps; their inherited runtime state is 96, corresponding to upstream state 84. These are different finite computations and must not be interchanged. A changed bootstrap must be checked from the changed table bytes, even if its final logical seed agrees.

At the time of this audit, the parent receipts `runtime228.json` and `runtime227.json` both report all 6,656 universal site cases complete, minimum actual block length 13, and the expected final-table transition counts. The 227-state source is a further exact structural rewrite with the same 5,121 primitive occurrences. These observations refer to their recorded table/source hashes; changing either input requires checking the corresponding binding again.

## Ordinary ZFC formalization and the remaining formal-artifact boundary

The halting predicate of a fixed finite binary TM is arithmetic. One may code a finite configuration by a state, signed head position, and finite tape word; after `t` blank-start steps only finitely many cells can have been visited. Executing one transition and checking a proposed finite run are primitive recursive operations. Finite source trees, nine-register vectors, finite formula strings, finite axiom-instance witnesses, and finite proof trees likewise admit elementary natural-number codings.

Define

\[
 \operatorname{Con}(\mathrm{ZFC})
 :=\neg\exists p\,\operatorname{Proof}_{\mathrm{ZFC}}(p,\bot),
\]

where a proof certificate includes the syntactic witnesses needed to identify schema instances. The inspected `StandardZFC` is the ordinary extensional ZF presentation with Foundation and Choice, and `⊢TC` is finite classical first-order derivability from a finite list of its axioms. Relating another conventional ZFC proof coding to this one requires explicit finite syntactic reencoding of logical rules and axiom instances. It requires no semantic soundness or reflection assumption.

The added optimization proof uses only arithmetic on finite objects, induction on naturals and finite lists, finite source identities, and the ordinary finite-refutation transformations already inspected in K230. ZFC supports these constructions and induction arguments. Thus the ordinary mathematical argument can be expressed as a ZFC proof of the displayed equivalence. There is no added arithmetic representability hypothesis: the finite codings and their basic properties are definitions and theorems to formalize, not assumptions about consistency, standardness of models, or the truth of ZFC.

A completed Rocq theorem is evidence about an exact formal statement in that proof system. One should not justify ZFC provability by a sweeping claim that all of Rocq's type theory is sound in ZFC; that general claim is unnecessary here. The relevant finite-syntax argument can be read and formalized directly in ZFC. Conversely, the existence of a Rocq declaration alone does not supply a separately encoded object-language ZFC or PA derivation.

The new ordinary induction checker and source proofs establish a conventional mathematical route from the optimized bytes to the frozen source theorem. They are not a newly compiled Rocq endpoint for the optimized table. A future kernel formalization would mechanize the same positive-progress lemma, register/list frame invariant, exact source transformations, startup computation, and literal table binding; it would not need a new equiconsistency conjecture or a new set-theoretic principle.

## Seven-zero source paths and the marker scanner

In the upstream canonical labels, zero transitions follow

\[
 2\to3\to5\to9\to15\to23\to34\to50\to75.
\]

All eight arrows write 0 and move left. Every state before 75 resets to state 2 and moves left upon reading 1. State 75 moves right across zeros and, at the next 1, moves right into dispatcher 84. Consequently entry at state 2 detects eight successive scanned zeros, entry at state 3 detects seven, and entry at state 5 detects six. Direct entry into one of the later states, or temporary zeros written while performing a primitive operation, changes the context relevant to the bound.

A maximum zero run of 7 in the static source is therefore not by itself a proof of failure or safety. The actual scanner entry and temporary pointer geometry matter. Once a spurious marker is detected wholly inside the pointer, increasing the external frame gap cannot change the already determined local transition sequence. A different marker format would require redoing the initializer and interpreter contracts. The appropriate acceptance criterion is the complete universal site proof for the exact candidate. The presently verified 227-state source restores the maximum static run to 6.

