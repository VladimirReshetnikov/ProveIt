# Further research questions and topics

Companion agenda to Section 12 of `paper/article.pdf`. Each target requires a size bound, a discovery algorithm, and checked implementation evidence.

## 1. A sharper free-product string kernel

Can direct compressed reduction in $C_2*C_3$ reduce the $O(s^2(B+1))$ allocation envelope while improving worst-case equality cost? One concrete target is an $O(s^2)$-size normal-form representation with deterministic prefix queries that avoid a separate binary search over $B$ bits. The analysis must include all substrings and inverse nodes accumulated across the whole DAG.

## 2. Representation-insensitive performance

How do equivalent balanced, skewed, reassociated, and deliberately nonshared input grammars change the cost of recognition? The positive sleeve benchmark favors exact sharing. A useful next corpus should preserve the represented braid while varying its parse independently, record equality splits and peak assertions, and identify a normalizing or balancing transformation whose own cost does not erase its benefit.

## 3. Smaller proof objects

Can discovery discard equality scratch nodes and emit only the subgrammar needed for replay, with a proved near-quadratic or better certificate-size bound? Any compaction must preserve exact references and must not reintroduce exponential duplication. Compare producer-arena size, reachable proof size, serialized bytes, and fresh verifier allocation separately.

## 4. An independently verified equality foundation

Can the finite-factor reduction and cyclic-conjugator lemmas be formalized, followed by the indexed split-and-compaction equality kernel? An intermediate milestone is a second structurally different equality backend used only for audit. Sharing the same kernel on producer and verifier is practical, but it remains the largest common algorithmic dependency.

## 5. Compressed moves that reveal new singleton cuts

Can certified context-safe braid equalities, cyclic cancellation, and endpoint descent update occurrence multiplicities and interval projections without expansion? The goal is to expose singleton cuts hidden by a compact sequence of elementary moves. A result must bound the number of moves and aggregate grammar growth; repeated local improvement alone does not give such a bound.

## 6. A broader exact family of easy leaves

Which wider braid families admit polynomial-in-SLP-size closure recognition with independently replayable certificates? Reducible or explicitly decomposed braid families are natural candidates, provided their boundary identifications are retained. Every additional exact easy-leaf family can be removed from $\mathcal E$ in the hybrid complete-bound theorem, improving the exceptional parameter without changing its proof pattern.

## 7. Four-strand input as a controlled next case

What additional information beyond exponent and a virtually free quotient is needed for a useful four-strand compressed backend? The concrete target is a certified subclass with an exact membership and decision procedure, not a claim that the three-braid constant-core criterion simply generalizes. The supplied unresolved four-strand example is a minimal interface test for this extension.

## 8. Presentation-dependent minority parameters

How much can $\kappa_{\mathrm{exc}}$ decrease under a bounded, certified set of Markov and braid moves? This parameter is attached to a presentation and its certified decomposition, not claimed to be a knot invariant. Prove either useful approximation guarantees under a restricted move system or obstruction families showing why a proposed local system cannot achieve them.

## 9. A certified diagram-to-grammar producer

Can the general diagram pipeline produce compact braid words and a proof of their closure equivalence, while preserving compression during simplification? The relevant measure is the sum of discovery time, proof size, and replay time. A small final grammar is not enough if an exponentially expanded intermediate object was needed to find it.

## 10. Marked collars and geometric hierarchies

Can braid-encoded collars or parallelity regions inside a geometric hierarchy be replaced by compressed certified objects while retaining meridian, longitude, and attachment data? A successful interface would connect the present exact algebra to the geometric program. An unmarked closed-braid classification is insufficient for substitution into an arbitrary three-manifold boundary pattern.

## 11. An end-to-end exceptional-parameter theorem

Find a natural nontrivial diagram class for which a certified polynomial-size transformation always yields $\kappa_{\mathrm{exc}}=O(\log^2 n)$. A stronger universal statement would meet the general goal, but even a precise structural class beyond planted connected sums would be meaningful. The theorem must describe how the transformation is discovered, not merely assert the existence of a favorable representation.

## 12. Fallback and budget integration

Wire the verified exceptional leaves into the maintained complete backend with a shared global resource ledger and preserved child certificates. Measure crossover thresholds for explicit versus compressed leaves and verify that a fallback timeout never changes an unresolved overall status into an affirmative one. This is an implementation milestone, not a new mathematical assumption in the hybrid bound.

## 13. Independent nonplanted evaluation

Build a reproducible corpus from actual grammar-producing project workflows, rather than only powers and known conjugates. Keep explicit-input and compressed-input populations separate. Report unsuccessful decompositions, no-progress overhead, certificate size, replay cost, and whole-pipeline cost. An exact algebraic stress test and an operational knot benchmark answer different questions and should remain separately labeled.
