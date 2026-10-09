# Independent audit of the persistent raw-elimination theorem

Audited `word_research/persistent_elimination_theorem.tex`, 9 October 2026.

## Verdict

The mathematical size theorem is sound under its stated raw-only, one-binding-per-original-generator hypotheses. No correction to the recurrences or numerical constants is required. The ordinary SLP export bound is also valid.

## Points checked

1. **Unique context path.** Saturated raw occurrence counts distinguish zero, one and at least two, including repeated references to the same child. A singleton occurrence therefore gives a unique path in the unfolded word. Signed traversal reverses child order and negates handles correctly; the saved prefix siblings in descent order and suffix siblings in reverse descent order recover the exact raw words L and R.
2. **Pivot formula.** From L x R=1 one obtains x=(RL)^(-1); from L x^(-1) R=1 one obtains x=RL. The formal inverse order is correct.
3. **Acyclicity.** A saved sibling with raw count zero has no dependency path to the current live pivot, including through earlier mutable bindings. The new image contains only such siblings and fresh concatenations. A new cycle would have to traverse the new binding edge and return to its source, which is impossible.
4. **Serial semantics.** The current image contains no pivot. Its value is unchanged when the pivot binding is installed, and evaluation of every old root afterward is exactly the substitution homomorphism applied to its previous raw value. Earlier bound terminals update through shared dependencies as required by serial substitution.
5. **Depth decomposition.** The definition of D_i deliberately deletes every binding edge. A full dependency path encounters at most i bound terminals, since there are only i and acyclicity prevents repeated vertices. Splitting at these edges gives at most i+1 binding-free segments, so H_i<=(i+1)D_i+i. This remains true when a new image references an earlier terminal or an old historical donor vertex.
6. **Balanced-image recurrence.** There are at most H_i sibling handles. A fresh balanced tree over these handles has at most ceil(log2 q_i) concatenations on any path before it enters an old handle. Thus D_(i+1)<=D_i+ceil(log2 max(2,A_i)). Bindings themselves do not contribute to D_i.
7. **Explicit constants.** The estimates A_i<=T_i^2(1+6 log2 T_i)<=T_i^5 and ceil(log2 max(2,A_i))<=6 log2 T_i hold for T_i>=2. The induction for D_i and the sums for S_k are correct.
8. **Length bits.** A binary/unary acyclic graph of full height H unfolds to at most 2^H terminal leaves. Raw inversions preserve length, and bindings are unary. This proves the claimed length-bit bound for historical vertices as well as retained roots.
9. **Ordinary export.** Process the underlying unsigned DAG in dependency order, storing values in both signs. Each unbound terminal contributes at most two terminal nodes, each concatenation at most two concatenation nodes, and each bound terminal only aliases previously exported image nodes. All child references point backward in export order; there are at most 2S_k nonzero nodes. The presence of mutable references to later-allocated image vertices in the source is irrelevant after a topological reorder.
10. **Controlled family.** The displayed recurrence A_(j+1)=A_j A_j^(-1), B_(j+1)=B_j^(-1)B_j gives both context lengths 2^(j-1) and retained relator length 2^k+2. The pivots remain raw singletons. This family stresses representation, not knot recognition.

## Minor accounting clarification recommended

Let M be the number of original relator slots. The fixed list can be much larger than S_0 if roots repeat. Charge O(M) graph operations once for reading/validating or exporting it and O(M log(S_k+r_0+2)) output bits for its identifiers, in addition to the circuit bounds. The draft already exempts this list in its storage statement and mentions root scanning, but an explicit M term removes any ambiguity in the total encoded-complexity claim. Adaptive donor discovery additionally scans the retained slots for each candidate generator or stores an equivalent index.

This is a bookkeeping clarification, not a flaw in the polynomial representation theorem.

## Scope remains necessary

The proof fails if “zero occurrence” means zero after free reduction, since cancellation could hide dependency paths. It does not automatically compose with repeated normalizations, insertion of new generators, primitive-power quotients, or a search over many elimination orders. End-of-block ordinary export permits a single separately charged compressed normalization operation. Its own polynomial output-size bound must be included before beginning another block.

The cited Ennes--Maria v2 source is available at https://arxiv.org/html/2507.11406v2 (31 December 2025). Its introductory arithmetic model is a unit-cost RAM for bounded-bit integers. The persistent theorem's independent raw-count and graph bounds do not rely on transferring that source's arithmetic model.
