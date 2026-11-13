# Structured model mask of standard length

For any IΣ₁ model and any support word, define a radix-2^67 digit recipe: slot
1063 is `2^67−4`, slot 1 is `2^67−1`, and all other slots are either
`2^67−2` or `2^67−1` according to the corresponding bit of the support word.
The first theorem constructs a block with exactly these digits for each
standard natural length, using external Lean induction over that length and
`Blocks.blocks_succ`. The specialized theorem constructs a block of length
8,807, proves its three-way digit classification, and proves the ordinary
origin digit when the support word's zeroth bit is explicitly 1.

This is an existence theorem for a structured model block, not an identity
with the retained MC literal, the graph's mask port, or a proof in PRA. The
support word remains a parameter; identifying it with the finite compact44
support and proving that the retained MC equals the constructed block are
separate tasks. The induction is external Lean induction on a standard
natural, not an internally formalized object-theory construction. No graph,
NoCarry premise, coefficient bound, machine simulation or consistency
equivalence follows from this packet alone.

The two initial exploratory attempts (sessions 26941 and 47843, both exit 1)
tried internal Σ₁ definability of the proposed digit function and exceeded the
200,000-heartbeat limit. Session 16570 exited 1 because model-valued variables
in the target defaulted to naturals. Their source and logs are retained.
Sessions 35407 and 46530 exited 0 after using external induction and explicit
model-type annotations; the latter also checks the exact digit recipe.

The replay uses the independently audited 342-module author/peer endpoint
successor and its source/object checks, including reruns of that provider audit
before and after. It records matching objects, direct imports and axiom reports.
The provider's scope does not include full dynamic or package-transitive
ancestry. Its sampled monitor is not a hard whole-process-tree quota.
