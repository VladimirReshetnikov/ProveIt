# Independent complete review of eager Tree occurrence flow

**PASS.** The frozen transformation preserves exactly the represented natural
`(program,argument,output)` triples for each external row count N>=1. Its
complete source costs27N²+124N+9 operations, saving N-1 additions from the
actual parent, with3N²+19N natural witnesses,23N+3 residuals and exact degree4.
It does not preserve witness tuples, canonical or unique fibers, or yield a
fixed-arity universal polynomial. No author change was requested.

Reviewed author files:

| File | SHA256 |
|---|---|
| [Source](eager_tree_occurrence_flow.py) | `0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c` |
| [Receipt](eager_tree_occurrence_flow.json) | `10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d` |
| [Proof](eager_tree_occurrence_flow.md) | `ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9` |

The actual corrected kernel is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py`,
SHA256 `636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52`.
I read the entire kernel and new source, including loading, tracing, pruning,
finalization, symbolic identities, public guards and fixture generation. The
historical kernel's `main` suite was neither called nor rerun.

## Independent graph and semantic proof

Write A_ij for the sum of the three slot selectors from row i to row j.
The natural tag sum and pointer-list sums force actual0/1 selections with
the prescribed number of premise slots. The flow equation is

    mu_i = [i=0] + sum_j A_ji*mu_j.

Therefore mu_0>=1, and each selected edge i->j gives mu_j>=mu_i. Every
root-reachable vertex has positive mass. Around any directed cycle the edge
inequalities force equal masses. If the cycle contains the root, the root
injection is an extra positive term, a contradiction. Otherwise choose a
root path first entering a simple cycle; its last edge contributes positive
mass in addition to the incoming cycle edge, again contradicting equality.
Thus the reachable subgraph is acyclic. Multiplicities of repeated premise
slots are counted and cannot weaken this argument.

The retained local rows are exactly the five eager application cases. Natural
tree codes split uniquely into leaf, stem and fork, and the selected case's
pointer lookups impose precisely its ordered premise triples. Induction on
the reachable DAG consequently proves the claimed root application.

For an explicit parent certificate at the same N, preserve the reachable
local rows and pointers, and assign heights recursively by one plus the sum
of selected child heights. Replace all unreachable rows by the valid leaf
`x=y=0,z=1,h=1`, tag0, zero pointers. Its decomposition fields are
`a=b=c=u=v=0,d=e=q=2,j=4,k=8`. No reachable pointer targets an erased row.
Every old residual then vanishes, and the root's external triple is unchanged.
This is an existential inverse that may alter many witnesses.

Conversely, the parent's height equations imply h_i>=1 and strict height
decrease along every selected edge. The whole graph is acyclic. Count its
root-to-row paths, including the empty root path and all slot multiplicities;
these finite natural counts satisfy the new equations, with zero counts on
unreachable rows. This proves the forward direction at the same N.

The natural domain is essential. Even the bare graph system A=[2],mu=[-1]
has a signed solution with a reachable cycle. No signed or real computation
theorem follows from polynomial evaluation on those domains. Nor must every
accepted natural mass vector be the minimal root path-count vector:
unreachable circulations can feed reachable vertices. The author's proof
correctly asserts only mu_0>=1 at arbitrary zeros and uses literal path counts
only in the forward construction.

The independent checker additionally constructs a full valid flow certificate
for the finite root `I(omega)=omega` with an unreachable fake `omega(omega)`
cycle of mass2. Its two outgoing calls feed the root, making **mu_root=5**.
All new residuals vanish; deleting the unreachable component and rebuilding
heights restores a parent zero at the same N. This verifies the distinction
between feasible flow and minimal occurrence counts using the actual kernel,
not only an abstract matrix. It is not a counterexample to the author's scope.

## Complete source, polynomial identity and costs

The independent helper implements the entire kernel schedule by hand from
its read equations. It does not reuse the author's tracer, rewrite, symbolic
expander, inspector, finalizer or graph helper for these comparisons. It
reconstructs parent and flow sources separately, including all constructor,
selector, lookup, root-binding and finalizer gates. Exact expression-DAG
identities compare every residual and the final outputs, without assuming
any zero equation or changing supplied values.

The old private height block has3N² multiplications and3N²+N additions:
each row has3N products,3N-1 summation additions and two subtractions.
The new block has the same3N² multiplications and3N²+1 additions: one
subtraction per row and one additional root-injection subtraction. The
transpose changes which paid products occur; no product or sum is free.
All other22N+3 residuals are unchanged. The complete finalizer still has
23N+3 squares and23N+2 summation additions. Hence

    new certificate: M=12N²+33N, A=15N²+45N+4;
    new full SOS:    M=12N²+56N+3, A=15N²+68N+6.

The old full count is27N²+125N+8. N=1 correctly ties at160;
N=2 decreases366 to365. Every gate and every supplied field is live.

With common coordinates equal but independent h and mu, the entire polynomial
difference is the sum of new flow residual squares minus old height residual
squares. This is an all-value identity over a commutative ring, separate from
the natural existential proof. Independent numerical corrections use h and
mu independently and include signed and rational assignments.

All residuals are quadratic. The retained pairing residual has leading form
`-(a_0+b_0)^2`, so the SOS has degree exactly4: its quadratic leading squares
cannot cancel over the reals. The independent complete circuits also attain
quartic degree on the exact line `a_0=t`, every other supplied field zero;
the t^4 coefficient is18 for both modes at every audited N. This supplements
the general homogeneous proof and is not used to infer a degree bound.

## Replay and evidence

The final standard-library helper is
[review_eager_tree_occurrence_flow_full.py](review_eager_tree_occurrence_flow_full.py),
with [its deterministic receipt](review_eager_tree_occurrence_flow_full.json).
Run from any working directory:

```sh
python /path/to/review_eager_tree_occurrence_flow_full.py \
  --repo /path/to/Proofs --artifacts /path/to/native-stream-queue \
  --expect /path/to/review_eager_tree_occurrence_flow_full.json
```

The artifact directory may instead be a private directory containing the
three frozen author files. Both the author and kernel are authenticated
before private source-byte execution; their historical main blocks do not
run. The author is imported solely for testing its actual emitted APIs, while
manual arithmetic reconstruction and graph restoration are independent.
The kernel's small evaluator is reused, with that limitation disclosed, for
eight selected actual application fixtures at three padding sizes.

The final audit passes:

- 12 independently reconstructed complete sources at N=1,2,3,4,5,8;
  1,094 residual DAG identities and12 whole-finalizer identities.
- 96 complete corrections with independently chosen old heights and new masses,
  including48 signed and12 rational cases.
- 24 actual forward-and-restored natural zeros, two saved disconnected-cycle
  restorations, and the additional circulation-feeds-root example.
- 70,400 finite weighted-graph/mass trials, yielding323 natural flows,
  including291 with a cycle outside the reachable subgraph. These fixtures
  supplement the general graph proof; they are not a completeness census.
- 1,132 malformed/domain rejections,24 defensive-copy checks, cold module-stub
  isolation, and a warm kernel-source mutation rejection.

The source loader executes the bytes it hashes, restores any preexisting
private module entry, and bypasses bytecode cache reuse. Canonical public
interfaces rebuild full packets and reject bool/float numeric aliases,
container substitutions, wrong external N and negative natural coordinates.
No unresolved source, arithmetic, domain or scope finding remains. This
review is distinct from the earlier supplemental pre-freeze review stem.
