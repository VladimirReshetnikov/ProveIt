# Eager Tree certificates with root occurrence flow

The corrected finite eager Tree Calculus kernel admits a smaller complete
certificate: replace its per-row height by an incoming occurrence count.
For every fixed external row count `N>=1`, the new polynomial represents
**exactly the same natural input/output triples** as the parent. It saves
**N−1 additions**, with unchanged witness count and exact degree four.

| Certificate | Natural witnesses | Quadratic residuals | Complete operations |
|---|---:|---:|---:|
| Corrected parent | `3N²+19N` | `23N+3` | `27N²+125N+8` |
| Root occurrence flow | `3N²+19N` | `23N+3` | `27N²+124N+9` |

This is a family indexed by external N. It supplies no fixed-arity universal
polynomial, no paid ordinary-input loader, and no new universal operation
bound. It changes witnesses and admits disconnected cycles; it does not
preserve the parent's entire zero set or a canonical/unique witness fiber.

## Authenticated source and local rules

The [checker](eager_tree_occurrence_flow.py) authenticates the actual corrected
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py`
before loading it in a private module. Its SHA256 is

    636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52

The earlier [report review](review_eager_tree_aebfa.md) records the imported
construction and its domain repairs. The current transformation starts from
the base kernel, not from the larger canonical certificate that additionally
sorts keys and normalizes inactive fields. Historical suites are not run by
this checker. Instrumenting the actual kernel's arithmetic records its full
literal source, including every residual and the sum-of-squares finalizer.

All coordinates are natural integers, including zero. Tree codes use leaf 0,
stem `S(a)=2a+1`, and fork `F(a,b)=(a+b)(a+b+1)+2b+2`. Every natural is a tree
code: odd numbers are stems, and for an even code at least two, subtracting
two and dividing by two gives the Cantor pairing number of a,b. The decoded
children are smaller than their parent. Thus local code validity is free.

Each row supplies x,y,z, a height h (replaced by mass mu), ten decomposition
fields, five tags and three N-entry pointer lists. Natural tags sum to one.
Each pointer list sums to its active flag, so it is either zero or selects
exactly one row. The retained decomposition and lookup residuals implement:

- `x=0`: output `S(y)`.
- `x=S(a)`: output `F(a,y)`.
- `x=F(0,b)`: output b.
- `x=F(S(a),b)`: premises `(b,y)->u`, `(a,y)->v`, `(u,v)->z`.
- `x=F(F(a,b),c)`: premises `(y,a)->u`, `(u,b)->z`.

The three final residuals bind row zero's x,y,z to the supplied program,
argument and output. No tag or pointer Boolean conditions are being dropped:
they follow from the retained natural sum equations.

## The changed equations

Write `p[i,s,j]` for the pointer from row i, slot s, to row j. The old equation
at every row is

    h_i = 1 + sum_(s,j) p[i,s,j] h_j.

It makes every selected edge strictly decrease height and so forbids all
cycles. Replace it by

    mu_i = delta_(i,0) + sum_(j,s) mu_j p[j,s,i].

These are incoming occurrence balances. Only row zero has a source of one.
The implementation uses one product per pointer and one subtraction per row;
it subtracts the root injection only at row zero. All other source rows and
residuals are retained literally after deleting the private height cones.

## Equality of represented triples for every N

First consider a natural zero of the new polynomial. A sum of natural-domain
integer squares vanishes only when every residual vanishes. Therefore tags,
pointers, decompositions, root binding and incoming balances all hold.
The root has `mu_0>=1`. Along any selected edge i to j, the nonnegative
incoming sum gives `mu_j>=mu_i`. Every row reachable from the root therefore
has positive mass.

Suppose a directed cycle were reachable. Choose a simple directed cycle and
a root path entering it for the first time. Along the cycle the mass
inequalities force equality at every edge. If the root is on the cycle,
its injection of one contradicts that equality. Otherwise the first cycle
vertex also receives a positive contribution from the preceding vertex of
the root path, which is outside the cycle. Its incoming sum is then strictly
larger than its cyclic predecessor's mass, again a contradiction. Repeated
premises and edge multiplicities only add nonnegative terms. Hence the
root-reachable subgraph is acyclic.

Induction from its leaves now establishes each of the five eager application
rules, and proves the claimed root input/output relation. To construct an
old certificate at the **same N**, retain the reachable rows and recursively
assign `h_i=1+sum p[i,s,j]h_j` there. Replace every unreachable row by the
existing valid leaf dummy `(x,y,z)=(0,0,1)`, tag zero, all pointers zero,
consistent decomposition fields and height one. Reachability closure ensures
that no retained row points to a replaced row. All parent residuals vanish
and the three external coordinates remain unchanged. Keeping unreachable
local fields unchanged would in general make this inverse impossible.

Conversely, at a natural parent zero all selected edges decrease positive
height, so the entire finite graph is acyclic. Define mu_i as the number of
rooted directed paths to i, counting multiplicities of selected slots and
the empty path at row zero. These finite natural counts satisfy the incoming
balances. Unreachable rows get mass zero. Retain every other coordinate;
all new residuals vanish. This proves equality of represented triples in
both directions for every fixed N, including certificates padded with
unreachable dummy rows. No bound on the occurrence counts is imposed.

The checker includes a concrete distinction between zero sets: an actual
leaf root accompanied by a disconnected fake omega-on-omega recursive call.
That component has a self-loop and accepts positive circulations in the new
system. The old height equation on that row would read
`h_cycle=1+2*h_Iomega+h_cycle`, impossible over the naturals. Replacing the
unreachable rows restores a parent witness for the same valid root triple.
These examples demonstrate why no unchanged-coordinate inverse or uniqueness
claim follows from the graph theorem.

## Full polynomial relation, exact degree and paid ledger

Let F_flow and F_height denote the complete emitted SOS polynomials. With
all common coordinates equal, but independent h and mu, their difference is
exactly

    F_flow - F_height = sum_i [
      (mu_i-delta_(i,0)-sum_(j,s) mu_j*p[j,s,i])^2
      -(h_i-1-sum_(s,j) p[i,s,j]*h_j)^2 ].

This is a polynomial identity on arbitrary commutative-ring assignments; it
is separate from the natural-domain witness theorem. The checker proves
retained residual identities by exact coefficient dictionaries and checks
the complete old and new changed residuals symbolically. Every retained
source instruction is literally unchanged. The complete finalizers contain
one square per residual and one fewer addition than residuals, so the
identity follows for the whole polynomials.

The old private height block costs `3N² M+(3N²+N) A`; the new incoming block
costs `3N² M+(3N²+1) A`. Other rows and the finalizer are unchanged. The new
comparison source therefore costs

    M=12N²+33N,  A=15N²+45N+4.

Adding `23N+3` squares and `23N+2` additions gives the full polynomial

    M=12N²+56N+3,  A=15N²+68N+6,
    total=27N²+124N+9.

All source gates and supplied fields are live. For N=1 the cost ties the
parent at160. For N=2 it falls from366 to365. The reduction is exactly N−1
additions for every N, with no uncharged finalization.

Every residual has degree at most two. The retained row-zero residual
`d_0-F(a_0,b_0)` has nonzero quadratic part `-(a_0+b_0)^2`. Thus the sum of
squares of quadratic leading forms is nonzero over the reals, establishing
**exact degree four** of the complete polynomial, uniformly for every N.
No residual equation or finite coefficient specialization reduces degree.

## Replay and contract

The [saved receipt](eager_tree_occurrence_flow.json) emits complete parent
and child sources at N=1,2,3,5,8, exact residual identity certificates and
all ledgers. It also checks 60 whole-polynomial numerical corrections,
5,196 retained residual values, 120 actual application zeros, two disconnected
cycle witnesses, 208 rejected malformed calls, 20 independent-copy checks,
a warm kernel-pin mutation and optimized-Python rejection. These finite
examples supplement the graph and source proofs above.

From any working directory, using the standard library:

```sh
python3 /path/to/eager_tree_occurrence_flow.py --repo /path/to/Proofs \
  --expect /path/to/eager_tree_occurrence_flow.json
```

`--output FILE` writes the deterministic receipt. Public `build`, `rewrite`,
`checked` and `evaluate` reconstruct and authenticate complete canonical
packets, with exact integer N and exact container/scalar types. Evaluation
requires every supplied coordinate and rejects negative values by default;
`signed=True` permits signed integer polynomial evaluation without asserting
a signed-domain computation theorem. No shared mutable packet cache is used.
The imported current kernel is authenticated before every public build and
is loaded without running its historical main suite. This is an executable
mathematical audit, not a proof-assistant formalization.
