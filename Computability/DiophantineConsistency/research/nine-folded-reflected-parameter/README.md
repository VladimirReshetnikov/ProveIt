# A reflected auxiliary parameter: 408 / 416 operations

This separate research sibling replaces only the auxiliary Pell parameter
in the accepted tight folded-nine construction:

    G_parent=A+F*(1+A*(C-1))
    G_new=F*(A+C+1)-A.

| Whole fixed tuple | Positive variables | Live operations | Exact degree |
|---|---:|---:|---:|
| original31, boundary_simple.json | 9 | 408 | 1,191,570 |
| compact54-sharp, compact_simple.json | 9 | 416 | 1,316,546 |

The original counts were409 and417, with degrees two larger. This new
parameter saves one multiplication and lowers the largest-degree summand
by two. It changes the polynomial, with a fully stated ordinary existential
map and fresh positive auxiliary witnesses. It is not a pointwise identity.
The complete source, fixed payloads and nine positive domains are retained.

The key is that G stays positive and exceeds F, equals1 modulo C, and
now equals -A modulo F. Pell recurrence satisfies
`psi_(-A)(t)=(-1)^(t-1)*psi_A(t)`. Soundness already uses signed folding,
so it needs no new parity assumption. Completeness uses the actual odd
index `B1=2R+1`, making `psi_(-A)(B1)=psi_A(B1)=C`, then the same
finite determinant-one matrix periods construct positive j and n.
PROOF.md includes the zero/negative-margin branches before integrality,
the main rank recovery, the source boundary and the full witness order.

The producer clones the entire parent circuit except the private old
parameter chain. Every other operator, operand and fixed leaf is retained.
The independent checker imports no producer and executes no parent emitter.
It verifies complete parent mappings, private-use inventories, all new
nodes, both full norms, all actual native and fixed integer payloads,
centered degree bounds, and nonzero highest homogeneous values modulo
three primes. Five corruptions are rejected in each profile. Signed
recurrence, residue folding and combined-modulus matrix-period controls
supplement the unbounded proof.

The prior zero-offset improvement has no further literal offset to delete
here: the retained core already has A=M(U+1). Likewise U=N²w and Y=N²s
belong to the inherited numerical ratio interface; replacing those products
by free additive bases is not licensed by the ten-variable direct-base
proof. A plain replacement `G=A+F*(C+1-A)` has the right residues but can
be negative at C=1, which is allowed before margin recovery. The new
reflection avoids that broken positivity-first bootstrap. A finite syntactic
common-expression scan of both accepted parent DAGs found no repeated
binary expression after commutativity; this is not a lower bound or an
optimality claim.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/research/nine-folded-reflected-parameter/build.py --check
python -B Computability/DiophantineConsistency/research/nine-folded-reflected-parameter/check.py
python -B -O Computability/DiophantineConsistency/research/nine-folded-reflected-parameter/build.py --check
python -B -O Computability/DiophantineConsistency/research/nine-folded-reflected-parameter/check.py
```

The ordinary calibration and source-to-refutation interpretation remain
those of the complete pinned parent family. Finite checks do not establish
that semantic theorem. No new Lean or internal-ZFC theorem is asserted.
All accepted parents, common documents and the canonical page remain fixed.
