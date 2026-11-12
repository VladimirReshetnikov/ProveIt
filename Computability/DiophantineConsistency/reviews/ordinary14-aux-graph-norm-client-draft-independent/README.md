# Independent source review: 78/79 graph-to-norm bounds client

**Source review passes; not elaborated.** The literal 78 and 79 graphs have
the same first, main and strong expression trees, even though slot 11 is
named differently. Their rank uses integer-port casts in the difference
ring, and the proposed main value retains this signed rank; no unproved
natural rank or orientation is assumed. The stated first/main/strong ring
evaluations, `Q=Delta(f²−1)`, and `z=f²(Tc−R)−c` match those graph trees
up to explicitly checked commutative-ring regrouping.

The client extracts its three fields from the relevant graph's own five-square
zero. In particular, the 78 wrapper does not assume a 79 zero or identify the
different auxiliary fields. Positive graph values give positive q, X, Y and
U. The strong field zero gives the explicit Q binding; the z binding is a
ring identity. Together with the natural c/Delta definitions and the first,
main and strong residual equations, these are the premises of the separately
uncompiled ring-norm/bounds route. The explicit `(p 0 : DiffRing V)=ι beta`
assumption is required; the other three integer ports need not be natural.

The checker pins all source and candidate bytes, replays the 78 graph
generator, author inventory and independent ring-norm review, compares
slot-normalized exact expression DAGs for both graphs, checks the displayed
rank/carrier/Q/z formulas, and proves the necessary cut regroupings in a
sparse integer polynomial ring. It does not invoke Lean or certify `rfl`,
`simp`, coercions, tactic behavior, imported provider ancestry, a slot-11
witness map, all-positive graph equivalence, the iPRA endpoint, or file
semantics. Those remain unverified.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-graph-norm-client-draft-independent/check.py
```

Compare stdout with `result.json`.
