# The free auxiliary-square partial assignment cannot satisfy the main norm

The [compact partial assignment](../ordinary13-free-aux-square-compact-factor-obstruction/README.md) chose `c=Delta+2`. It cannot be extended to a full graph zero: the actual main residual is necessarily nonzero. This is a rigorous obstruction for that choice of c, not a proof that the free auxiliary-square candidate has no other zero or a zero-preserving map to its parent.

For any ordinary integer A≥2, set `Delta=A²−1` and `c=Delta+2=A²+1`. An exact polynomial identity gives

```
1+Delta*c² = A²*(A⁴+A²−1).
```

This number cannot be a square. If d² equalled it, square divisibility would give A|d. Cancelling A² would make `A⁴+A²−1` an integer square, but

```
(A²)² < A⁴+A²−1 < (A²+1)².
```

The compact assignment has `A=a+2≥2` and positive `U=Yq²`. Its exact graph main residual is `A1=Dstar²−U²*(1+Delta*c²)`. If A1 were zero, integer square divisibility would give U|Dstar and make the displayed radicand a square, contradiction. This uses no first-root, rank, alpha or mask assumption beyond the assignment's positive U and chosen c.

In fact the same c choice is incompatible with a **complete integer output zero** of this candidate whenever U>0. The exact output is the product of four integer factors minus one. At output zero all four factors are ±1. The main factor `1+A1` is never −1 modulo four; the checker exhausts its 256 residue patterns. It must therefore be +1, forcing A1=0, already impossible. This unit argument is ordinary-integer arithmetic; no arbitrary-model extraction or Lean proof is supplied.

The checker reproduces the partial packet's receipt, pins and checks the candidate's main/output rows, verifies the radicand identity as an exact polynomial, exhausts the main-factor mod-four cases and tests bounded A controls. The symbolic square-gap argument above establishes the stated conclusion; finite controls alone do not. Other choices of c and all other candidate zero maps remain open. No large fixed constants, Lean process, build, provider/axiom validation or PDF binding is involved. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-partial-main-obstruction/check.py | cmp - research/ordinary13-free-aux-square-partial-main-obstruction/receipt.json
```
