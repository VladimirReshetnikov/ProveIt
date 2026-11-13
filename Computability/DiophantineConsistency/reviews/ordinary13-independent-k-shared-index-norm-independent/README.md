# Independent review: shared-index norm family

The [reviewed construction](../../research/ordinary13-independent-k-shared-index-norm-audit/README.md) correctly produces ordinary-integer scalar data satisfying both stated Pell norms, the first-index congruence and window, and the exact relation `2n=R+1` with the main Pell index R, while `eta>k`. I found no indexing or growth-bound mismatch. These are partial scalar data: the construction chooses R and does not prove that it equals the independent-k graph's rank expression, bind its signed roots, or satisfy its strong and auxiliary factors. It is not a full graph zero or a counterexample to an unrestricted witness replacement.

The recurrence starts at `(1,0)` at index zero, as in `ArithmeticPellRecurrence`; its parameter b corresponds to base `A=b+2` and discriminant `A²−1`. The first base is `2M+1`, so b=`2M−1`, matching the source's `ycoord n (2*(M−1)+1)` when M≥1. The main base is `a+2`, so its parameter is a and the constructed c is exactly its ordinate at index R. Thus the source's separate m and R match upon choosing m=R, and `2n=R+1` has the stated orientation.

The step preserves `x²−(A²−1)y²`; its companion identity `A*y_{j+1}−x_{j+1}=y_j` implies the claimed upper growth bound from index 1, and the recurrence gives the lower bound. With `M=q⁷` and `a=q⁴+q³`, these bounds yield

```
k ≤ 2*6^(n−1)*q^(7n−7),
c ≥ q^(8n−8).
```

Since `Y+1≤2q³`, comparison reduces to `q^(n−4)>4*6^(n−1)`, which follows for n≥14, q≥2n+2 from the audited, stronger q≥24 and n≥9 inequality. Consequently `c>(Y+1)k` and `eta=c−Yk>k`. The q⁴ window follows from the exact identity `q⁴−(R+q³+q+1)=(q−1)(q³−2)+(q−2n−2)`; the last term is nonnegative under the stated q bound. The first recurrence's y-coordinate is n modulo 2M, so its quotient s is natural and `k=2n+4Ms`.

At the fixed symbolic compact beta with J=1, q is `2^(67*8807)`, so the advertised n interval exists and is finite for that fixed q. No large numeral was expanded. The general unbounded-n statement varies q, as the author notes. An arbitrary-model version would require separate formalized recurrence growth and witness arguments; the source-only recurrence signatures and controls do not supply one.

The receipt reproduces the author's exact-polynomial checker and independently computes ten additional examples using matrix exponentiation, including n up to 100. It also checks the zero-index convention and exact-index theorem's source binders. These finite controls do not establish the uniform theorem or any Lean/provider/axiom replay. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-shared-index-norm-independent/check.py | cmp - reviews/ordinary13-independent-k-shared-index-norm-independent/receipt.json
```
