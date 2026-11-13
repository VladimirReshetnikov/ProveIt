# Independent review: high-index independent-k norm construction

The author receipt reproduces. The independent checker verifies the Pell
norm-step and scalar-window identities as exact integer polynomials and
checks 15 bounded high-first-index instances without constructing the huge
main index. This is external mathematical evidence, not a Lean/model proof or
a full graph zero.

With n≥14 and q≥2n+2, X=q, Y=q³ and m=XY² are positive. The first recurrence
uses A=2m+1, D=A²−1=4m(m+1), initial `(1,0)`, and the stated Pell step.
The exact norm identity preserves `x²−D*y²=1`. Since A≡1 and D≡0 modulo
2m, induction gives x_j≡1 and y_j≡j modulo 2m; the nonnegative recurrence
also gives x_j≥1 and y_j≥j. Hence, for tau=x_n and k=2y_n, the first norm
holds and a natural s satisfies `k=2n+4m*s`.

The chosen **scalar** R=2n−1 obeys R≥26 and R+1=2n<q⁴, giving the
stated residue equation. The window follows from the checked exact identity
`q⁴−q³−q−2n=(q−1)*(q³−2)+(q−2n−2)≥0`. These facts say nothing by
themselves about the candidate's actual rank expression.

For the separate main recurrence, setting a=XY+Y and base B=a+2 gives
`B²−1=3+4a+a²`. Its Lth ordinate c, for `L=(Y+1)*k+1`, satisfies
`c≥L` by the same induction. Therefore eta=c−Y*k is a natural with
`eta≥k+1`, while `c=eta+Y*k` and the main norm hold. The Lean source's index
convention is zero-based `(x₀,y₀)=(1,0)` with recurrence base b+2: the first
recurrence corresponds to b=2m−1, and the main recurrence to b=a. There is
no off-by-one change in these identifications.

For the symbolic compact beta, q=beta+1=2^(67*8807), so the displayed finite
range `14≤n≤floor((q−2)/2)` is nonempty; n is unbounded only when q is
allowed to vary. The construction leaves the actual graph's rank, signed
first and main roots, and strong/auxiliary factors unbound. It is therefore
not a compact full-zero example, a counterexample to the exact-index theorem,
or a proof that the candidate admits k<eta. No Lean/provider, endpoint,
external encoding or PDF claim follows.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-independent-k-high-index-norm-independent/check.py | cmp - reviews/ordinary13-independent-k-high-index-norm-independent/receipt.json
```
