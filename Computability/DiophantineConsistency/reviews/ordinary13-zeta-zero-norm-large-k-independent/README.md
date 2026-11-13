# Independent review: zeta-zero large-k facts

At `k=2`, put `A=XY+Y+2` and `c=2+2Y`. With model-natural X,Y, `Y>0` gives `1<c` and `2*A-c=2*X*Y+2>0`, so `c<2*A`. Together with the explicitly assumed `A²=Delta+1`, these match the `no_main_square` interface: the proposed main norm would put a square strictly between `(A*c-1)²` and `(A*c)²`.

For the large bound the source explicitly assumes `X,Y,k>0` and both first and main norms. With `m=XY²>0`, it presents the first norm to `two_le_ordinate` using `discriminant(m-1)=m*(m+1)`. The k=2 exclusion gives `k>2`, which is exactly the premise of `first_ordinate_large`, yielding `k≥8*XY²+4`. This route does not assume positive zeta. The `k=0` boundary is not covered by this lemma.

The checker pins and matches all cited source interfaces, and reproduces the author's receipt. Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-zeta-zero-norm-large-k-independent/check.py | cmp - reviews/ordinary13-zeta-zero-norm-large-k-independent/receipt.json
```

All Lean terms and model providers remain unelaborated. The facts do not yet follow from an altered graph zero, and no zero map, reduction or endpoint is established.
