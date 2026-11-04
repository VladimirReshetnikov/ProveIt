# Proposed exclusion of first Pell index 2 when q≥4

This is a mathematical proof plan, not yet a Lean theorem. Every step must be checked in the same (possibly nonstandard) arithmetic model. Its graph inputs are the already checked first-Pell recurrence and `n≥2`, the odd-ordinate witness with index `r>0` and `r%2=1`, the K-bound, and `c=kY+eta`, `k=eta+zeta` with positive eta/zeta. No rank, F/C bound, reverse guard or fixed-mask claim is used. Assume additionally `q≥4`, which holds for the intended fixed beta but still requires the relevant symbolic binding.

Write `X=wq`, `Y=q³s`, `A=Y(X+1)`, `P=XY²`. Positivity gives `X≥4`, `Y≥64`, and both X,Y divisible by q. Assuming first index n=2, the recurrence gives `k=8XY²+4`; the checked first-index geometry gives `X<2Y`. Also `c=kY+eta<k(Y+1)`.

For `b=A−1`, expand the fifth ordinate without subtraction:

```
y₅(b) = 16A⁴+64A³+84A²+40A+5.
```

It exceeds `k(Y+1)`: since X,Y≥1, `Y+1≤2Y`, `8XY²+4≤12XY²`, `A⁴=Y⁴(X+1)⁴≥2XY³`, so `k(Y+1)≤24XY³<32XY³≤16A⁴<y₅`. Strict monotonicity in the model then makes `r≥5` impossible. As `r` is a positive odd model element, r is 1, 3, or at least 5; r=1 gives c=1, contradicting c>2. Hence r=3.

The third ordinate is `y₃(A−1)=4(A+1)²−1`. Substituting the n=2 k-value into `c=kY+eta` gives the exact integer identity

```
eta + 4Y²(2XY−(X+1)²) = 8YX+4Y+3.
```

If `X+3≤2Y`, then `2XY−(X+1)²≥X−1`. Because X≥4 and Y≥64, `Y(X−1)≥2X+2`; thus `4Y²(X−1)≥8YX+8Y>8YX+4Y+3`. This contradicts eta>0 and the identity, proving `2Y<X+3`.

Now `X<2Y<X+3`, while q divides both X and Y. Therefore q divides the positive integer `2Y−X`, which is less than 3. This contradicts q≥4. Model formalization must use its discrete-order and truncated-subtraction divisibility lemmas, and its internal odd-index and strict-monotonicity results, not an external claim about standard integers.

If formalized, the conclusion for q≥4 is first index n≥3, and hence `32P²+32P+6≤k` from the checked first-Pell recurrence. In particular, this plan does not establish F<q, C≤q, the 74-to-75 guard, or any end-to-end iPRA claim.

Independent [mathematical review](../../reviews/trace74-n2-exclusion-plan-independent/README.md) passed, SHA-256 `5030f6a83a8d11cab0c130d480e0ac7a9122198c632f1167f0d0ff8343448e19`. It verifies the displayed reasoning and identifies the nonstandard-model formalization obligations; it is not a Lean check.
