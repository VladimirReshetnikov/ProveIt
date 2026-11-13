# Scalar obstacle to uniform quotient cancellation

This exact standard-integer diagnostic tests one possible inference in an attempted uniform extension of the checked r=7 and r=9 arguments. Let `t=2Y`, `h=q−1`, `K=2^r`, `L=K/4`, and let `y_0(a)=0`, `y_1(a)=1`, `y_(i+1)(a)=a*y_i(a)-y_(i-1)(a)`. With `q=64`, `Y=64^3`, `X=2^200`, `n=15`, and `r=17`, the checker verifies all of:

* `n>=7`, `r=n+2` is odd, `X>=32`, `Y>=q^3`, and `q` divides both `X` and `Y`;
* the strict scalar Pell inequality `t*y_n(X*t^2+2) < y_r(t*(X+1)+2)`;
* `L*h = 2064384 > Y = 262144`.

Thus the scalar inequalities and divisibility listed above do not by themselves supply the `L*h<Y` bound used to identify the quotient in the fixed-r argument. In this example the weighted projection `H | h*X*(X-K)*(K*X+1)`, with `H=4*Y*(X+1)-1`, **fails**; the exact nonzero remainder is retained in `receipt.json`. This is not a 74 graph zero, does not refute any full graph implication, and does not decide whether a different uniform argument works. The finite example illustrates a proof gap; it is not evidence of a countermodel in a nonstandard model.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/trace74-uniform-projection-quotient-obstruction/check.py
```

The script rejects Python without isolation, without `-S`, or with optimization, because its exact checks use assertions. It performs ordinary integer arithmetic only and makes no Lean/kernel claim.

The [independent arithmetic audit](../../reviews/trace74-uniform-projection-quotient-obstruction-independent/README.md) reproduced the recurrence gap and projection remainder.
