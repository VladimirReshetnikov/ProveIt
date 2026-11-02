# Source-only straddling-window plan; not compiled

Work in an arbitrary IΣ₁ model. Let `e = 67*k + a`, `0 < a < 67`, `L = e + ((67-a) + t)` and `X < Exp.exp L`. The proposed equality is

```
dig 67 (rot 1 L X e) k =
  (X % Exp.exp (67-a)) * Exp.exp a +
  (X / Exp.exp ((L-e)+67*k)) % Exp.exp a.
```

All exponentials and subtraction are internal. The cut-length hypothesis is explicit, not derived from the graph. Define P=exp(67*k), A=exp a, B=exp(67-a), H=X/exp(L-e), Q=X%exp(L-e). The rotation is Q*(P*A)+H. From the bound X<exp L and L=e+(L-e), obtain H<P*A; hence H/P<A. Dividing the rotation by P gives Q*A+H/P using `div_add_mul_self` after algebraic reassociation. The final mod-2^67 decomposes into `(Q%B)*A + (H/P)%A`: apply `mod_mul_split` with P=A, Q=B to the quotient or prove the generic low-high identity using `div_mul_add` and `mod_mul_split`. Since exp(L-e)=B*exp t, `mod_factor X B (exp t)` reduces `(X%exp(L-e))%B` to `X%B`. Rewrite H/P as `X/exp((L-e)+67*k)` using `Arithmetic.div_mul` and `exp_add`.

The previous `AdjacentDigits.adjacent` supplies the full 67-bit digit of the high-source quotient at any represented index `67*q+r`; reducing its two-digit expression modulo exp a yields the required a-bit fragment. Additional bounds or source-zero facts are needed for strict `<2^66` and choosing the relevant q,r,t in the graph. No implication is asserted for a window of insufficient source cut length or absent word bound.
