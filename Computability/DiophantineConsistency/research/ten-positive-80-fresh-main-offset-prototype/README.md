# Fresh unscaled main-offset divisibility

`TenPositive80FreshMainOffset.graph_fresh_main_offset` augments the fresh
unscaled source projection with a natural h satisfying

    K = R + 1 + (Y*q²)*h,
    d = X + a*C + (4a+3)*γ,   γ > 0,
    a = Y*(X+1),  R = 2r+1.

The same r, γ, fresh K and C are used throughout. K is the doubled first
Pell ordinate and C is the fresh unscaled main ordinate. The proof applies
the general first-ordinate residue at index r+1 to obtain a multiple of
`4*X*Y²`; the graph's explicit `X=q*w`, `Y=q³*s` make that multiple divisible
by `Y*q²`. It does not claim h>0. All statements concern an actual positive
80-graph zero and symbolic β/low/high ports; p₁ remains arbitrary, with no
binding to an external K0 byte string. No old-graph factor, source converse,
halt equivalence, PDF binding, or iPRA theorem is asserted here.

The guarded check `observations/fixeddigits-attempt01/` produced
`/tmp/tenpositive-80freshmainoffset-jiuanoo9/Direct80FreshMainOffset.olean`,
SHA-256 `4ae50ad87c91a1b6d96f4f1e7febeb2b9f0c0998c0ffb30dfae9717aefe6748e`.
The receipt pins selected direct inputs and resources; full project/package
ancestry, dynamic libraries and historical source-object edges are inherited.

The original accepted run did not individually pin the directly imported
`ArithmeticPellCongruences.olean`. The separate self-pinning `run-v2.py`
adds its selected object pin, SHA-256
`ff395c82ca9ea770a64ec69e4b4b7f8e1e2d655d67db4831af39a2d8a78ae664`.
The corrected guarded check is `observations/v2-attempt01/`; its fresh output
`/tmp/tenpositive-80freshmainoffset-zbew9euo/Direct80FreshMainOffset.olean`
is bit-identical to the earlier object. The v2 receipt verifies source,
runner, tool and selected pins across the run. Other historical transitive
source-object, package and dynamic-library limitations remain inherited.
