# Exact degrees of the ordinary 29-integer certificates

There are seven positive ports `J,F,alpha,z,s,eta,zeta`; each is replaced by
`1+u^2+v^2+r(r+1)`. The ports `f,h,T,tau,y,gamma` remain unrestricted,
`i=2r_i+1`, and `w=u_w^2`. This gives 21+6+2=29 coordinates.
The substitution costs 52 gates: 23 multiplications and 29 additions or
subtractions. The three resulting circuits have these exact metrics:

| Form | Integer variables | Equations | Operations | Exact degree |
|---|---:|---:|---:|---:|
| Product | 29 | 1 | 121 = 62M+59A | 188 |
| System | 29 | 6 | 113 = 57M+56A | maximum 50 |
| Sum of squares | 29 | 1 | 130 = 63M+67A | 100 |
| Normalized product | 29 | 1 | 119 = 62M+57A | 300 |
| Reduced normalized product | 29 | 1 | 120 = 62M+58A | 236 |

## Uniform upper bounds

Assign weight 2 to `J,F,alpha,z,s,eta,zeta,w` and weight 1 to the other
seven source variables. Fixed coefficients have weight zero. The relevant
weighted degrees are

```
q:2, X:4, Y:8, E:12, k:2, c:10, a:12, H:12, Delta:24,
R:8, V:12, A0=Delta(f^2-1):26.
```

For the main norm use the polynomial identity, with `r=X+gamma H`,

```
D^2-Delta c^2 = 2ac r+r^2-Hc^2.
```

Its weighted degree is 35 rather than the uncorrected gate bound 44.
The six factor degrees of the ordinary product are exactly

```
44, 35, 50, 13, 4, 42.
```

The sum is 188; the auxiliary factor alone has the maximal degree 50.

## Nonzero leading forms for the genuine coefficients

For each of the seven positive ports x, let
`x_2=u_x^2+v_x^2+r_x^2` be the leading homogeneous form of its
parametrization. Put

```
Q=beta*J_2,      k_2=eta_2+zeta_2,      C_2=Q-F_2-alpha_2,
beta=B-1>0.
```

The ordinary product's leading homogeneous form after substitution is

```
32 Q^55 h gamma r_i^2 k_2^9 u_w^14 s_2^16 T^2 f^4
   * [u_w^2 C_2-z_2 Q].
```

This is a nonzero degree-188 polynomial. For example the last bracket
contains the monomial `-u_w^2 u_F^2`, which cannot cancel with the term
`-z_2 Q` or the other two summands of C_2.
The SOS leading form is the square of the auxiliary residual leader:

```
Q^28 k_2^4 u_w^8 s_2^8 T^4 f^8.
```

It is nonzero and has degree 100. This proves both degrees uniformly for
the actual giant fixed coefficients; evaluating toy numerals is not the
reason these degree claims hold.

## Executable independent specialization

The emitter includes an exact standard-library univariate evaluator.
Set every positive triple to `(t,0,0)`, all six free variables to t,
`r_i=t` and `u_w=t`. Its product leading coefficient is
`-32768 beta^55`, and its SOS leading coefficient is `16 beta^28`.
Both are nonzero for every beta>0. The verifier evaluates this at beta=15
and records the exact integer coefficients, verifies all operation
ledgers, and compares 100 exact signed-input evaluations per emitted
circuit with the direct source substitution. These checks concern the
circuits and their degrees, not the universal solvability theorem.

## Normalized variants

The same substitution applies to the literal package06 packets
`fixed_blank_67.json` and `fixed_blank_68.json`. Their weighted factor
degrees are, respectively,

```
44, 35, 114, 13, 4, 90;      44, 35, 50, 13, 4, 90.
```

Their leading forms are

```
-128 Q^91 h gamma r_i^4 k_2^13 u_w^26 s_2^26 T^2 f^2
     * [u_w^2 C_2-z_2 Q],

-32 Q^71 h gamma r_i^2 k_2^9 u_w^22 s_2^20 T^2 f^4
     * [u_w^2 C_2-z_2 Q].
```

They are nonzero for beta>0 and have degrees 300 and 236.
The same specialization gives leading coefficients
`2097152 beta^91` and `32768 beta^71`. The script verifies the stated
degree bounds and both exact specializations.

Run the reproducible emitter with explicit input directories as needed:

```
python3 build_integer29.py --ordinary-dir PATH_TO_ORDINARY_JSON \
  --normalized-dir PATH_TO_PACKAGE06_DATA --output-dir OUTPUT
```

It writes five circuits and one exact verification receipt. It requires
only Python's standard library.

