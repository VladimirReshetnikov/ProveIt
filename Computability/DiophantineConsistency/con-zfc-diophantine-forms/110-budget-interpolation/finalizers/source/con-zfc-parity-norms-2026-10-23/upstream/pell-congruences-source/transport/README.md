# Monic native transport and the small integer equations

This component provides six finite, fixed-coefficient ordinary integer
polynomials. Each JSON packet lists all unknowns, ordered polynomial
abbreviations, and a finite list of residuals. The single equation is the
sum of the residual squares. Abbreviations introduce no additional
unknowns and contain no variable exponent, inequality, divisibility test,
unbounded product, or hidden quantifier.

| Packet | Unrestricted integers | Residuals | Exact total degree |
|---|---:|---:|---:|
| `degree10_24.json` | 24 | 11 | 10 |
| `degree16_22.json` | 22 | 10 | 16 |
| `degree20_20_rank_register.json` | 20 | 8 | 20 |
| `degree28_19.json` | 19 | 7 | 28 |
| `degree32_18.json` | 18 | 6 | 32 |
| `degree88_17.json` | 17 | 5 | 88 |

The six fixed numerals are the unchanged whole source-34 tuple
`beta,K0,MC,MF`, together with the determinant scales
`cone_A=2^1113`, `cone_B=2^666104`. The neighboring `coefficients/`
directory supplies the authentic coefficient payloads and their binding.

## The exact new elimination

Promote `C=q-F-alpha` to an independent coordinate `C_native` replacing
alpha. Its inverse is `alpha=q-F-C_native`. The transport equation is

```
(K0+W)C_native-F-z(q-1)=0.
```

It is monic in F. Delete that coordinate and row by substituting

```
F=(K0+W)C_native-z(q-1).
```

The rank simplifies identically to

```
R=(q(q-F)-C_native)(q^2-1)+(MC+q MF)J_native.
```

Every other occurrence is substituted as well. This proves a bijection
of integer zero sets without any new number-theoretic hypothesis. The
20-variable degree-20 companion then reintroduces R as an explicit
register with its own monic defining row, reducing the cost of repeatedly
substituting R in the CRT and auxiliary expressions.

## Rebuild and check

From the complete package root:

```
python3 transport/build_transport.py
python3 transport/check_transport.py
```

When this directory has a different name or location, invoke the two
scripts by their actual paths. An optional first argument supplies the
absolute or relative directory containing the authentic `.bin.gz`
coefficient payloads. Otherwise the scripts use the neighboring
`../coefficients/payloads` directory. Python's standard library suffices.

The builder checks the finite DAG, declared-variable liveness and a degree
upper bound. To establish exact degree on the actual coefficient slice,
it substitutes integer multiples of one indeterminate for all unknowns
and computes a nonzero leading coefficient modulo 1,000,000,007. The
independent checker verifies that coefficient by finite differences,
using the degree bound and the identity

```
Delta^d p(0) = d! [t^d]p(t).
```

This is an exact coefficient certificate, not a random-point identity
test. Since a nonzero highest real homogeneous polynomial square cannot
cancel in a sum of squares, the final degree is twice the largest
residual degree. The checker imports no builder code. It also verifies
the local polynomial identities and strictly compares the entire finite
definition graph and retained rows with their source packets. The large
degree-88 residual need not be expanded to certify these facts.

`certificates/INDEPENDENT_TRANSPORT_AUDIT.json` records 225 successful
checks. `parents/` contains the inert source packets needed for rebuilding;
the main report supplies the mathematical CRT, parity, guard and inherited
calibration arguments. These checks do not claim to be a new end-to-end
Lean/Rocq certificate or to prove Con(ZFC).
