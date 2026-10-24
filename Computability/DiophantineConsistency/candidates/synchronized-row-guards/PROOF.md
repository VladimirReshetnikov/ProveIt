# Integer companions from actual synchronized row certificates

The main new equation has **1,224 unrestricted integer variables**, exact
degree four, 634 quadratic residuals, 23,590 collected terms and height
83,900,628. It has an integer zero exactly when the reviewed synchronized
522-natural equation has a natural zero. Three additional fully
materialized quartics retain useful term/height tradeoffs.

This is ordinary arithmetic research. No Lean source is changed or run;
formalization remains paused. The sign proof below applies to arbitrary
integer zeros of the actual polynomial rows. It does not assume their
Pell, binomial, factorial, CRT or refutation meanings.

## 1. Authenticated natural parents

The parents are four unchanged literal systems in
`ConZFC_Synchronized_Certificates_2026-10-24.zip`, SHA256
`ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf`.
Each variant includes the exact parent bytes as `natural_parent.json`.
`PARENT_PINS.json` gives its complete ZIP member and SHA256, along with
the frozen elementary closure framework's source hash.

The parent ordinary source proof was independently accepted in
`PROPOSAL_REVIEW_SYNCHRONIZED_CERTIFICATES.md`; it includes the common
Pell frame, simultaneous index CRT witnesses, deferred binomial radix,
natural contractions and explicitly inherited C222/refutation interfaces.
All 22 original generated JSON files were reproduced byte-identically in
normal and optimized Python before this transformation. The present
sign certificate does not import that proof to establish any sign.

## 2. Elementary inference over unrestricted integers

Suppose an actual zero row, possibly multiplied by -1, is

```
c*x=P(z_1,...,z_r),    c>0,
```

where x is absent from P and every coefficient of P is nonnegative.
If every variable occurring to an odd exponent in a monomial of P has
already been proved nonnegative, that monomial is nonnegative. Even
powers are nonnegative for arbitrary integers, and the constant term is
nonnegative. Hence P>=0, so c*x>=0 and x>=0.

This rule requires neither c=1 nor a quotient witness. All premises are
literal coefficient/sign/parity conditions, together with previously
certified coordinate signs. It is valid on every integer assignment
satisfying the row. In particular, a square on the right needs no sign
guard on its underlying variable.

For each parent, enumerate every row's nonzero linear monomial c*x.
It gives an available rule precisely when x occurs nowhere else in that
row and all other coefficients have the opposite weak sign. This is a
finite exhaustive enumeration of this stated rule class. It does not
use `kind=gate` or any compiler annotation.

Select as seeds exactly the coordinates which are not the conclusion
of **any** such rule. All four parents have 234 seeds. Starting from
their nonnegativity, the supplied ordered row certificate derives all
remaining coordinates:

| Natural parent | Available rules | Distinct conclusion coordinates | Seed signs | Ordered inferences |
|---|---:|---:|---:|---:|
| 522 | 289 | 288 | 234 | 288 |
| 529 | 296 | 295 | 234 | 295 |
| 596 | 363 | 362 | 234 | 362 |
| 895 | 708 | 661 | 234 | 661 |

Each `NONNEGATIVITY.json` step contains a coordinate and an actual parent
row index. The independent checker reconstructs that row, its positive
multiplier, every RHS coefficient, and every odd-power dependency. It
requires each dependency earlier in the certificate and checks complete
coverage. Compiler metadata is not a premise of any inference.

There is a narrow minimum statement: within this exact output-free
linear-conclusion/nonnegative-RHS rule class on these fixed rows, the
234 seeds are necessary because no inference can conclude them, and
they suffice by the displayed closure. This is not a minimum over all
valid sign arguments, other row combinations, other encodings, or all
Diophantine equations.

## 3. Quadratic guards for the 234 seeds

For each seed coordinate x, retain x as an unrestricted integer and add
three fresh unrestricted integers a,b,c and the residual

```
x-a^2-b^2-c^2-c.
```

Its zero condition is `x=a^2+b^2+c(c+1)`. This forces x>=0: for an integer
c, either c>=0 or c<=-1, and in either case c(c+1)>=0.

Conversely every natural x has such a representation. The positive odd
number 4x+1 is 1 or 5 modulo 8, and hence is not of Legendre's excluded
form `4^r(8s+7)`. By the three-square theorem it is a sum of three integer
squares. Modulo four exactly one of these coordinates is odd. Reorder
it last and write the representation as

```
4x+1=(2a)^2+(2b)^2+(2c+1)^2.
```

Dividing by four after cancelling the constant gives the desired
identity. This includes x=0. Only seed variables need these guards;
the ordered row derivation supplies every other original coordinate.

## 4. Exact equivalence of zero existence

Let r_j be the original quadratic residuals, G the set of 234 seeds,
and g_i the new guards. The actual integer equation is

```
Q_Z = sum_j r_j^2 + sum_(i in G) g_i^2 = 0.
```

At an arbitrary integer zero, every summand is nonnegative, so every
individual residual vanishes. The guards first prove all seed signs.
Induction through `NONNEGATIVITY.json`, using Section 2, proves all
original coordinates nonnegative. Project away the fresh auxiliaries;
the unchanged parent rows now give an actual natural zero.

Conversely, given any natural zero of the parent, choose each seed's
three-square witnesses from Section 3. The complete original assignment
and these fresh coordinates make all old rows and all new guards zero.
This establishes existence equivalence. It is not a unique-lift claim.

The original residual prefix is unchanged. Every new residual is
quadratic; no square is substituted into an old row, so degree eight
does not arise. A fresh guard auxiliary occurs nowhere else and has
fourth-power coefficient exactly one in Q_Z, proving exact degree four.
No native tuple, machine simulator or universal polynomial is introduced.

Composing with the independently reviewed parent's explicitly inherited
ordinary calibration gives the same zero/refutation equivalence. Neither
this transformation nor that equivalence establishes Con(ZFC), absence
of zeros, or an internal object-ZFC derivation.

## 5. Literal results

| Variant | Parent naturals | Integer variables | Quadratic residuals | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|---:|
| integer1224 | 522 | **1,224** | **634** | **4** | 23,590 | 83,900,628 |
| integer1231 | 529 | 1,231 | 641 | 4 | 14,148 | 211,184,624 |
| integer1298 | 596 | 1,298 | 708 | 4 | 10,628 | 63,909,160 |
| integer1597 | 895 | 1,597 | 1,007 | 4 | **8,232** | **63,908,265** |

Each adds exactly 702 fresh integer auxiliaries. All variable lists and
fully collected coefficients are materialized; all coordinates occur.
The delivered integer2088 parent companion had 922 rows, 26,791 terms
and height 83,901,150. The 1,224-variable result strictly improves its
variables, rows, term count and height at the same degree. The other
variants give further term/height choices rather than being conflated
with the fewest-variable point.

The generator uses the unchanged frozen `rules_from_rows` and `close`
functions in `tools/build_shared_crt_row_guards.py`, SHA256
`dee810ff01606cdaa91e477360bd7106f3405e9adc4e026c549e9ed80bb2fbf5`.
The independent checker imports neither that tool nor any natural
compiler. It separately enumerates all admissible conclusion variables,
verifies every ordered sign step and guard binding, reconstructs every
complete polynomial using an unordered-pair SOS expansion, and checks
the original prefix, variable liveness and the exact fourth-power
coefficient. It rejects four deliberately corrupted sign certificates.
Finite controls represent x=0,...,1000 by the guard; the unbounded
completeness proof uses Legendre's theorem as stated above.

Normal and optimized generator `--check` and independent-checker runs
all passed. `CHECK.json`, `CHECK_OPTIMIZED.json`, `VERIFICATION.json`
and `MANIFEST.json` retain the exact results. No acceptance condition
depends on Python assertions, and no Lean process was run.
