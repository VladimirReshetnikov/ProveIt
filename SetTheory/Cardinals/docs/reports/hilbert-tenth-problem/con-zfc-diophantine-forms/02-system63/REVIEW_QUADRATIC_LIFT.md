# Independent review of the natural-variable quadratic lift

**Result: PASS, with the explicitly stated nonnegative-integer domain.**
The lift has 79 unknowns, 70 equations of degree at most two, and an equivalent
sum of squares of exact degree four. Its equivalence to the 16-positive-variable
ordinary-strong source uses the zero-set positivity theorem, not a generic
assumption about arithmetic circuits.

The independently reviewed source is
`fixed_input63_ordinary_system.json`, SHA-256
`fae15df15460d41868db8fbc96e4d7619004e9ac04b390dcc44379a8e9ff1bfb`.
The prior ordinary-strong reduction is reviewed in
`REVIEW_ORDINARY_STRONG75.md`.

## Mathematical checks

The sole internal sign change is

\[
g=V^2-y^2\longmapsto-g=y^2-V^2,
\qquad A_0g\longmapsto-A_0g.
\]

Replacing the final sum by the corresponding difference leaves
\(A_0(V^2-y^2)+y^2\) unchanged as an integer polynomial. The other four
norm/transport comparisons, strong-square comparison, and budget comparison
are unchanged. No constraint on a primary input has been altered.

The modified circuit has exactly 14 subtractions. Their nonnegativity audit
is exhaustive:

- Five final norm/transport gates equal 1 by the source comparisons.
- The three budget differences equal respectively
  \(2Z+\alpha+W_0\), \(Z+\alpha+W_0\), and \(Z+W_0\).
- `index_difference` is \(R+1>0\), and `Lm1` is \(q^2-1>0\).
- `auxiliary_Tf_minus_one` and `f2_minus_one` are positive because \(f>1\).
- `aux_u_rhs` is \(V>1\); the changed gap is \(y^2-V^2>0\).

The latter two claims require attention. The already reviewed main-Pell
bootstrap gives \(c>(a+2)\Delta^2\) and \(R<a<\Delta\) before any
auxiliary positivity is used. From
\((ic^2)^2=\Delta(f^2-1)\), one obtains
\(f>c^2/\sqrt\Delta>c^2/(a+2)>2c\), hence
\(A_0=\Delta(f^2-1)>Rf^2+c\).
The auxiliary norm gives, for \(v=|V|>1\),

\[
v^2-1=(A_0-1)(y^2-v^2),\qquad v\ge2A_0-1.
\]

The explicit expression for \(V\) gives \(V>-A_0\), ruling out negative
\(V\) of that size. The value 0 contradicts the auxiliary norm; the values
\(\pm1\) contradict \(V\equiv-c\pmod f\), since \(2<c<f/2\).
Thus \(V>1\) and then \(y>V\). This argument does not incorrectly reuse
the stronger normalized-source estimate \(f>c^2\).

All other gates use nonnegative literals, positive fixed numeral ports,
and sums/products of prior outputs. Induction in the actual source order
therefore proves that all 63 gate outputs are nonnegative at every positive
solution on the specified compiler slice. This proves the forward direction
of the lift. Conversely, the gate equations determine every gate value in
order, so any nonnegative solution yields exactly a positive source solution
after the shifts \(x=1+v_x\). That direction needs no auxiliary positivity
assumption.

The 63 gate equations and seven comparisons give 70 residuals in
\(16+63=79\) nonnegative unknowns. Their sum of squares vanishes exactly
when all residuals vanish. Its coefficient of
\(v_{\mathrm{tau\_root}}^4\) is 1, independently of the fixed coefficients,
so its degree is exactly four. This does not assert the same acceptance
predicate when the 79 variables are instead allowed to be arbitrary signed
integers; the domain in the theorem is \(\mathbb N\), including zero.

## Independent arithmetic reconstruction

`check_quadratic_lift_review.py` does not import the producer. It reconstructs
the 70 residuals using a separate exponent-vector representation and checks
every coefficient against `quadratic_lift.json`. It then independently
expands their sum of squares and checks every one of its 286 formal terms.
The five coefficient ports are formal symbols for this comparison and are
excluded from the degree in unknowns. The 286 count is before specializing
the coefficient ports, as stated by the producer.

The review also checks the complete variable list, the occurrence of all
79 unknowns, acyclic gate order, the exact sign changes, the precise
14-subtraction coverage, maximum residual degree two, quartic degree four,
and the coefficient-independent quartic monomial. The recorded result is
`quadratic_lift_review_checks.json`.

Reviewed artifact SHA-256 hashes:

| Artifact | SHA-256 |
|---|---|
| `quadratic_lift.py` | `c0437ddaf06177a00d0ed34425ece4ba731a0f3ae894a23004de5c3cdc8c05cc` |
| `quadratic_lift.json` | `f4c658256e36df4b988d414adae7a10d0f545f3d7f8c77c8a520ce8858a0c3bd` |
| `QUADRATIC_LIFT.md` | `4c729eefee76ccdc6fe2f232b013fd00207028666226c80af3019b0dd6af466a` |

This is an exact arithmetic and mathematical review. No positive solution
for the K215 instance was constructed, and no new Lean or Rocq proof is
claimed.
