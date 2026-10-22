# A 79-variable quartic, or 70 quadratic equations

The explicit ordinary-strong system in `fixed_input63_ordinary_system.json`
has 16 strictly positive primary unknowns, 63 arithmetic gates and seven final
equations. It has an equivalent presentation using **79 nonnegative integer
unknowns and 70 equations of degree at most two**. The sum of the 70 squared
residuals is a **single ordinary polynomial of exact degree four**, with the
same nonnegative solvability predicate. Its expanded sparse expression has
286 terms before substituting the fixed compiler numerals.

This transformation does not change the recommended 16-variable system or
its source. It supplies a separate degree/variable tradeoff. Coefficients use
the same five fully specified integers `Bm1,Kconstant,MC,MF,W0`.

## 1. Why a direct natural-variable circuit lift needs an audit

An arbitrary integer circuit may have negative intermediate values even at
solutions. Requiring all gate outputs to be natural numbers can then destroy
solutions. For the present circuit, every intermediate at a genuine positive
solution is nonnegative after reversing the signs of precisely two registers.
This fact uses the whole solution conditions and the admissible coefficient
recipe. It is not claimed on arbitrary positive assignments.

In the original circuit, let `H2=V^2`, `aux_y2=y^2`, and
`R16=K_aux`. The original final three relevant operations are

```
aux_square_gap = V^2-y^2
L17 = K_aux*aux_square_gap
norm_aux = L17+y^2.
```

Replace them by

```
aux_square_gap = y^2-V^2
L17 = K_aux*aux_square_gap
norm_aux = y^2-L17.
```

There are still 63 gates. The polynomial `norm_aux` is unchanged identically
over every commutative ring; the two internal registers change sign, and all
other registers are unchanged. Thus the seven final residuals are identical
polynomials on all supplied tuples, including tuples that are not solutions.

## 2. Nonnegativity of every subtraction

Use the notation of the main proof:

\[
q=(B-1)J+1,\quad X=wq,\quad Y=sq^3,\quad E=XY,\quad
k=\eta+\zeta,\quad c=kY+\eta,\quad a=E+Y,\quad
\Delta=(a+1)(a+3).
\]

The budget comparison gives

\[
q=F+2Z+\alpha+W_0,\qquad C=Z+W_0.
\]

All primary inputs and fixed numeral ports are strictly positive. The
complete subtraction audit is:

| Gate | Value or lower bound at a solution |
|---|---|
| `norm_first` | 1 |
| `norm_main` | 1 |
| `q_minus_F` | \(2Z+\alpha+W_0>0\) |
| `q_minus_FZ` | \(Z+\alpha+W_0>0\) |
| `C_after_alpha` | \(Z+W_0>0\) |
| `index_difference` | \(R+1>0\), by `norm_index=1` |
| `Lm1` | \(q^2-1>0\), since \(q\ge B\ge16\) |
| `norm_index` | 1 |
| `norm_transport` | 1 |
| `auxiliary_Tf_minus_one` | \(Tf-1>0\), since \(T\ge1\) and \(f>1\) |
| `aux_u_rhs` | \(V>1\), by the auxiliary positivity proof below |
| modified `aux_square_gap` | \(y^2-V^2>0\) |
| `f2_minus_one` | \(f^2-1>0\) |
| modified `norm_aux` | 1 |

This list contains every subtraction in the modified source. All remaining
gates are sums or products of already nonnegative inputs, so induction in the
literal gate order proves nonnegativity of all 63 outputs. In fact all these
outputs are strictly positive, although only nonnegativity is needed.

### The auxiliary positivity argument for the ordinary-strong source

The ordinary strong equation is

\[
(ic^2)^2=\Delta(f^2-1),\qquad
K_{\rm aux}=\Delta(f^2-1).
\]

It does **not** directly give the normalized source's bound \(f>c^2\).
The proof must use the preliminary first/main Pell estimates first. Those
estimates, derived independently of the sign of \(V\), give

\[
c>(a+2)\Delta^2,\qquad R<a<\Delta.
\]

Since \(i\ge1\) and \(\sqrt\Delta<a+2\), the strong equation gives

\[
f>\frac{c^2}{\sqrt\Delta}>\frac{c^2}{a+2}>2c.
\]

Also \(c>\Delta+1\), so \(f^2>\Delta+c\), and therefore

\[
K_{\rm aux}-(Rf^2+c)
 =(\Delta-R)f^2-\Delta-c>0.
\]

The auxiliary equation is

\[
K_{\rm aux}V^2-(K_{\rm aux}-1)y^2=1.
\]

If \(v=|V|>1\), it implies

\[
v^2-1=(K_{\rm aux}-1)(y^2-v^2)>0,
\]

and thus \(y\ge v+1\) and \(v\ge2K_{\rm aux}-1\).
But \(T>0\) and the explicit formula
\(V=c(Tf-1)-Rf^2\) give
\(V>-Rf^2-c>-K_{\rm aux}\). These inequalities exclude negative
\(V\) with \(|V|>1\). The case \(V=0\) fails the auxiliary equation.
The cases \(V=\pm1\) fail
\(V\equiv-c\pmod f\), because \(2<c<f/2\). Hence \(V>1\), and
the auxiliary equation then gives \(y>V\), proving the positive gap.

The preliminary Pell estimates are an inherited part of the ordinary-strong
soundness proof. This lift does not add an independent unproved positivity
assumption: the main theorem proves them at every positive solution on the
admissible coefficient slice, before using any positive auxiliary witness.

## 3. Explicit quadratic equations

For each of the 16 original positive variables \(x_j\), introduce
\(v_j\in\mathbb N\) and substitute \(x_j=1+v_j\). For each of the 63
gate outputs introduce a new variable \(g_r\in\mathbb N\). A literal gate

\[
r=u+v,\qquad r=u-v,\qquad r=uv
\]

becomes respectively

\[
g_r-\widehat u-\widehat v=0,\qquad
g_r-\widehat u+\widehat v=0,\qquad
g_r-\widehat u\widehat v=0.
\]

Here \(\widehat u\) is its fixed coefficient if the operand is constant,
\(1+v_j\) if it is a primary variable, and its own gate variable if it is
an earlier output. Thus every gate equation has degree at most two in the
79 unknowns. The final seven comparisons are affine equations between gate
variables and literals. There are \(16+63=79\) unknowns and \(63+7=70\)
equations.

The construction emits all 70 residuals explicitly in `quadratic_lift.json`.
Coefficients are signed integers or polynomial expressions in the five fixed
numeral ports, whose actual integer values are specified by the coefficient
recipe. Those ports are not additional unknowns.

### Both directions of the equivalence

Given a solution of the original 16-variable system, set \(v_j=x_j-1\) and
evaluate the sign-adjusted circuit. Section 2 proves that every resulting gate
value is a natural number. This gives a solution of all 70 equations.

Conversely, any natural solution of the 70 equations gives positive primary
inputs \(1+v_j\). Induction in topological gate order shows that every
\(g_r\) equals the corresponding evaluated output. The seven final equations
are therefore exactly the original seven comparisons. This direction requires
no separate positivity lemma and yields no spurious solutions.

Thus the new system has a solution if and only if the ordinary-strong source
has a positive solution, hence if and only if K215 halts blank and ZFC is
inconsistent, under the main construction's stated proof dependencies.

## 4. A single explicit quartic

Let \(E_1,\ldots,E_{70}\) be the emitted quadratic residuals. Define

\[
Q(v_1,\ldots,v_{16},g_1,\ldots,g_{63})
 =\sum_{r=1}^{70}E_r^2.
\]

On integer or natural assignments, \(Q=0\) is equivalent to the simultaneous
vanishing of every \(E_r\). The degree is at most four, and is exactly four:
the first gate residual is

\[
g_{\text{tau\_square}}-(1+v_{\text{tau\_root}})^2,
\]

whose square contributes the monomial \(v_{\text{tau\_root}}^4\) with
coefficient 1. No other residual changes that coefficient. The expanded
quartic, included in the JSON, has exactly 286 nonzero formal terms before
specialization of the five coefficient ports. This is an explicit quartic,
not an appeal to a general existence theorem.

## 5. Executable checks and their scope

Run beside the source JSON:

```
python3 quadratic_lift.py
```

Or pass its path with `--source`. The command writes `quadratic_lift.json`
and `quadratic_lift_checks.json`. The script uses only Python's standard
library and uses explicit exception checks rather than removable assertions.

The recorded validation proves the local sign identity by exact sparse
polynomial arithmetic, verifies the equation and variable counts, expands
the quartic, and checks its exact degree and distinguished coefficient.
It also compares both circuits on 64 signed assignments, verifies 4032
gate residuals and 448 final residuals, and evaluates the expanded quartic
on each resulting assignment. These are all-value arithmetic controls;
their small diagnostic numeral assignment is not claimed to compile a
valid machine. No actual positive K215 solution was constructed.

The nonnegativity theorem is the mathematical proof in Section 2, not a
conclusion drawn from testing a finite collection of purported solutions.
No new Lean or Rocq proof is claimed by this artifact.

