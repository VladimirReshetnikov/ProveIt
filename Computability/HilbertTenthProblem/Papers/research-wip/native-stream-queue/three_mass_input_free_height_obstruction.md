# Input-free height destroys the four direct clean-clock representations

Deleting the initial encoded input from the height saves one addition in each
complete direct clean-clock source, producing totals **596/471/469/472**.
Every one of these four candidate polynomials is unsound: it has full positive
witness zeros at infinitely many false fixed-clock input pairs. The proof is
an exact polynomial symmetry applied to genuine parent zeros, whose positive
native extensions exist by the already reviewed parent theorem. The numerical
fixtures below materialize only the outer histories and joined AND inputs;
they do not materialize enormous full native Pell tuples.

This is an obstruction to these four literal deletions. It is not a lower
bound on other height formulas, a universal compiler bound, or an objection
to the unchanged sound direct clean-clock parent. The separate Report 18
intake motivates examining exact clocks but is not a dependency of this
counterexample theorem.

## 1. Pinned sources and the one-gate change

The immediate parent is `three_mass_direct_clean_clock`:

- Python: `9627ffd85f79e5ed2c0174f716e95afcf1f92c0f3035e65c76aaa15f98af34b6`
- Receipt: `a360d1573dfb12b2e5fb3188bdce3a36e7029c4fc13b86b61969f34d2644b7d1`
- Proof: `59efd3d56b794f8632c1da48c080083a750895e9897bf213662195e45861167c`

The new helper authenticates those bytes, the parent source review, all
inherited parent dependencies, and the three Report 18 proof/audit/trace
inputs listed in its `dependency_pins`. It reads JSON and Markdown bytes as
data. It does not import or execute any predecessor or archive Python.

The free natural coordinates are `x,U`; all existing witnesses remain strictly
positive integers. Write `F=clean_final_payload`, `eta=height_slack`, and
`khat=clock_quotient_hat`. The literal bridge has

\[
 n_0=5x+1,\qquad n_f=5F+q_h-5,\qquad
 h=n_0+\eta+U,\quad B=262144h^2.
\]

The candidate deletes the private row
`bridge_height_without_time = bridge_input + height_slack` and replaces its
sole consumer by `height = height_slack + U`. Thus the new height is
\(h=\eta+U\). Every other body row, comparison pair, supplied coordinate,
and finalizer row is unchanged. In particular the radix multiplier remains
262144; no native or range coordinate is dropped. The nineteen-comparison
SOS finalizer still costs 56 gates.

| Literal source | M | A | Total | Positive witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| inc2;dec2 | 237 | 359 | 596 | 59 | 19 | 2344 |
| zero3 | 182 | 289 | 471 | 57 | 19 | 1192 |
| nop | 180 | 289 | 469 | 57 | 19 | 1192 |
| positive3 | 187 | 285 | 472 | 57 | 19 | 1192 |

All 2,008 emitted gates and all supplied coordinates are output-live. Exact
degrees follow from formal upper propagation and a nonzero matching output
coefficient after coordinate `i` is replaced by `(i+2)z`, modulo 1,000,003.
The four coefficients are 490378/401389/401389/401389. Intermediate formal
bounds are not lowered if their specialized coefficient vanishes.

## 2. Whole parent identity under the positive height lift

Let \(Q_P\) be the actual parent SOS polynomial and \(Q_C\) the candidate.
For every scalar tuple, set

\[
 \eta_C=\eta_P+n_0
\]

and leave all other supplied coordinates fixed. The computed heights agree,
and hence every retained register, comparison residual and finalizer agrees:

\[
 Q_C(x,U,F,\eta_P+n_0,\ldots)
   =Q_P(x,U,F,\eta_P,\ldots).                       \tag{1}
\]

This is a full polynomial graph identity, not a zero-only consequence. The
literal consumer audit establishes that the old intermediate has only the
height consumer and that the slack has only that intermediate consumer.
Local associativity therefore extends to every downstream register. On the
natural-input/positive-witness domain, \(n_0>0\), so (1) is a positive lift
of every full parent zero to a full candidate zero.

There is no assertion that arbitrary positive candidate zeros lift back to
the parent: the proposed inverse would subtract \(n_0\) from the slack.

## 3. An exact full-polynomial symmetry of the candidate

Let \(J\) be the sum of the nonnegative selector words and
\(P=(B-1)J+1\) the already-paid scale. In the candidate, \(B,P\), every
packed current/next word, and every native register are independent of
`x,F,khat`. This is checked from the complete literal consumer graph.
The only relevant endpoint/clock equations are

\[
 B N_{word}+n_0=C_{word}+P n_f,                     \tag{2}
\]
\[
 2C_\tau+192(x+F)+208=(B-1)(\widehat\kappa-1)+U.  \tag{3}
\]

The other seventeen residuals depend on none of the three changed ports.
For any scalar parameter \(r\), define

\[
 x'=x+rP(B-1),\quad F'=F+r(B-1),\quad
 \widehat\kappa'=\widehat\kappa+192r(P+1).        \tag{4}
\]

Keep `U`, the height slack, and every other witness fixed. Consequently
\(B,P\) remain fixed. The two sides of (2) each increase by
\(5rP(B-1)\). The two sides of (3) each increase by
\(192r(P+1)(B-1)\). Thus every one of the nineteen residuals is identical
before and after (4), and

\[
                         Q_C(x',U,F',\widehat\kappa',\ldots)
                          =Q_C(x,U,F,\widehat\kappa,\ldots).    \tag{5}
\]

The identities hold over every commutative ring; no equation, positivity,
native classification, or height bound is needed for (5). The helper proves
the literal nineteen residual identities at unaffected register cuts by
exact sparse polynomial arithmetic, using the actual relation `Bminus1=B-1`.
Its checked instance is `r=1`; iteration gives every natural `r`, and the
displayed affine calculation proves arbitrary scalar `r` directly.

On the supplied integer domain, \(h=U+\eta\ge1\), so \(B>1\).
The positive selector hats make \(J\ge0\) and \(P\ge1\).
For positive integer \(r\), (4) only increases the three changed
coordinates and therefore preserves their required domains. In particular
it preserves full positive candidate zeros, with all native witnesses fixed.

## 4. Full positive false-clock zeros, without a fabricated Pell tuple

Choose a genuine accepted input for one of the four parent machines. The
parent theorem supplies full positive witnesses at every sufficiently large
dyadic height. It first packs a genuine finite first-halt history, obtains
the prescribed joined AND, and then uses the inherited positive native
extension theorem. The height and global slacks are positive by the parent
completeness bounds. This use of the parent theorem is legitimate: it occurs
at the genuine input and its true clean time before any change of input.

Apply (1), then (4) with any positive integer \(r\). These produce full
positive candidate zeros at the original fixed value of `U`. For the genuine
seed with \(t\ge1\) source steps, \(P=B^t>B^0=1\). All four machines
preserve the raw input payload overall, so their actual final payload is
\(N=x+1\). Their true first clean-target times are

\[
 L_{inc;dec}(x)=1584(x+1)+48,
 \qquad L_{zero3/nop/positive3}(x)=768(x+1)+32.      \tag{6}
\]

For the two guarded machines, `zero3` accepts when 3 does not divide `x+1`,
and `positive3` accepts when it does. Dyadic \(h\) gives
\(B=2^{18}h^2\equiv1\pmod3\). Hence the input increment in (4) is a
multiple of 3, preserving both guards. The inc/dec and NOP fixtures have
no input guard. Thus the shifted inputs still have genuine first halts,
but (6) strictly increases while the candidate's requested `U` is fixed.
They are false zeros for the claimed first clean-clock relation.

Also \(F'=x+1+r(B-1)\) differs from the actual shifted final payload
\(x'+1=x+1+rP(B-1)\), since \(P>1\). The native words continue to
describe the original genuine short history, while the two endpoint and
clock equations admit its algebraic shear. This identifies the lost
chronological low-digit bound: the new \(n_0\) is no longer below \(B\).

Every fixed genuine seed yields infinitely many distinct raw-input parameters
at the fixed requested time. This is a parametric full-zero theorem, not an inference from the
four small outer fixtures. It refutes soundness even on positive tuples,
without claiming that the candidate accepts every input/time pair.

## 5. Concrete NOP outer fixture

Take the genuine parent input and clock

\[
 x=0,\quad F=1,\quad U=800,\quad \theta=200,\quad h=1024.
\]

Then \(n_0=1\), parent slack is 223, candidate slack is 224,
\(B=P=2^{38}=274877906944\), and \(\widehat\kappa=1\).
The `r=1` shear gives

\[
 x'=B(B-1)=75557863725639445512192,\quad F'=B,
 \quad\widehat\kappa'=1+192(B+1)=52776558133441.
\]

The original one-step packed current/next encoded values are 1 and 2.
Both sides of transport (2) become \(5B^2-3B+1\); both sides of clock
(3) become \(192B^2+608\). The global row and all native inputs remain
unchanged. The true clean time of the shifted input is
58028439341291094153364256, whereas the candidate still has `U=800`.
Its would-be restored parent slack, \(224-(5x'+1)\), is negative.

The receipt also checks genuine outer seeds for the other three machines.
It supplies explicit selector/quotient/global/clock values, verifies the
three outer equations and full joined AND, and checks that every native
register is unchanged by the shear. Native witness placeholders in these
numeric fixtures are not claimed to solve the native equations. Their
positive solvability, including at the displayed sufficiently large seed
heights, is supplied by the pinned parent completeness theorem.

## 6. Replay and precise exclusions

The bounded helper saves all four complete arrays and their exact ledgers,
checks closure and liveness, proves 76 residual shear identities, and records
the four outer seed/shift pairs. Its explicit exception checks remain active
under optimized Python. Receipts are compared recursively with exact types
after a JSON roundtrip. From any working directory:

```
python3 /path/three_mass_input_free_height_obstruction.py --repo ABS_REPO \
  --expect /path/three_mass_input_free_height_obstruction.json
python3 -O /path/three_mass_input_free_height_obstruction.py --repo ABS_REPO \
  --expect /path/three_mass_input_free_height_obstruction.json
```

The writer and fresh exact receipt replays from `/` passed in both normal
and optimized Python.

There is no maintained public compiler API, historical suite execution,
unrestricted optimization claim, real/rational zero-exactness claim, or new
ordinary-input loader. The earlier time-free-height obstruction changes a
requested time while removing its height bound. Here the requested clean
time remains height-bounded and fixed; removing the **input** term permits
an endpoint/clock shear. These are different source-specific failures.
