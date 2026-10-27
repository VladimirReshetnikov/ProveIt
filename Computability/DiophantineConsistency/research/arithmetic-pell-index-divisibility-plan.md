# Proposed final ordinate-to-index divisibility

Read-only plan, 2026-10-27. Proposed pair:
`ArithmeticPellIndexDivisibility.lean` and focused Checks, importing only
`ArithmeticPellIntegralSolution`. No Lean source, overlay, or compiler has
been created for this proposal. IntegralSolution remains explicitly
provisional in this frozen inventory pending ROOT's accepted supplement.

All arithmetic is inside an arbitrary `ORingStructure V` satisfying IΣ1.
Write `A=a+2`, `D=delta a`, `X_j=xcoord j a`, `Y_j=ycoord j a`.
The actual norm gives `A*A=1+D`. This plan uses ROOT's two-certificate
simplification; no cubic congruence, power sequence or gcd quotient is needed.

## Exact proposed endpoints

The core certificate and divisibility theorem are:

```lean
theorem index_certificate (a j : V) :
    ArithmeticGcdNormalization.Bez (ycoord j a) (delta a) j

theorem ordinate_divides_index (a p m : V)
    (hpm : p∣m)
    (hdiv : ycoord p a*ycoord p a∣delta a*ycoord m a) :
    ycoord p a∣m
```

The latter deliberately includes both zero indices. It splits `p=0`
before constructing a shifted base. If `p=0`, `hpm` forces `m=0`, so
the conclusion is immediate. The positive branch derives all required
positivity internally. No coprimality, unit, quotient certificate,
index parity, or further norm hypothesis is supplied.

The actual completed relaxed-norm endpoint is:

```lean
theorem relaxed_auxiliary (a c p i f : V)
    (hp : 0<p) (hi : 0<i) (hf : 0<f)
    (hcp : c=ycoord p a)
    (hnorm : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hbig : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ f=xcoord m a ∧ p∣m ∧ c∣m ∧
      i*c*c=delta a*ycoord m a
```

A literal-input adapter replaces `hnorm` by
`(i*c*c)*(i*c*c)=delta a*(f*f-1)` and uses the existing justified
`integral_solution_tsub` endpoint. These endpoints first obtain the actual
same `m` from IntegralSolution, then derive `c*c∣delta a*ycoord m a`
using its equality and the witness `i`, and apply the new index theorem.
No `c∣m` assumption is hidden in the imported IntegralSolution statement.

## Internal quotient recurrence, with every coefficient nonnegative

It suffices to prove the following actual Σ1 disjunction at every internal
`j`, without adding parity syntax or importing the broader Congruences or
Periodicity modules:

- even-shaped branch: `∃u v, X_j=1+D*u ∧ Y_j=A*j+D*v`;
- odd-shaped branch: `∃u v, X_j=A+D*u ∧ Y_j=j+D*v`.

This is a statement about exact natural quotients, not just sampled
remainders. A genuine Σ1 successor induction proves the disjunction.
At `j=0`, choose the even-shaped branch with `u=v=0`.
The actual represented recurrence swaps branches. More explicitly:

- From the even-shaped branch, at `j+1` choose the odd-shaped branch
  with `u'=A*u+A*j+D*v`, `v'=u+j+A*v`.
- From the odd-shaped branch, at `j+1` choose the even-shaped branch
  with `u'=1+A*u+j+D*v`, `v'=u+A*v`.

Each identity follows by substitution into `x_succ` and `y_succ` and the
literal polynomial identity `A*A=1+D`. All proposed quotients are sums
and products of natural model elements. No subtraction, division, power
function or standard-index recursion is involved. The branch labels
explain their alternating origin; the exposed theorem need only claim
the disjunction, not an unproved identification with `j%2`.

For the odd-shaped branch, `Y_j=j+D*v` gives
`j+D*v=Y_j`, hence `Bez Y_j D j` with coefficients `(0,v,1,0)`.
For the even-shaped branch, `Y_j=A*j+D*v` gives
`A*Y_j=j+D*(j+A*v)`, hence the same certificate with coefficients
`(0,j+A*v,A,0)`. This includes `j=0` and requires no sign restriction
on any coefficient beyond the natural domain.

## The shifted base and first divisibility

In the positive `p` branch of `ordinate_divides_index`, put `c=Y_p(a)`
and `F=X_p(a)`. Actual `time_le_y` gives `c>0`; actual `y_lt_x` gives
`c<F`, so `1<F` and then `2≤F`. Define `B=F-2`. Only after deriving
that bound use the justified identity `B+2=F`.

From the actual norm at `p` and `(B+2)^2=1+delta B`, addition
cancellation yields `delta B=D*c*c`. Apply the accepted represented
composition theorem with arguments `(B,a,p)` and the equality
`B+2=X_p(a)`. At every internal `k`, it gives
`Y_k(B)*c=Y_(p*k)(a)` (and a first-coordinate identity not needed here).

Choose `k` with `m=p*k` from `hpm`. The given `c*c∣D*Y_m(a)` has
an actual quotient `v`, so after the composition rewrite:

`c*(D*Y_k(B)) = c*(c*v)`.

Cancel the proved nonzero `c` to obtain `D*Y_k(B)=c*v`. Thus
`c∣D*Y_k(B)`. Also `c∣delta B`, with the explicit witness `D*c`.
The case `k=0` needs no separate positivity and is retained.

## Two natural Bezout certificates finish the proof

The already existing convention is

`Bez x y g := ∃u v w z, g+x*u+y*v=x*w+y*z`.

Two elementary scaling transformations are valid even when the scale is
zero:

- multiplying `Bez x y g` by `s` and absorbing `s` into the second
  coefficients gives `Bez (s*x) y (s*g)`;
- multiplying it by `s` and absorbing `s` into the first coefficients
  gives `Bez x (s*y) (s*g)`.

Apply the first transformation with `s=D` to
`index_certificate B k`. It yields
`Bez (D*Y_k(B)) (delta B) (D*k)`.
The actual `bez_divisor` theorem and the two divisibilities above give
`c∣D*k`. This completely removes the earlier candidate's need to
cancel a power or even a single factor `F` modulo `c`.

Apply the second transformation with `s=k` to
`index_certificate a p`, rewritten using `c=Y_p(a)`. It yields
`Bez c (D*k) (p*k)`. Since `c∣c` and `c∣D*k`, `bez_divisor` now
proves `c∣p*k=m`. There is no gcd quotient, squarefree factorization,
valuation, external unit, or desired divisibility premise.

## Comparison with the source guide and scope

The complete external guide
`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/PellRelaxedMain.lean`
was read. Its Step 7 uses `xy_modEq_yn` modulo `c^3`, cancellation of
powers of `X_p`, a residue modulo `D`, and normalized gcd quotients.
The two natural certificates above replace those steps for the exact
conclusion needed. They do not claim the stronger cubic residue theorem.

The existing actual `ArithmeticPellCongruences.residue_quotients` requires
a modulus dividing `a+1`, which `D=(a+1)*(a+3)` generally does not.
`ArithmeticPellPeriodicity` handles the different first-coordinate
modulus. Both sources and the actual IOpen parity/division APIs were read;
neither module or a new boundary is needed for this plan.

The final public statement matches the relaxed auxiliary norm's
integrality and both index divisibilities at all internal indices.
It still does not prove the later target-index/step-down identity,
signed carrier alignment, cofinal witness construction, or an HA equation
endpoint. Focused checks should include `j=0`, `j=1`, both quotient
shapes, zero scale in certificate helpers if exported, `p=0`, `m=0`,
and both actual norm input forms. No new assumptions should be added
merely to simplify those zero cases.

## Exact cache inventory and source pins

The sole requested import is provisional `ArithmeticPellIntegralSolution`,
source `358d56e418a32843cd93c58266f406d49db3ae9373561ffb879307d7a0e927d1`,
author object `7814dd0443e0438a5f110beca8dee926e32a5104fa96f279936aeeaa9f29a1af`
from `/tmp/arithmetic-pell-integral-solution-author-4aqhmxqy/lib`.
Before any future compiler, a separate accepted ROOT supplement must
select its independently validated provider; this provisional inventory
must remain unchanged. The existing accepted StrongDivisibility supplement
is already applied only in memory by the read-only auditor.

The exact selected closure is 102 custom modules, 95 Foundation,
387 custom artifacts, 38 boundary modules with 114 total artifacts
(38 primaries and 76 companions), zero refresh, and 501 first providers.
The full JSON records every selected source/header/import/object and
package-boundary artifact, including implicit Init. The auditor rehashed
3,303 observations over 872 pinned paths. The mapper checked all 501
provider pairs without creating an overlay. No Foundation build or
new runtime package is proposed.

Frozen read-only artifact pins:

- `arithmetic-pell-index-divisibility-cache-audit.py`:
  `235d730f291a3813ea3f5861463433a6cff98ebe785daa1790dac57bb0c9825d`;
- `arithmetic-pell-index-divisibility-cache-plan.json`:
  `ab6f041ac993f09ef46965feb906c3445da26d9c509a13ca7522c1b4a57a8274`;
- `arithmetic-pell-index-divisibility-providers.py`:
  `a3caec142628dd68a486b62acdbc8fb85ac8cc71e28973ce16a9b7987e1e68c6`;
- `arithmetic-pell-index-divisibility-providers.json`:
  `d49ce42289f8bed210bb006fde11008527c6e9d98a1c884c2413f448d4806103`.

Both Python scripts were completely read before execution; they only
read/hash authenticated inputs and write new plan artifacts. No Lean
source, compiler, overlay, or dependency refresh occurred. Any future
pair requires ROOT approval, complete final source/driver reads,
Lean4.32 `-M6000 -j1 -DElab.async=false`, the 512MiB guard, fresh regular
outputs, and preservation of every attempt and both input snapshots.
