# A 31-operation timed certificate for the uniform binary shuttle

For source 18's explicit binary mass-four orbit, the complete polynomial can
be evaluated in **31=8M+23A operations**, with **two natural witnesses and exact
degree four**. It represents the same complete timed configurations as the
four-witness seven-square certificate, uniformly in the natural gap parameter.
At integer external coordinates it also has the same empty or singleton
nonnegative-real witness fibers. The final polynomial is nonnegative on that
integer external interface; it is not a sum of squares or nonnegative for
arbitrary real external coordinates.

This is an explicit decidable family, not a Turing-complete machine or a
generic normal-form compiler. It does not change the established universal
polynomial bound of 84 operations. The [source-18 intake](review_timed_four_mass_source18_intake.md)
reviews the conditional chart proof and the original compact certificate.
The present [fresh helper](timed_binary_shuttle18_projection.py) and
[receipt](timed_binary_shuttle18_projection.json) emit and compare six complete
arithmetic sources without importing or executing the delivered code.

## 1. External domain, exact orbit and the paid baseline

Let the external parameters x,t be natural integers. The initial gap is
d=7+x, and the four external integer positions are x0,x1,x2,x3. Their zeros
will automatically be ordered natural positions. They specify the complete
four-particle binary configuration, with every other site vacuum. Time t
is external, and the initial configuration is (0,3,4,d).

At cycle n≥0 write h=x+n+1 and T(n)=n²+(2x+3)n. For e=0 or 1 and
0≤j≤h, the inherited explicit orbit charts are

```
t  = T(n)+j+e*(h+1),
x0 = 0,
x1 = 3+j+e*(h−1−2j),
x2 = 4+j+e*(h−2j),
x3 = d+n+e.
```

The two phase intervals are consecutive: the first is
`[T(n),T(n)+h]`, the second `[T(n)+h+1,T(n)+2h+1]`, and
`T(n+1)=T(n)+2h+2`. They partition natural time uniquely. The displayed
positions are strictly ordered for h≥1. These are source 18's binary
charts, not a newly implemented simulation or proof of the general
mass-four normal form.

The four natural witnesses e,n,j,u use u=h−j. The seven residuals are
Booleanity B=e(e−1), the domain h−j−u, the clock equation, x0 and the three
remaining position equations. Their sum of squares is exactly the frozen
compact polynomial. The helper directly reconstructs all seven formulas;
its 73 coefficients agree with that algebra. The source intake independently
compares those same 73 coefficients with the delivered exported polynomial.

Our baseline shares h−j between the domain and the first position formula,
and shares the predicted first position with the second. Its full ledger,
including seven squares and their sum, is **39=11M+28A**. This is a declared
paid schedule for the original polynomial; the delivered seven-square count
was not itself an operation count or an optimal circuit claim.

The helper pins the delivered compact module and audit note, respectively:

```
9243fa208603c59285ded9d25e4493beeeadf9d90508ea7cfa615f6add7b15d4
ce4f6cdadf548b55a00fa981f140f870ebd0fab396f164ee2a5eb4c143b50a1a
```

Both are under the signal-machine collision report's unchanged source-18
evidence. The intake supplies the exact publication and wider read scope.
No trajectory counts from the historical suites are relabeled as fresh tests.

## 2. Remove the cycle witness, preserving the natural domain

Compute `n=x3−d−e`. The last position residual now vanishes identically.
Keeping natural e,j,u and substituting this affine expression gives an
exact whole-polynomial pullback with six square slots. All residuals
remain quadratic. The direct projected source costs **36=10M+26A**.

The missing naturality of n must be proved. At any projected zero,
Booleanity gives e∈{0,1}. Integer external positions make restored n an
integer, and h=j+u≥0 gives n≥−x−1. If n<0, then −x−1≤n≤−1. Since
0≤j≤h and e≤1, the clock gives

```
t ≤ n²+(2x+5)n+2x+3
  = (n+1)*(n+2x+4)−1 < 0.
```

The first factor is nonpositive and the second at least x+3>0. This
contradicts natural external t. Therefore n≥0, and the literal inverse
restores a natural original zero. Forgetting or restoring n is a bijection
of full natural zero fibers at the same external tuple. This argument is
independent of an assumed accepted orbit or a pre-existing inverse map.

The natural-time hypothesis is essential. At x=0,t=−1 and positions
(0,2,4,7), the projected tuple e=1,j=u=0 is a zero but restores n=−1.
The helper evaluates every projected complete source at this excluded-domain
boundary, rather than relying solely on a stated sign caveat.

## 3. Share the projected clock without Boolean substitutions

Put L=x3−6, so h=L−e and n=L−e−x−1. The exact all-value identity

```
n*(h+x+2)+e*(h+1)
    = (L−x−1)*(L+x+2)−e*L
```

cancels the two e² terms identically. It holds over every commutative ring,
without imposing Booleanity. Replacing only this clock computation preserves
the entire three-witness polynomial and lowers its ledger to
**35=10M+25A**.

## 4. Remove the phase witness, with an explicit square correction

The two middle-position predictions differ by 1+e. Compute
`e=x2−x1−1` and retain B=e(e−1). At any zero, e is therefore zero or one
and is a natural value. The inverse restores exactly the missing phase.

Under this substitution, the second position residual becomes identical
to the first residual R1; it does not vanish. Keeping two copies of R1²
gives the exact full-polynomial pullback in **33=9M+24A** operations, with
only the natural witnesses j,u. The square is computed once and its value
is used twice in the fully paid final sum.

Dropping one duplicate produces the complete five-square polynomial P32
at **32=9M+23A**, with the exact all-value relationship

```
P33 = P32+R1².
```

Both are sums of nonnegative real squares and both retain R1². Consequently
their zero sets agree over real supplied coordinates. This is zero
equivalence with a known correction, not equality of the two polynomials.
Combined with Sections 2–3, the two-witness natural zero fibers are in
bijection with the original four-witness fibers at the same allowed input.

## 5. Pay Booleanity once on the integer external interface

In the two-witness source, e=x2−x1−1 is an integer **before any equation is
imposed**, because all external positions are integers. Thus B=e(e−1)≥0.
Its zero set consists exactly of e=0 or 1. Replace the summand B² by B,
retaining all four other squares. The result is

```
P31 = B + domain² + clock² + x0² + R1²,
P32−P31 = B²−B.
```

The correction is an all-value polynomial identity. On the integer external
interface each summand in P31 is nonnegative, even when j,u are real. Hence
P31=0 if and only if B=0 and all other residuals vanish, exactly the zero
condition for P32. This saves one multiplication. It yields the complete
ledger **31=8M+23A**, including all output assembly.

This reasoning does not give nonnegativity at noninteger external positions.
For x=0,t=1, positions (0,3,9/2,15/2) and j=0,u=1, every other residual
vanishes but e=1/2. The complete output is −1/4. The helper checks this
excluded-domain example. In particular P31 must not be described as a sum
of squares or as a polynomial nonnegative throughout the real orthant.

## 6. Real witness exactness, uniqueness and complete evidence

At an allowed integer external tuple, a nonnegative-real zero of any of the
six sources has Boolean e. Restored n is integer from the last position;
Section 2 forces its nonnegativity when it was eliminated. The first
position equation gives `j=x1−3` on phase zero or `j=h+2−x1` on phase one.
Thus j is integral; the domain gives integral u=h−j. Every nonnegative-real
zero is therefore natural. Conversely every natural zero is a real zero.
The inherited disjoint time charts, or the unique phase and cycle recovered
from the spatial data, prove the empty/singleton fiber assertion. No
unrestricted signed-witness claim is made.

| Complete source | M | A | Total | Natural witnesses | Final summands |
| --- | ---: | ---: | ---: | ---: | --- |
| Original compact polynomial | 11 | 28 | 39 | 4 | 7 squares |
| Cycle projected | 10 | 26 | 36 | 3 | 6 squares |
| Exact clock identity | 10 | 25 | 35 | 3 | 6 squares |
| Phase projected, duplicate retained | 9 | 24 | 33 | 2 | 6 square slots |
| Duplicate removed | 9 | 23 | 32 | 2 | 5 squares |
| Integer Boolean term | 8 | 23 | **31** | **2** | B and 4 squares |

All six sources have exact degree four; the coefficient of n⁴ in the
original and of x3⁴ in every projected polynomial is one, including on
each fixed gap slice. No minimality among circuits or certificates is claimed.
The receipt saves every source row, residual polynomial and complete output
coefficient. It checks all 206 paid gates and supplied-port liveness, the
literal seven-row baseline, exact cycle and phase pullbacks, exact clock
identity, and both complete-output corrections.

Fresh bounded arithmetic checks construct 1,026 complete chart states over
five gaps and nine cycles, giving 6,156 full natural zero evaluations. They
also compare 144 complete rational evaluations with the direct formulas
and verify 5,850 negative-cycle phase cases. These samples corroborate the
general proofs; they do not prove the underlying radius-six rule theorem,
run its archived simulator, or implement a generic orbit classifier.

From any working directory:

```sh
python3 timed_binary_shuttle18_projection.py --repo-root ABS_REPO --expect ABS_RECEIPT
python3 -O timed_binary_shuttle18_projection.py --repo-root ABS_REPO --expect ABS_RECEIPT
```

All checks use explicit exceptions and type-exact receipt comparison.
The result remains a uniform-gap certificate for this explicit binary
orbit, with a required natural external clock, rather than a universal
Diophantine equation or a first-hit certificate for arbitrary observations.
