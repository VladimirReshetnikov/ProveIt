# Shared self-bounding radius for factorials and the CRT radix

**Relationship to the delivered equation.** Section 1 gives the factorial
lemma used in the final reciprocal-modulus construction, and Section 6 gives
the norm transformations. Sections 2-5 and 7 record an intermediate
two-factorial architecture. The final one-factorial architecture and its
current counts are proved in `reciprocal_moduli_proof.md`; they supersede
that intermediate architecture. The complete combined result is in the report.

## Scope

This is an existence-preserving replacement for the two independent factorial
radius powers in the direct projected C222 source of
`ConZFC_407_888_Quartics`. It is not a new logical calibration of C222. All
coordinates in this proof are natural numbers, including zero, except where
positivity is stated or proved. The source's inherited shared Pell theorem
represents positive exponentiation by a finite ordinary polynomial system;
no variable exponent remains in the released polynomial.

Let `R >= 4`, `1 <= t <= R`, `H >= R^4`, and let the number of range
columns `r` satisfy `1 <= r <= H`. All range lower indices are in `[1,R]`.
These hypotheses hold for the actual source, with `r=8`,
`R=2+t+x+y+M0`, and `H=R^8388608`.

## 1. Self-bounding factorial lemma

For positive `n` and natural proposed output `f`, put `rho=f*n^2`,
`C=binom(rho+n,n)`, `P=(rho+1)^n`. There exist natural `u,v` with

    P+C = C*f+u+1,     C=u+v+1                         (1)

if and only if `f=n!`.

Indeed, `C>=1` and (1) say precisely `f-1<P/C<=f`; equivalently
`f=ceil(P/C)`. They first force `f>=1`. Set `F=n!` and

    R0=P/C=F product_(i=1)^n (1-(i-1)/(rho+i)).

Every factor lies in `(0,1]`, and

    sum_(i=1)^n (i-1)/(rho+i) < 1/(2f).

Thus `0<R0<=F` and `R0>F(1-1/(2f))`. From `f=ceil R0` we obtain
`f<=F`; from `R0<=f` and the strict lower bound,

    F < 2*f^2/(2*f-1) = f+f/(2*f-1) <= f+1.

Integrality gives `F<=f`. This proves soundness. Conversely, if `f=F`,
the same estimate gives `F-1/2<R0<=F`, hence (1) has natural witnesses.
Explicitly, choose `u=P+C-C*f-1`, `v=C-u-1`. This also proves the `n=1`
case. A zero-input extension is immediate (`C=P=1`, forcing `f=1`),
but the actual two inputs are positive.

A useful one-way variant is: if `rho>=n!*n^2`, then

    ceil((rho+1)^n/binom(rho+n,n)) = n!.

Its proof is the same finite-product estimate, now with
`n!-R0< n!*n(n-1)/(2rho) < 1/2`.

## 2. The new common radius and literal rows

Allocate the proposed `H!` output `T` before defining the radius. Use

    rho=T*H^2,      V=(rho+1)^H,       Vt=(rho+1)^t.

The two exact-binomial requests are now

    C_H=binom(rho+H,H),       C_t=binom(rho+t,t),

with ceiling rows (1) for `(n,f,C,P)=(H,T,C_H,V)` and
`(t,Ft,C_t,Vt)`. The output `Ft` is the proposed `t!`.
The third exact binomial, used in the CRT product, is unchanged:
`binom(Q+t,t)`, where

    Q=(1+(t+1)T)^t+2.

Keep all other CRT product rows unchanged. In particular they imply the
raw inequality `B<TQ`, independently of the intended meaning of `B`.
The canonical-index equation is

    B=1+(C+1)T,                                          (2)

so `B>=1` before factorial soundness is known.
Keep the aggregate representative bound

    sum_i a_i + g = r*B,                                 (3)

where all `a_i` are positive, and use the common binomial radix

    q=B*(V+1).                                          (4)

There are still three exact-binomial requests and eight fused
binomial-divisibility requests. The two radius exponentiations
`(H+2)^(H+2)` and `(t+2)^(t+2)` are absent; every other change is ordinary
addition or multiplication. The number of power requests falls from 23 to
21, and the two shift-by-two Pell-index derivations disappear.

## 3. Soundness without a circular factorial assumption

First invoke the shared-power criterion pointwise on the finite power
family. This does not assume that `T` or `Ft` is already a factorial.
In particular the base `rho+1` is positive and the exponents `H,t` are
positive, so `V,Vt>=1`.

The H-factorial ceiling rows alone force `T>=1`, even before the proposed
binomial value `C_H` is interpreted. They give `C_H=u+v+1>=1` and,
after cancellation, `V+v=C_H*T`. If `T=0`, the left side is positive
and the right side zero, a contradiction. Therefore `rho=T H^2>=H`.
By (2) and (4), `q>=V+1>V`.

For `0<=j<=H`, binomial monotonicity up to the midpoint and `rho>=H` give

    binom(rho+H,j) <= binom(rho+H,H) <= (rho+1)^H=V.

The last inequality follows termwise from
`binom(rho+H,H)=product_(i=1)^H (1+rho/i)`.
Thus the exact low-digit binomial graph is sound for `C_H`. Applying
Section 1 yields `T=H!`.

For the second factorial, `t<=H` and `rho>=H>=t`, so for every `j<=t`,

    binom(rho+t,j) <= binom(rho+t,t) <= (rho+1)^t <= V < q.

Its binomial graph is therefore exact. Since `rho=H!*H^2>=t!*t^2`,
the one-way variant of Section 1 now proves `Ft=t!`.

Only after these deductions do we use `T=H!` to prove the radix bounds
for the CRT-product binomial and the eight range-binomial requests.

## 4. The remaining low-digit bound

As `T=H!<=H^H` and `t+2<=H`,

    1+(t+1)T <= (t+2)T <= H^(H+1).

Put `e=t(H+1)>=1`. Then

    Q+t <= H^e+t+2 <= H^e+H <= H^(e+1).

The raw remainder bound `B<TQ` and (3), with `r<=H`, give

    a_i <= rB < rTQ <= H^(H+e+2)
                     <= H^((t+2)(H+1)).

The same final bound holds for `Q+t`. If `n` is any of these remaining
upper arguments and `1<=k<=R` is its lower index, then for `0<=j<=k`,

    binom(n,j) <= n^k <= H^(k(t+2)(H+1)).                (5)

The coefficient is zero if `j>n`, so that case causes no problem.
Because `R>=4` and `H>=R^4`,

    2R(R+2)<=R^4<=H,

hence `k(t+2)<=H/2`.

Pairing factorial factors proves the elementary bound

    H! >= H^floor(H/2).

For each paired pair `j,H+1-j`, their product is at least H; if H is
odd the unpaired middle factor is at least one. Consequently

    V=(T H^2+1)^H > H^[H(floor(H/2)+2)].                (6)

The integer exponent in (6) is strictly larger than
`H(H+1)/2`, whereas the exponent in (5) is at most that quantity.
Thus every coefficient needed in every remaining low digit is less
than V and therefore less than q. This argument uses the raw remainder
bound for B, not the CRT product identity that has yet to be proved.

The third exact-binomial graph and all fused divisibility graphs are now
correct. The inherited finite product identity identifies B with
`product_(i=1)^t (1+iT)`, and the unchanged CRT/certificate proof applies.

## 5. Completeness and dependency order

Given a genuine finite source proof, choose its outer t,x,y,M0 and H.
Set `T=H!`, `Ft=t!`, `rho=T H^2`, and the actual positive CRT product B.
Choose each encoded column's positive representative in `[1,B]`, giving
the slack in (3), and choose the inherited canonical index C. Set q by
(4). Sections 1 and 4 supply every exact factorial, binomial and fused
range certificate with natural quotients. Then choose the common Pell
frame and simultaneous seed-index witnesses, exactly as in the inherited
construction. The arithmetic operations defining rho from a proposed T
are a finite forward gate DAG; existence does not require solving a
numerical fixed point. The self-bounding lemma proves the unique intended
value after the equations have been imposed.

## 6. Independent norm and square-product transformations

For each Pell norm replace

    x^2+y^2=1+a^2 y^2

by a product coordinate `w=a*y` and the quadratic row

    x^2+y^2=1+w^2.

The added coordinate is uniquely determined and natural, and both
presentations are equivalent. Replace `product_i(Y_i^2)` by
`(product_i Y_i)^2`. This is an integer polynomial identity; all new
multiplication outputs have nonnegative inputs. These transformations
alter the graph representation and sum-of-squares polynomial, not the
existence predicate. Most raw savings are already absorbed by the prior
monic contraction, but two coordinates survive as a final saving.

## 7. Exact instantiated counts

With both Section 6 transformations and the shared-radius replacement,
the direct source has 583 natural variables, 501 quadratic rows, and
21 power requests. There are 15 full seed-index tests and one derived
index. The inherited exact rational-SOS contraction at support cap 64
produces 394 natural variables, 312 rows, degree exactly 4, 8,073 expanded
monomials, and coefficient height 83,843,141. The baseline has 407 natural
variables, 323 rows, 8,420 monomials, and coefficient height 83,843,774.
These are measured finite artifact counts, not a global optimality claim.
The mathematical dependencies of the original C222-to-Con(ZFC)
calibration remain explicit and unchanged.
