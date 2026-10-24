# Reciprocal factorial moduli: the CRT product is a single binomial

## 1. Moduli lemma

Let `1<=t<=H`, `F=H!`, and `T=F^2`. For each integer `1<=i<=t` put

    D_i = 1 + T/i.

These are integers greater than one. Indeed, `i|F`, and
`T/i = F*(F/i)`. In particular

    D_i = 1 mod F.                                     (1)

Every prime divisor of D_i is therefore larger than H: a prime at most H
would divide F, contradicting (1).

The D_i are pairwise coprime. If a prime p divided D_i and D_j, then
`i D_i - j D_j=i-j` shows that p divides i-j. For distinct i,j,
`0<|i-j|<t<=H<p`, a contradiction. Equivalently, a common divisor divides
i-j and is coprime to F, while |i-j| divides F.

Most significantly, their product has the exact formula

    B = product_(i=1)^t D_i
      = product_(i=1)^t (T+i)/i
      = binom(T+t,t).                                  (2)

No variable-length product is used in the emitted polynomial: the one
ordinary binomial graph replaces the right side of (2).

## 2. A canonical index with no quotient

Because D_1=T+1 is a factor of B, `B>=T+1`. Thus

    C=B-T-1                                             (3)

is natural. For each i, `T=-i mod D_i`, and hence

    C=i-1 mod D_i.                                     (4)

The defining row for C is only `B=T+C+1`. Both (2) and (3) are exact,
not congruence constraints with unspecified quotients.

## 3. The bounded-forall certificate

Let `P(k,z,w)` be the nonnegative source polynomial of the direct C222
construction, where z are external natural parameters, k is a row index,
and w=(w_1,...,w_r) are local coordinates. Suppose H bounds every allowed
local coordinate, every bound successor, t, and the absolute value of P
at every allowed bounded row. In the actual source P>=0 and the explicit
majorant ensures `P<H`; more generally `|P|<H` is sufficient.
Let the natural local bounds be u_j, with u_j+1<=H.

The assertions below are equivalent:

1. For every k<t there is a tuple w with `0<=w_j<=u_j` and `P(k,z,w)=0`.
2. There are positive integers a_1,...,a_r and a natural q satisfying

       B | binom(a_j,u_j+1)   (all j),
       P(C,z,a)=B*q,

   with F,T,B,C defined by (1)-(3).

For soundness fix i in 1..t and choose a prime p|D_i. We have p>H and
p|B. Multiplying each binomial-divisibility condition by `(u_j+1)!`
shows that p divides the falling-factorial product
`product_(v=0)^u_j(a_j-v)`. Primality supplies `w_j` in `[0,u_j]` with
`a_j=w_j mod p`. Equation (4) gives `C=i-1 mod p`. Thus
`P(i-1,z,w)=0 mod p`. Its absolute value is less than H<p, so it is zero.

For completeness choose one bounded tuple for every k<t. Pairwise
coprimality gives CRT representatives a_j for their residues modulo D_i.
Choose each a_j in `[1,B]`; replacing a zero representative by B preserves
all residues. Their falling-factorial products vanish modulo every D_i,
therefore modulo B. Since `(u_j+1)!|F` and gcd(B,F)=1, cancel the factorial
to obtain the stated binomial-divisibility conditions. The source
polynomial evaluates to zero modulo every D_i and hence modulo B; it is
nonnegative, so its quotient q is natural.

This is the same bounded-forall semantic interface as the prior modulus
family `1+iF`. The new family does not alter the source rule predicate,
accumulator interpretation, formula-code calibration, or the logical
meaning of Con(ZFC).

## 4. One factorial and a self-bounding radius

The old product formula required the powers generating an auxiliary Q,
the power F^t, the separate factorial t!, and a third exact binomial.
Equation (2) deletes all those requirements. Only F=H! remains.

Use its proposed output F in its own radius:

    rho=F H^2,      V=(rho+1)^H,      C_H=binom(rho+H,H).

The two natural ceiling rows

    V+C_H=C_H F+u+1,      C_H=u+v+1                     (5)

are equivalent, once C_H and V are interpreted, to
`F=ceil(V/C_H)`. The self-bounding factorial lemma proves that this is
exactly F=H!. Its proof is supplied separately in shared_radius_proof.md.

The finite source has one factorial call, two exact-binomial calls
(C_H and B), and eight binomial-divisibility calls. The latter encode the
eight local columns. Its shared-Pell family contains seventeen power
requests, fourteen full seed-index tests, and one additive index.

## 5. A common radix without circular size estimates

The actual source has `R>=4`, `1<=t<=R`, `H>=R^4`, and r=8<=H. Every
range lower index k is positive and at most R. Keep the single aggregate
bound

    sum_j a_j + g = rB,                                 (6)

and set the common binomial radix to

    q=B(V+1).                                          (7)

The soundness order is as follows.

First recover all required powers from the independently proved shared
Pell criterion. The base rho+1 is positive regardless of the proposed F,
so V>=1. Before interpreting C_H, (5) implies `C_H>=1` and
`V+v=C_H*F`. Thus F>=1. The canonical index row `B=F^2+C+1` implies
B>=1 independently of whether its binomial value is correct. Therefore
q>V. We have rho=F H^2>=H, so for every 0<=j<=H,

    binom(rho+H,j) <= binom(rho+H,H) <= (rho+1)^H=V<q.

Hence C_H's low-digit graph is exact, and the self-bounding factorial
lemma gives F=H!.

Next validate B, whose binomial upper argument is F^2+t and does not
depend on B. Since F=H!>=H>=t and F>=2,

    F^2+t <= F^2+F <= F^3.

For 0<=j<=t its binomial coefficients are at most F^(3t). Moreover
`3t<=3R<=H`, while `V=(F H^2+1)^H>F^H`. Thus these coefficients are
strictly below V<q. The exact binomial graph proves (2), and consequently

    1 <= B <= F^(3t).                                  (8)

Finally, (6), (8), and r<=H<=F give

    a_j <= rB <= F^(3t+1).

If 1<=k<=R is a range lower index, then for every 0<=l<=k,

    binom(a_j,l) <= a_j^k <= F^[k(3t+1)]
                       <= F^[R(3R+1)] <= F^H < V < q.  (9)

The coefficient is zero if l>a_j. The penultimate inequality follows
from `R^4>=R(3R+1)` for R>=4 and H>=R^4.

All required lower digits are therefore carry-free. Because B|q, the
fused quotient graph recognizes `B|binom(a_j,k)` exactly. Every needed
binomial/divisibility statement is now known, so Section 3 applies.
No estimate presupposes the value of a binomial that has not already been
validated. In particular, (8) is used only after B's exact-binomial graph
has been proved correct.

## 6. Completeness

Given a finite source proof, choose the old outer parameters and majorant
H. Set F=H!, T=F^2, B=binom(T+t,t), and C=B-T-1. Section 3 supplies
positive CRT representatives a_j<=B, so (6) has a natural slack. Set
rho=F H^2, V=(rho+1)^H and q by (7). Equations (5) hold by the
self-bounding lemma. The bounds in Section 5 ensure that all exact and
fused binomial graphs admit their ordinary natural quotients/remainders.
Finally choose the common Pell frame and index witnesses for the finite
family of true power relations. Thus the changed equation has a natural
solution exactly when the original direct source certificate exists.

All divisions in this proof are mathematical definitions used to analyze
integer moduli. No divisibility by a variable i or variable-length product
appears in the final polynomial. Its only product-family materialization
is B's already specified binomial graph.

## 7. Measured forms and proof boundary

With the product-coordinate Pell norms and product-of-squares factoring,
the materialized source has 526 natural coordinates and 454 quadratic
rows. The exact certified contraction with support cap 64 yields a
quartic in 363 natural variables, with 291 residuals, 6,674 collected
monomials, and coefficient height 83,842,716.

The source has 17 power requests, 2 exact-binomial requests, 1 factorial
request, 14 seed-index tests, and 1 derived index. These numbers are
computed from the literal emitted rows. They improve the inspected direct
407-variable natural quartic. They do not claim global minimality among
all Con(ZFC) equations, and the inherited calibration remains explicit.

A separate squared-frame variant places `W=2+sum(power_port^2)` directly
in one quadratic row. Its purpose is to recover signs of semantic ports
when constructing an unrestricted-integer companion. The natural
contraction count for that variant is 372; it is not a replacement for
the 363-variable natural choice.
