# A finite negative-input power branch and exclusion through gap seventeen

Every positive zero of the [unchanged86 candidate](complete75_weakened_bound86_candidate.md)
with `R<0`, `mu<0` and **X=2^p** satisfies

    Y<2(q^2-1)X^2,       n<p<=2n-19.

More generally, for each fixed odd gap `g=2n-p`, this branch has an
effectively computable finite necessary domain of `(q,p,w,Y)`. The
input Pell index may be arbitrarily large; the bound does not truncate
it. This complements the [positive-input fixed-gap reduction](complete75_weakened86_gap_eleven.md).
It does not bound the negative-input **X<2^p** branch or all gaps.

The [checker](complete75_weakened86_negative_power_gap.py) and
[receipt](complete75_weakened86_negative_power_gap.json) retain the
86=48M+38A source,19 positive supplied coordinates and degree203. No
passing full outer tuple, false-input zero or universal86 theorem is
claimed. The established75/87 bounds are unchanged.

## 1. The actual packing and a bounded residue wrap

Retain the full compiler, both first/main ratios and strong-rank
conditions used in the [negative-input residue theorem](complete75_weakened86_negative_input_residues.md):

    q=(2^d-1)J+1>=16, X=wq^3, Y=sq^3, d>=4,
    a=Y(X+1), A=a+2, H=4a+3, Delta=A^2-1,
    c=psi_A(p), k=2psi_(2XY^2+1)(n),
    p odd>=13, n<p<2n, kY<c<k(Y+1),
    chi_A(p)-a*c=X+gamma*H, gamma=rho+sigma>=2.

For this packet impose X=2^p. Thus `q=2^t`, `4<=t<=floor(p/3)`, and
`w=2^(p-3t)`. In particular `M=q^2-1` is odd. The actual fixed radix
can be smaller than q; enumerating every such power q is a safe
superset of its possible compiler decompositions.

Use the actual positive `x,F,alpha`, fixed offset b, and masks to set

    C=q-F-alpha-2d*x>=0,
    K=q(q-F)M+(MC+q(MF+2^d-1))J,   0<K<q^4,
    Theta=K-M*C+epsilon-lambda-omega*p,
    epsilon,lambda,omega in{1,-1}.

Here `M*C` is a product, distinct from the mask named MC. The exact
packing identity

    K-M*C=M*((q-1)C+q*(alpha+2d*x))
          +(MC+q(MF+2^d-1))J > 0

therefore gives

    -p-2<Theta<q^4+p+2,    |Theta|<c.                 (1)

For the second assertion, `A>q^6` and the Pell recurrence give
`c>=A^(p-1)>=(p-1)q^6>q^4+p+2`.

Let `r=v mod2p`, where v is the unbounded negative input Pell index.
The preceding residue theorem supplies the canonical `0<f_r<c`:

    f_r=F_r=chi_A(r)+a*psi_A(r)        for 0<=r<p,
    f_p=c-psi_A(p-1),
    f_r=E_s=chi_A(s)-a*psi_A(s)        for s=2p-r, p<r<2p.

The target congruence is equivalent to an integer j satisfying

    M*(H*rho+f_r)=Theta+j*c.                          (2)

This j is a residue wrap, not the supplied auxiliary coordinate.
Since `rho<gamma` and `gamma*H=2c-psi_A(p-1)-X<2c`, the left side
lies strictly between0 and3Mc. Equation(1) consequently forces

    0<=j<=3M.                                        (3)

We allow all three independent signs, omitting the stronger
[auxiliary-sign restriction](complete75_weakened86_auxiliary_sign_lift.md),
first-index equation and transport relation. Excluding this superset
is sufficient for excluding a full positive candidate zero.

## 2. Three small, nonzero multiples of H

The Pell recurrence modulo the odd integer H gives

    F_r=2^(-r) modulo H, E_s=2^s modulo H,
    3Xc=2(X^2-1) modulo H.                            (4)

The first two identities follow from `A=5/4 modulo H` and the initial
values `F_0=E_0=1`, `F_1=1/2`, `E_1=2` modulo H. The last follows
from the main norm and `chi_A(p)-a*c=X modulo H`; no inverse of3 is
taken. Also `f_p=chi_A(p)-(a+1)c=X-c modulo H`.

According to the three ranges of r, equations(2)--(4) make H divide
one of the following integers:

    L_F=3X*(Theta*2^r-M)+2j*(X^2-1)*2^r,        0<=r<p,
    L_E=3X*(M*2^s-Theta)-2j*(X^2-1),            1<=s<p,
    L_p=3X*(MX-Theta)-2(M+j)*(X^2-1),           r=p.   (5)

Each integer in its applicable case is nonzero at a solution of(2).

For L_F, if j>=1, equation(1) and

    2(X^2-1)-3X(p+2)>3XM

make the bracket `3X*Theta+2j(X^2-1)` greater than3XM, so L_F>0.
The displayed inequality follows uniformly from `M<X/16`,
`p+2<=X/512` for odd p>=13 and X=2^p. If j=0 and L_F=0, then
`Theta*2^r=M`. Oddness of M forces r=0 and Theta=M. Since f_0=1,
equation(2) would then give rho=0, impossible.

For L_E=0, reduction modulo X forces X|2j. But
`0<=2j<=6M<X`, so j=0 and Theta=M*2^s. Equation(2) would give
`H*rho=2^s-E_s<=0`. To justify the weak inequality, E_0=1,E_1=2
and `E_s=2A*E_(s-1)-E_(s-2)` imply `E_s>=2E_(s-1)` inductively
for A>=3. Equality E_1=2 is retained; positivity of rho still fails.

Finally L_p=0 would imply X|2(M+j), whereas
`0<2(M+j)<=8M<X`. This is impossible.

Now `q^3<=X`, q>=16 and p>=13 imply

    |Theta|<q^4+p+2<2MX,   2^r,2^s<=X/2.

With(3), the three absolute values in(5) are respectively bounded by

    |L_F|<6MX^3+3MX<8MX^3,
    |L_E|<(27/2)MX^2<8MX^3,
    |L_p|<17MX^2<8MX^3.                             (6)

Each is a nonzero multiple of H, so H<8MX^3. Therefore

    Y=(H-3)/(4(X+1))<2MX^2<2q^2X^2.                 (7)

This argument has no assumption that the negative input index is
smaller than p. Its finite residue r represents every such index.

## 3. Every fixed gap leaves finitely many scales

Set g=2n-p. It is positive and odd, and p>g. The strict ratio estimate
in the [index-gap proof](complete75_weakened86_index_gap.md), Section4,
uses only the first/main Pell coordinates and upper ratio, not the
sign of the input root. It gives

    (X+1)^((p-g)/2)<2^g*Y^(g-1)*(Y+1).

Using(7), `Y+1<2Y`, `q^3<=X` and X=2^p yields

    2^(p(p-g)/2)<2^(2g+1)*2^(8gp/3),
    3p^2-19gp<12g+6.                                (8)

For odd g>=3, p>=7g would make the left side at least14g^2,
which exceeds12g+6. For g=1 the quadratic already fails at p=13
and is strictly increasing thereafter. Thus the power branch has
no g=1 solutions and otherwise p<7g.

For every fixed g, enumerate the finitely many odd
`max(13,g+2)<=p<7g` satisfying(8), then
`4<=t<=floor(p/3)`, `q=2^t`, `w=2^(p-3t)`. Finally enumerate
`Y=sq^3<2(q^2-1)X^2`. This proves effective finiteness, without a
uniform bound on g and without the older positive-input scale bound.

## 4. Exact exclusion of the first nine odd gaps

The finite necessary domains have these sizes:

| g | Necessary(q,p,w) triples | Strict-ratio survivors |
| --- | ---: | --- |
| 1 | 0 | none |
| 3 | 8 | none |
| 5 | 40 | none |
| 7 | 96 | none |
| 9 | 192 | q16,p21,w512,Y8192 |
| 11 | 300 | none |
| 13 | 431 | none |
| 15 | 613 | none |
| 17 | 795 | none |

For each of the2,475 triples, put n=(p+g)/2 and form the exact
integer coefficient arrays

    F(Y)=2Y*psi_(1+2XY^2)(n)-psi_(2+(X+1)Y)(p),
    G(Y)=2(Y+1)*psi_(1+2XY^2)(n)-psi_(2+(X+1)Y)(p).

The source regenerates every coefficient and verifies strictly
negative coefficients below degree p, nonnegative coefficients at
or above p, and positive leading coefficient. Hence F(Y)/Y^p and
G(Y)/Y^p are strictly increasing for Y>0. The finite coefficient
checks are exact certificates for these particular domains; no
unproved coefficient-sign theorem for every gap is assumed.

Geometric bracketing and binary search locate the last permitted
integer multiplier with F<0, using the strict scale limit from(7).
If G<=0 there, every earlier multiplier also fails. The neighboring
point excludes all later multipliers. If both signs permit a survivor,
a second monotone search locates the full interval. All reported
boundary values are independently evaluated from the coefficient
arrays by Horner's rule. The receipt records each triple, its exact
scale bound, boundary and coefficient-array hash; the source regenerates
the full arrays for verification.

Only `(q,p,n,X,Y)=(16,21,15,2^21,8192)` survives the ratios. The
checker reruns the preceding negative-input packet's complete20,160
mask/offset/sign cases at that tuple:19,320 fail the target gcd test,
and840 have least positive rho>=gamma. Their exact interval-receipt
hash is retained here. This excludes the sole survivor without a
period search modulo E or any assumed auxiliary converse.

Thus all odd gaps through17 fail, and every full positive zero in
the stated negative-input power branch has n<p<=2n-19.

## 5. Reproduction and scope

```sh
python3 complete75_weakened86_negative_power_gap.py
```

The checker retains the frozen complete source contract and adds
exact residue identities with signed scalar assignments, uniform
bound fixtures, the finite coefficient/sign certificates and the
inherited all-mask rejection. These supplement the uniform proof;
none is presented as a complete positive candidate zero.

Author receipt generation passes. Its2,475 domains have4,950 exact
coefficient-sign certificates and402 distinct coefficient arrays,
402,106 exact per-domain Pell evaluations and4,280 Horner boundary
checks. There are7,105 power-envelope fixtures and1,932 main/wrap
residue checks, including966 signed assignments.

The author's separate direct-polynomial-recurrence oracle independently
regenerates all402 arrays, enumerates all2,475 triples over a wider
index range, and verifies6,536 endpoint evaluations with its own binary
Pell implementation. An independent full proof/source review and fresh
default replay pass without findings. That review uses closed
Chebyshev-binomial coefficients to regenerate every array, independently
enumerates every domain, and checks all4,280 recorded boundary pairs
and the survivor endpoints with a separate binary-matrix Pell oracle
and Horner evaluation. All seven local links resolve.

The full86 candidate remains unresolved. In particular,
this theorem says nothing that bounds all negative-input X<2^p
data, and it does not replace the separate positive-input gap result.
