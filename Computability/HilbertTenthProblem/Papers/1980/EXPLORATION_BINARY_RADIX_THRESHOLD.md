# The other equations do not recover the deleted radix threshold

The published binary product system has 90 arithmetic instructions:
48 multiplications and 42 additions. Its radix relation is

    theta=H+b, H=H0-1, B=theta+2=H0+1+b.

This note tests deleting its one addition and its free equality, leaving
every other straight-line equality in place. The resulting 89-instruction
candidate is unsound. For **every admissible binary index**, it accepts
the queried input x=2 using B=4. In particular it accepts 2 for an index
representing the empty set.

The counterexample includes the original positive product bound,
the input gap, all three bounded masks, the exact fixed-index
congruence, and the full positive Pell extension. Thus these retained
conditions cannot be used to infer the deleted large threshold.
This result concerns this precise deletion and the published support
compiler. It does not exclude another 89-operation construction.

## 1. The exact candidate and arithmetic cost

Delete the instruction theta_sum=H+b and the free equality
th=theta_sum from
../verification/round37_1980_binary_product_certificate.py.
That register has no other consumers. All other instructions and free
equalities remain unchanged. There are 89 instructions, consisting of
48 multiplications and 41 additions, and 21 equality tests on the same
34 positive unknowns. The fixed supplied H is now unused.

For this candidate the mathematical radix is **B=theta+2**. Its geometry
is q^2=1+lambda(theta+1), and its second exponent congruence uses
A-B=a-theta. This is not the different operation of deleting a source
equation while continuing to define B=H+b+2 elsewhere. A fresh source
for the candidate is obtained by substituting H=theta-b in all published
source residuals and removing the now-zero radix residual. The usual
auxiliary-norm correction remains; the two corrections proportional
to the deleted radix residual become identically zero.

The alternative suggestion b=B-1, with theta=b-1, does not by itself
reduce the operation count: it replaces H+b by b-1. The same
counterexample also satisfies that replacement. It shows why its
remaining equations do not supply a missing large-radix guarantee.

## 2. A small-radix family for every admissible index

Fix any admissible binary compiler index (V,H,T_L). Let L be its
underlying power of two. The actual compiler has L>=6. Its two
binary code polynomials have zero constant coefficient and degree
less than L, so

    0<V<2^(2L), V even, T_L=psi_2(L).

Choose the following positive coding witnesses:

    B=4, theta=2, b=3, x=2, beta=1,
    g=ell=4, C=x+g=6,
    e=4^(L-4), q=4^L=256e, n=q^8,
    lambda=(q^2-1)/3,
    sigma=36(e-4), alpha=220e+140.

Since L>=6, e>=16, hence e-ell>0 and sigma>0. Direct substitution gives

    sigma=(e-ell)C^2,
    ell+sigma+alpha=4+36e-144+220e+140=q,
    b=x+beta,
    q^2=1+lambda(theta+1).

In particular the *strong* original product bound holds. It gives
ell,e<q and C^2<q in this example as in the published proof.

The middle source value is

    S2=ell+eq=4+4^(2L-4).

It has two binary base-four digits, at positions 1 and 2L-4.
Since V<2^(2L)=q and S2>q, the quotient

    t=(S2-V)/theta=(S2-V)/2

is a positive integer. Thus the exact congruence with the **original
fixed V** is satisfied. There is no choice of V depending on the
queried input or on the small-radix witnesses.

## 3. All three masks and their ranges

Use the retained packed definitions

    S=g+q^2(S2+q^2 sigma),
    Tplus=q^2(1+theta lambda)+ell(theta q^4-b),
    r=S(n^2-n)+Tplus(n^2-1).

Their genuine block decomposition is

    S=4+q^2 S2+q^4 sigma,
    Tplus-1=T1+q^2 T2+q^4 T3,

where

    T1=q^2-13, T2=2lambda, T3=8.

All three S coordinates fit their widths q^2,q^2,q^4:
g=4<q^2, S2<q^2, and 0<sigma<q. Likewise
0<T1,T2<q^2 and T3=8<q^4. More sharply,

    0<S<q^5+q^4+q^2<n,
    0<Tplus<9q^4<n.

Hence

    n^2-1<=r<2n^3.

The first mask passes because T1=q^2-1-12 has base-four digit zero
at position 1; g=4 has its only nonzero digit there.
The middle mask T2 has digit 2 at every position below 2L.
The two nonzero digits of S2 are 1, so their binary intersections
with those digits are zero.

Finally sigma is divisible by 16: e is divisible by 16, as is
144. Therefore

    sigma AND T3 = sigma AND 8 = 0.

All three masks pass exactly, not just a truncated prefix. Because
the radix and the block widths are powers of two, this gives
S AND (Tplus-1)=0. The same bounded packing lemma as in the
published certificate then proves

    n^2 divides binom(2r,r).

All powers B,q,n are already canonical. Also g and ell are divisible
by B, so the exact packed definitions make S,Tplus,r even.

## 4. Full positive Pell extension without a large radix

The bound 3L<=B from the published soundness bootstrap fails for B=4.
It is not needed for this explicit *necessity* construction. We have
the stronger direct alternatives

    L<J=2r+1,
    B^(3L)=q^3=4^(3L)<4^(8L)=n.

We now verify the hypotheses needed to construct all the Pell
witnesses rather than applying a theorem with an unmet hypothesis.

Put

    J=2r+1, U=2^J, w=U/n^2,
    xi=(U+1)^(2r)/U^r, Y=floor(xi), s=Y/n^2,
    a=Y(U+1), A=a+2, D_P=A^2-1,
    E=UY, Q=UY^2, P=2Q+1.

Since n is a power of two and n^2<=r^2<U, w is a positive integer.
The exact binomial-tail expansion in
BASE_TWO_PELL_90_PROOF.md, Section 5, gives
Y=binom(2r,r) modulo U and Y>=U^r. The displayed central-binomial
divisibility therefore makes s a positive integer. In particular

    U,Y>=n^2, E>=n^4>r+1, a>U^(r+1).

Take c=psi_A(J), d=chi_A(J), k=psi_P(r+1).
The explicit ratio estimates for these chosen indices, proved in
Sections 3 and 5 of that note, give

    Y<xi<c/k<Y+3/4.

Their small-error hypotheses hold because U=2^(2r+1)>32r and r>=64.
Thus eta=c-kY and zeta=k-eta are positive integers. The usual choices

    tau=(chi_P(r+1)-1)/2, h=(k-r-1)/E

are positive integers: P is odd, the Pell congruence modulo P-1=2Q
gives the divisibility, and strict Pell growth gives positivity.

For the main and relaxed auxiliary norms, use the positive generic
construction of HALF_PARAMETER_PELL_92_PROOF.md:

    m=2cJ, f=chi_A(m), i=D_P psi_A(m)/c^2, R=ic^2,
    y_aux=psi_R(J), u_star=chi_R(J)/R,
    o=(u_star-c)/f, j=(u_star-J)/c.

Its congruence signs require J=1 modulo 4, which holds because r is
even. It supplies every required integral positive auxiliary and
both retained norm identities at the chosen A.

For the second main norm choose

    kappa=psi_A(L), mu=chi_A(L), phi=c-kappa,
    Delta=(psi_A(L)-psi_2(L))/a.

Here L<J and A>2 make phi,Delta positive; A=2 modulo a gives the
integrality of Delta. The original fixed T_L is exactly psi_2(L).
The first exponent has base two and value U=2^J; the second has
base four and value q=4^L. Their chi congruences therefore give
integer gamma,rho. All relevant size requirements hold:

    2^(3J)<U^(r+1)<a,
    U^3<a,
    q^3=B^(3L)<n<a,
    psi_2(L)<=4^(L-1)<n<a.

Both exponent moduli are positive. The quotient signs follow from

    d-ac=2c-psi_A(J-1)>c>U,
    mu-(A-B)kappa=B kappa-psi_A(L-1)
                         >(B-1)kappa>q.

Thus gamma,rho are positive too. Every one of the remaining 34
positive unknowns has now been supplied. No coefficient row was
decoded, and no large-radix inequality was silently assumed.

## 5. Consequence and exact finite evidence

Choose the admissible binary index for an inconsistent circuit, for
example the final constraint 2 delta delta_copy=0 together with the
published unit and fresh-copy rows. Its represented set is empty.
The construction above nevertheless supplies a solution of the
threshold-deleted certificate at x=2 for that same fixed index.

The companion script
../verification/explore_binary_radix_threshold.py checks the exact
one-instruction deletion and all remaining symbolic source residuals.
It also evaluates a finite family of the explicit coding witnesses,
all three full integer masks, the packed integer r, and the identity
v_2(binom(2r,r))=popcount(r). It tests several even V values in the
proved admissible range. These finite V choices are range samples,
not claimed full compiler indices. The full Pell witnesses are not
materialized: their existence is the general argument in Section 4.
The receipt clearly distinguishes these scopes.

An independent review of the complete note and checker found no
mathematical issues. A fresh independent run reproduced all 21 symbolic
residual checks and all 21 finite complete-mask cases without rewriting
the receipt.

This is a structural obstruction to recovering the threshold from
the existing bounds, positivity, first mask, fixed binary congruence,
and Pell equations. A smaller construction would have to change
some other part of the encoding or of the threshold mechanism.
