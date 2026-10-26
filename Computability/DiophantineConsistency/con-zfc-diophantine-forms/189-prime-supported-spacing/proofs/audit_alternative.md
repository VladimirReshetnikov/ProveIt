# Independent semantic audit: a prime-index Pell growth witness and forced beta spacing

Prepared for the new direct consistency construction, 25 October 2026.

## Verdict and boundary

The proposed semantic replacement is sound and constructively complete, subject to the unchanged and explicitly inherited C222, shared-Pell, binomial-digit, generalized binomial-CRT, and logical calibration interfaces. I found no circular choice or missing number-theoretic condition in the version proved below.

This note audits the unbounded mathematics. It does **not** authenticate a particular emitted coefficient vector, count its variables, check its projection certificates, or provide a new Lean/Rocq proof object. Those are separate obligations. The ordinary proof is formalizable in ZFC and does not assume either consistency or inconsistency.

The audited predecessor was the complete `ConZFC_Pell_Growth_210_2026-10-25` packet, principally `proofs/growth_proof.md`, `inherited/anchor/proofs/LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md`, and `inherited/anchor/inherited/linear_crt157/MAIN_PROOF.md`.

## Exact changed equations

Put

\[
d=2^{19},\qquad c=524309,
\]

where c is prime and c>d+1. Retain the predecessor's signed variables F, t and y. Replace its horizon and standalone growth constraints by

\[
t=32(2z+1)^2,\qquad Z=ctF,
\]
\[
X^2-Z^2-2ZF=1,\qquad F=ctu-t.
\]

Replace the old spacing equation y=F(2v+1) by

\[
y=FB.
\]

Here B is the **existing** binomial-output coordinate. Its later semantic value is `binom(F+t,t)`. All displayed source equations are quadratic polynomials in unrestricted integer variables. The independent growth variables X,Z,u do not become atoms of the main shared-Pell frame; the already retained F, t, F+t, and the actual retained requests still have their original frame roles.

The unchanged front equations needed in this audit are

\[
C=2c_0,\quad B\eta=C+F+1,\quad D=2(C+F+1),\quad q=D^x,
\]
\[
x=F+1+(y+1)r_0,\qquad x=1+[1+(t+1)y]r_t.
\]

The power displays abbreviate the interpretations of retained polynomial certificates. In particular the base-q request at exponent y+1, the base-(q+1) requests for the actual representatives, and the request at exponent F+t must remain.

## 1. Sign-free growth and the signed bootstrap

Every permitted horizon is positive, even, and at least 32. The equation F=t(cu-1) makes F nonzero and even. Set a=ct+1. Substitution gives

\[
X^2-(a^2-1)F^2=1.
\]

The inherited integer Pell classification gives `|F|=Y_n(a)` for some positive n. The elementary recurrence congruence `Y_n(a)=n mod (a-1)` and F=-t mod ct give

\[
n=\pm t\pmod{ct}.
\]

Consequently n>=t. The standard growth estimate `Y_n(a)>=(2a-1)^(n-1)` implies |F|>t before any sign of F is recovered.

Since C and F are even, C+F+1 is odd and nonzero. Thus the retained product B eta=C+F+1 makes B nonzero. The new equation y=FB therefore gives

\[
|y|\ge |F|>t.
\]

This is exactly the sign-free spacing premise used in Section 4 of the predecessor growth proof. Its acyclic bootstrap remains valid: D is nonzero and even; q=D^x forces x>=0; the final beta endpoint rules out x=0; the q-based y+1 request forces y>0; the first beta endpoint rules out x=1; the final endpoint gives x>=2+(t+1)y; then the q+1 requests force all their actual indices nonnegative. In particular F+t>=0 together with |F|>t forces F>0. The C anchor and its numerator request yield C>0, hence D>0 and q>0. No B positivity premise has been used prematurely.

After F>0, the positive Pell index satisfies n=-t mod ct, hence

\[
n\ge(c-1)t>dt.
\]

Let the predecessor's depth-19 label bound be

\[
L=8^{d-1}t^d.
\]

As c>=4, the same growth comparison yields

\[
F\ge(2ct+1)^{n-1}\ge(8t)^{dt-1}\ge L^t.
\]

The last inequality follows because the quotient of `(8t)^(dt-1)` by `L^t` is `8^(t-1)/t>=1`. Thus the exact inherited label-separation budget remains available.

The predecessor's anchored digit argument now authenticates B=binom(F+t,t)>1. Consequently y=FB>F, so the exceptional spacing branch y=F is automatically excluded. The remaining beta range and local residual estimates only use y>=F and x>=2+(t+1)y, and therefore retain their hypotheses.

## 2. A finite-field zero-rank bound

Fix an odd prime p and an integer a>=2; write Delta=a^2-1. There is an integer rho_p with

\[
1\le\rho_p\le p+1,\qquad p\mid Y_{\rho_p}(a).
\]

One explicit choice is

\[
\rho_p=\begin{cases}p,&p\mid\Delta,\\p-\left(\frac\Delta p\right),&p\nmid\Delta.\end{cases}
\]

For p not dividing Delta, work in the two-dimensional ring F_p[s]/(s^2-Delta) and put epsilon=a+s. This is a norm-one unit. Frobenius gives epsilon^p=a+chi s, where chi is the Legendre symbol of Delta. If chi=1 this equals epsilon; if chi=-1 it equals epsilon^{-1}. Therefore epsilon^(p-chi)=1, giving the claimed zero ordinate.

If p divides Delta, s^p=0, so epsilon^p=a^p=a is scalar. Its ordinate is zero. This covers ramification without assuming the quadratic algebra is a field. At p=2 take rho_2=2. By the Pell addition/composition identity, rho_p dividing n implies p dividing Y_n(a).

This proof needs no assertion that rho_p is the *least* zero rank. The explicitly chosen upper bound is sufficient.

## 3. Compatible cofinal horizons and index congruences

For completeness choose k>=1 and use the cofinal subsequence

\[
t=32c^{2k}=32(2z+1)^2,\qquad z=(c^k-1)/2.
\]

Choose k so that this t exceeds the finite refutation's number of genuine proof-tree nodes and all independent local schema parameters. Set a=ct+1, and choose the rho_p of Section 2 for every prime p<=t.

Because c>32,

\[
\rho_p\le p+1\le t+1<c^{2k+1}.
\]

Thus every rho_p has c-adic valuation at most 2k. For an arbitrary integer ell with 2^ell>t, put

\[
M=\operatorname{lcm}(\{\rho_p:p\le t\}\cup\{2^\ell\}).
\]

The only prime factors of ct are 2 and c. Its 2-adic valuation is 5 and its c-adic valuation is 2k+1. Therefore

\[
\gcd(M,ct)\mid 32c^{2k}=t.
\]

The two congruences

\[
n=0\pmod M,\qquad n=-t\pmod{ct}
\]

are compatible by generalized CRT. Their common solutions form a nonempty arithmetic progression, so n can be chosen positive and arbitrarily large. There is no conflict between high 2-adic divisibility and n=-t mod ct: the latter requires only n=0 mod 32 at the prime 2.

Put F=Y_n(a), X=X_n(a), Z=ctF, and u=(F+t)/(ct). The recurrence congruence modulo ct proves u is an integer and all new growth equations hold. Every prime p<=t divides F. Since a is odd, the standard duplication identity gives v_2(Y_n(a))=v_2(n), so 2^ell divides F.

For 1<=i<=t<2^ell, v_2(F+i)=v_2(i). Hence

\[
v_2\binom{F+t}{t}=0.
\]

Thus B is odd. This simpler parity argument replaces the predecessor's normalized Pell permutation construction.

## 4. The forced spacing dominates every pending state

This is the place where confusing schema parameters with formula labels would be a mistake. Local parameters are below t, but derived formula labels may be as large as L=8^(d-1)t^d. The following bound uses L, not t.

Unroll the finite refutation to a tree with r<t genuine nodes. Expand open obligations in that tree, and pad the resulting rows by the neutral truth row to exactly t rows. Every pending frontier has at most r<=t-1 nonunit factors. Its multiplicative state S therefore satisfies

\[
S\le(1+LF)^{t-1}\le(2LF)^{t-1}.
\]

On the other hand, the new forced spacing is

\[
y=F\binom{F+t}{t}\ge\frac{F^{t+1}}{t!}.
\]

Using F>=L^t, t!<=t^t and L>=2t, the quotient of these respective lower and upper bounds satisfies

\[
\frac{F^{t+1}/t!}{(2LF)^{t-1}}
=\frac{F^2}{t!(2L)^{t-1}}
\ge 2L\left(\frac L{2t}\right)^t>1.
\]

Thus y exceeds every pending state. Also B>1 gives y>F, so the initial value F+1 lies in the required beta range. No independently adjustable multiplier is needed.

## 5. Beta CRT and the remaining choices

The forced y=FB is positive and even, and every prime p<=t divides y. For distinct i,j in {1,...,t+1}, any prime dividing both 1+iy and 1+jy would be coprime to y and divide i-j. It would therefore be at most t and divide y, a contradiction. Hence all beta moduli are pairwise coprime and odd.

CRT now supplies an arbitrarily large positive beta code x encoding the actual pending states. The strict local quotient ranges follow from the same positive-modulus argument as in the predecessor. B was already fixed from F and t, but this creates no cycle because it does not depend on x. After x is chosen, set N=B^x; N is odd. The generalized binomial-CRT theorem applies since F>=L^t>=t^t>=lcm(1,...,t)^2. Choose the eight other representative classes first and then C even and larger than every other required nominal index in its prescribed class modulo N^2. Finally define D, q, the actual powers, and the shared Pell frame in the predecessor's order.

The dependency order is therefore

\[
\text{finite proof}\ \longrightarrow\ t\ \longrightarrow\ n,F,B,y\ \longrightarrow\ x,N\ \longrightarrow\ \text{representatives},C,D,q\ \longrightarrow\ \text{main Pell frame}.
\]

There is no reverse dependence in the new number-theoretic choices.

## 6. Requirements for binding the delivered polynomial

The final finite audit must check the exact horizon coefficient, the prime c, all three growth rows, the use of the *actual* existing B and F coordinates in y=FB, and removal of only the obsolete spacing coordinate. The entire retained beta endpoints, nine range interfaces, C anchor, orientation pool, requests at y+1 and F+t, and actual frame atoms must be preserved. Eliminating an old coordinate by an integral projection is different from merely subtracting one from a raw variable count.

No claim about a 209-variable output is established by this note alone. Once the literal equation and reversible algebraic maps are independently bound, this semantic proof composes with the predecessor's named calibration to give the requested equivalence over ZFC.

## Addendum: sharper capacity bound using strict integral labels

The capacity estimate in Section 4 can be simplified. The source proves the **strict** bound `0<=j<L`, with integral j and L. Hence j<=L-1, and for F>=1,

\[
1+Fj\le 1+F(L-1)\le FL.
\]

If a pending state contains at most t-1 nonunit factors, then

\[
S\le(FL)^{t-1}.
\]

For integers L>=t>=2 and F>=L^t, the forced spacing satisfies

\[
y=F\binom{F+t}{t}\ge\frac{F^{t+1}}{t!},
\]

and therefore

\[
\frac{F^{t+1}/t!}{(FL)^{t-1}}
=\frac{F^2}{t!L^{t-1}}
\ge\frac{L^{2t}}{L^tL^{t-1}}
=L>1,
\]

where t!<=t^t<=L^t. Thus y>S. This stronger and cleaner form requires only L>=t, and it eliminates the factor 2 from the earlier estimate. It is valid because the inherited label bound is strict and the labels are integers. No other part of the audit changes.
