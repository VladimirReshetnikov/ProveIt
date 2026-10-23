# A two-root congruence finalizer for the ten-integer equation

This component defines a fixed integer polynomial in ten unrestricted integer
variables.  Its total degree is **9,152,284** and its emitted arithmetic circuit
has **586 live binary operations**.  Its solvability is equivalent, in ZFC, to
the solvability of the pinned 31-positive-variable source.  Composing with the
source theorem therefore gives

\[
 \mathrm{ZFC}\vdash
 \bigl[\forall(t,g_0,h_0,k_0,l,w,x,y,z,m)\in\mathbb Z^{10},\ F_{10}\ne0\bigr]
 \ \longleftrightarrow\ \operatorname{Con}(\mathrm{ZFC}).
\]

This is an ordinary mathematical reduction, with finite circuit certificates.
It is not a proof-assistant verification of the inherited machine/compiler
endpoint or of Sun's number-theoretic bridge.  No global minimality claim is
made.  The JSON variable `f` is the free variable denoted by `t` below.

## 1. What changes

The prior selective construction used a three-root norm and large separating
weights.  We combine its square-base condition, the auxiliary Lucas square
condition, and positivity in one radicand.  Congruences separate that radicand
from the remaining Lucas certificate.  Only a two-root norm is then needed.
The final norm has degree four in its center, compared with degree eight for
the prior norm.  Positivity also recovers the old nonvanishing condition on `l`,
so its square need not be carried in the guard.

There is a separate source simplification.  Rather than first replacing each
positive source coordinate by a new coordinate plus one and expanding all 22
quadratic residuals, we add the common packed word for one to the packing word.
This leaves 94 weighted source records instead of 136.  Translation had
canceled two terms, however, so the earlier targets cannot be reused unchanged.
The new code changes row 13's target from 2212 to 2124 and row 21's from 1050 to
1059.  `code_positive.json` is authoritative; the legacy shifted targets are
retained solely as a negative control.  The new maximum target remains 5190.

## 2. Literal source and fixed constants

`data/parent_quartic31.json` contains the 22 quadratic residuals
\(q_j(p_1,\ldots,p_{31})\), with the fixed ports specialized to the four binary
payloads in `data/`.  The coordinate and port orders are recorded in that JSON.
These ports are the entire pinned `wang943-mixed-121x8801` tuple; no component
from another tuple is substituted.  They have exact byte and integer hashes in
`data/coefficients_binding.json` and `SOURCE_PINS.json`.

Write
\[
 q_j(p)=\sum_{|\alpha|\le2}c_{j,\alpha}p^\alpha,\qquad
 d_{j,\alpha}=(2-|\alpha|)!\prod_i\alpha_i!\,c_{j,\alpha}.
\]
All these are fixed integers, not quantified witnesses.  The complete
coefficient recipes are in `generated/source_records.json`.  There are 94
nonzero records and ten nonliteral fixed recipes, plus the two fixed powers
of two below.

The weights, in coordinate order, are
\[
 (a_1,\ldots,a_{31})=
 (9,25,23,139,35,151,168,21,91,181,94,52,150,180,7,135,
 38,88,183,106,178,136,20,138,8,64,105,154,37,137,120).
\]
Let \(a_0=0\), \(W=183\).  Rows are ordered as
\[
 (16,2,9,14,21,7,15,22,13,3,19,20,1,10,17,8,4,6,11,18,12,5),
\]
with the respective targets
\[
 (70,86,451,685,1059,1296,1530,1874,2124,2358,2696,
 2780,2792,3157,3290,3634,3929,4238,4384,4527,4865,5190).
\]
Write \(t_j\) for the target assigned to row \(j\).  Put
\(\beta_c=2^{2134940}\), \(\beta_m=2^{2134919}\).  Our free variables are
\(t,g_0,h_0,k_0,l,w,x,y,z,m\), all in \(\mathbb Z\), and define
\[
 f=2t+1,\quad b=1+3f=6t+4,\quad
 g=bg_0,\quad h=bh_0,\quad k=b(3k_0+2),\quad B_c=\beta_cb^2.
\]
Thus \(f\ne0\), \(b\ne0\), \(|b|\ge2\), \(2\mid b\), and
\(b\equiv1\pmod3\), without any additional equation.

Define the following finite polynomial expressions:
\[
 \ell=\sum_i B_c^{a_i},\quad
 D_c=\sum_{j,\alpha}d_{j,\alpha}B_c^{t_j-\sum_i a_i\alpha_i},
 \quad T_0=\sum_j B_c^{t_j},
\]
\[
 N_0=B_c^{184},\quad N_1=B_c^{5557},\quad N=N_0N_1=B_c^{5741},
\]
\[
 M_c=N_0-1-(b-1)\ell,\qquad
 T_c=M_c+(B_c-2)T_0N_0,
\]
\[
 J_c=2(1+\ell+g)^2D_c+T_0,\qquad S_c=g+J_cN_0,
\]
\[
 X=N^2+(S_c+T_c)N+N-1-S_c,
\]
\[
 Y=\beta_c^{15}\beta_m B_c^{5931}b,
 \qquad \mathcal C=bB_c^{183}.
\]
Every exponent here is a fixed nonnegative integer.  No exponentiation by a
variable, quotient, square root, or binomial coefficient is in the equation.
The builder compiles each power into binary multiplication gates.

### Source contract and its exact boundary

The selective-support property is the following finite identity: in
\[
 \left(1+\sum_i p_i Z^{a_i}\right)^2
 \sum_{j,\alpha}d_{j,\alpha}Z^{t_j-\sum_i a_i\alpha_i},
\]
the coefficient at target \(t_j\) is \(2q_j(p)\), and no other row contributes
to that target.  `verify.py` enumerates all 94 times 528 interactions and checks
this property including the multiplicities of the 528 unordered pairs.
It also verifies that the old translated-source targets fail this check.

For completeness, the source proof used by this component is the inherited
sparse-borrow and calibrated-population argument, with the following exact
change.  If \(g=\sum_i n_iB_c^{a_i}\) then
\(1+\ell+g=1+\sum_i(n_i+1)B_c^{a_i}\), so the tested tuple is the required
positive tuple \(p_i=n_i+1\).  A conservative fixed mass bound is
\(M=2^{2134927}\), and \(\beta_c=8192M\).  Before digit decoding,
\(0\le g<2\mathcal C\) and \(b\ge4\) imply
\(1+\ell+g<3bB_c^{183}\), since the distinct weights give
\(\ell<2B_c^{183}\).  The old pre-decoding size estimates therefore remain
valid with the conservative bound \(18Mb^2B_c^{366}\) for the nonconstant
word-square factor.  After decoding, \(1\le p_i\le b\), and the coefficient
bound \(M(1+31b)^2\le1024Mb^2\) still applies.  The reversed polynomial has
degree 5102 in \(B_c\), with leading coefficient +1; the positivity proof
using domination of its lower terms is unchanged with this leader.

The one-bit marked-cell argument allows incoming borrows: if the target
coefficient is \(4q_j(p)+1\), its normalized digit has the permitted low
shape exactly when \(q_j(p)=0\).  Unmarked negative coefficients need not
be absent.  It follows, with the same strict range \(S_c+T_c<N\), that
\[
 S_c\mathbin{\&}T_c=0
 \iff g=\sum_i n_i B_c^{a_i},\ 0\le n_i<b,\ q_j(n+\boldsymbol1)=0\ (\forall j).
\]
When \(b=2^s\), put \(B_c=2^v\).  The binary population of \(T_c\) is
\((184+22)v-31s-22\).  For the displayed two-block value of \(X\),
\[
 s_2(X)=1+5741v+s_2(T_c)
       -\{s_2(S_c)+s_2(T_c)-s_2(S_c+T_c)\}.
\]
The subtracted carry count vanishes exactly when the masks are disjoint, and
\(\nu_2\binom{2X}{X}=s_2(X)\).  Thus
\[
 Y\mid\binom{2X}{X}\iff S_c\mathbin{\&}T_c=0,
\]
since \(\log_2Y=5947v-31s-21\).  The inherited range estimates also give
\(X>3b\), \(Y>\max(b,256)\) for every square \(b\) and
\(0\le g<2\mathcal C\).

The source forward implication is cofinal on \(b=4^s\): given a positive
source zero, choose any sufficiently large such \(b\) and encode
\(n_i=p_i-1\).  This tuple is nonzero: row 5 at the all-one positive tuple
has residual 1.  Hence \(b\le g<\mathcal C\), and indeed \(b^2\mid g\)
because every weight is positive.  It is therefore of the imposed form
\(g=bg_0\).  Conversely, the mask proof decodes any signed witness once
the Sun bridge has recovered \(b\in2\uparrow\) and \(0<g<2\mathcal C\).

The source-proof companion in the containing release gives the complete
sparse-borrow inequalities, the original inherited source theorem, and the
retargeting certificate.  The new finalizer below uses only this stated source
contract plus its displayed congruences; it does not presume a source zero.

## 3. The Sun bridge registers

Set
\[
 L=lY,\quad U=2LX,\quad V=4gwY,\quad W_*=bw,
\]
\[
 A=U(V+1),\quad B_*=2X+1,\quad C=B_*+(A-2)h,
\]
\[
 P=U^2V,\quad K=X+1+k(P-2),\quad
 S=2A-5,\quad T=3W_*C-2(W_*^2-1),
\]
\[
 Q=\bigl((P/2)^2-1\bigr)K^2+1,
\]
\[
 \Delta=8\mathcal C^3gK^2-
 g^2\bigl(32(C-KL)^2\mathcal C^3+g^2K^2\bigr).
\]
The notation \(P/2\) is only an abbreviation for the division-free expression
\((LX)UV\), as \(U=2LX\); `Phalf` is exactly that expression in the circuit.
Thus \(4Q=(P^2-4)K^2+4\), the old auxiliary square radicand.

Put \(\xi=zx\), and form Sun's modified Lucas certificate
\[
 D=(A^2-4)C^2+4,\qquad E=C^2D\xi,\qquad
 F=4(A^2-4)E^2+1,
\]
\[
 G_*=2(A+2)(A-2)^2E^2-1,\qquad \Omega=16E,
\]
\[
 H_*=C+(B_*-C)F+\Omega Fy,\qquad I_*=(G_*^2-1)H_*^2+1.
\]
Finally set
\[
 \rho=T+Sy,\quad \Sigma=\xi S^5,\quad
 \Theta=(\rho^3-\rho S^2-S^3)(\rho^2+23S^2).
\]

The external bridge input is precisely Sun (2021), Theorems 4.12--4.13,
specialized to \(p=P_{\rm theorem}=2,Q_{\rm theorem}=1\), with the modified
Lucas certificate and residue interpolation of Sun (2026), Theorems 3.1 and
4.1 and Propositions 6.1--6.2.  These give the following interface.

* From a source witness with \(b\in2\uparrow\), \(0<g<\mathcal C\), and
  the central-binomial divisibility, choose positive \(l,w\) and integers
  \(h,k\) so that \(Q\) is a square, \(S\mid T\), \(\Delta>0\),
  \(C=u_{2X+1}(A)\), and \(K=u_{X+1}(P)\).
* Conversely, if \(b\) is square, \(f^2l^2\Delta>0\), \(\xi\ne0\),
  \(4Q\) and \(DFI_*\) are squares, and \(S\mid T\), the bridge recovers
  \(b\in2\uparrow\), \(0<g<2\mathcal C\), and the binomial divisibility.
* On the forward branch, \(\xi\) can be made a multiple of any prescribed
  positive integer, and \(y\) can be assigned any residue modulo \(\xi\)
  while retaining the square certificate \(DFI_*\).

The exact forward values of \(C,K\) are not an extra assumption: the proof of
Sun's 2021 Theorem 4.12 defines \(C=u_B(A,1)\) immediately before equation
(4.16), which defines \(K=u_{QX+1}(U^PV,1)\).  The recurrence used here is
\(u_0(a)=0,u_1(a)=1,u_{n+1}(a)=au_n(a)-u_{n-1}(a)\).

## 4. Congruences valid for every integer assignment

These identities do not assume positivity, a source solution, a Pell equation,
or a zero of the final polynomial.

First, \(B_c,N_0,N\) are multiples of \(b^2\).  Therefore
\[
 X+1\equiv-g\equiv0\pmod b.
\]
Also \(X\) is odd, because \(b,g,B_c,N_0,N\) are even.  Since
\(b\equiv\beta_c\equiv1\pmod3\), all powers of \(B_c\) equal 1 modulo 3.
There are 22 targets.  Modulo 3 one has
\(M_c=0\), \(T_c=-22=2\), and hence
\[
 X\equiv1+(S_c+T_c)+1-1-S_c=T_c+1=0\pmod3.
\]

The displayed formula for \(Y\) has a factor \(b\); hence \(2b\mid U\)
and \(2b\mid A\).  Consequently \(b\mid P\) and \(3\mid P\).  The
normalization \(k=b(3k_0+2)\) gives
\[
 K\equiv0\pmod b,\qquad K\equiv1+2(-2)=0\pmod3.
\]
It follows that
\[
 Q\equiv1\pmod{b^2},\qquad Q\equiv1\pmod3,
 \qquad \gcd(b,Q)=1.
\]
In particular \(Q\ne0\), \(Q\) is odd, and for \(r=bQ\) we have
\(r\equiv1\pmod3\), \(|r|\ge2\).

Since \(h=bh_0\),
\[
 C+1=2(X+1)+(A-2)bh_0\equiv0\pmod{2b}.
\]
Consequently \(4b\mid D\): both terms of
\(D=A^2C^2-4(C^2-1)\) are divisible by \(4b\).

## 5. The equation and unconditional two-root separation

Define
\[
 r=bQ,\quad a=r+(3\Delta-1)(rz)^2,
 \quad d=DFI_*,\quad Z=\Sigma m-\Theta.
\]
The single equation is
\[
 \boxed{F_{10}=\bigl(Z^2-\Sigma^2(a+d)\bigr)^2
                  -4\Sigma^4ad=0.}
\]

The crucial separation is small and unconditional.  Namely,
\[
 \frac ab=Q+(3\Delta-1)bQ^2z^2\quad\hbox{is odd},\qquad
 \frac db\quad\hbox{is even}.
\]
Both displayed quotients are integers; they are not operations in the emitted
polynomial.  Since \(b\ne0\), this proves \(a\ne d\) on every assignment.
No magnitude comparison or large separating coefficient is required.

The following elementary lemma explains why this is enough.  If integers
\(a\ne d\) and a rational number \(q\) satisfy
\[
 (q^2-a-d)^2=4ad,
\]
then \(q\ne0\), because at zero the difference is \((a-d)^2\).
Define \(u=(q^2+a-d)/(2q)\) and \(v=q-u\).  Expanding gives
\(u^2=a,v^2=d\).  A rational square root of an integer is integral, so
both \(a,d\) are integer squares and \(q=u+v\in\mathbb Z\).
This proof includes negative and zero candidate radicands without making
any prior choice of real or complex square roots.

Now \(S=2A-5\) is odd and never zero.  The polynomial
\(\pi(v)=(v^3-v-1)(v^2+23)\) has no rational root, so
\(\Theta=S^5\pi(\rho/S)\ne0\).  If \(\Sigma=0\), the final polynomial is
\(\Theta^4\ne0\).  At any zero we therefore have \(\Sigma\ne0\), and
in particular \(\xi\ne0\), \(z\ne0\).  Apply the lemma with
\(q=Z/\Sigma\).  It yields
\[
 a,d\in\operatorname{Sq}(\mathbb Z),\qquad \Sigma\mid\Theta.
\]
The latter follows from \(q=m-\Theta/\Sigma\in\mathbb Z\).

The standard quintic merger then gives \(S\mid T\).  For clarity: if for
some prime \(p\) one had \(v_p(T)<v_p(S)\), then
\(v_p(\rho)=v_p(T)\).  The two factors of \(\Theta\) have valuations
\(3v_p(T)\) and \(2v_p(T)\), respectively.  Thus
\(v_p(\Theta)=5v_p(T)<5v_p(S)\), contradicting \(S^5\mid\Theta\).

## 6. The combined square and positivity guard

Factor
\[
 a=r\{1+(3\Delta-1)rz^2\}.
\]
The two factors are coprime.  Neither is zero: \(|r|\ge2\), \(z\ne0\),
and the second factor is 1 modulo \(r\).  Since their product is a square,
each is a signed square and both have the same sign.  But
\(r\equiv1\pmod3\) excludes a negative square.  Hence \(r\) and the
bracket are positive squares.

Similarly \(r=bQ\), \(\gcd(b,Q)=1\), and
\(b\equiv Q\equiv1\pmod3\).  Each factor is a signed square, and the
same modulus excludes negative squares.  Thus \(b,Q\) are positive squares.
Since \(b\) is even and nonzero, \(b\ge4\), and therefore \(r\ge4\).

If \(\Delta\le0\), then
\[
 1+(3\Delta-1)rz^2\le1-r\le-3,
\]
contradicting positivity of the bracket.  Therefore \(\Delta>0\).
Since \(\mathcal C=bB_c^{183}>0\), the formula for \(\Delta\) gives
\(K\ne0\) and \(g>0\).  If \(l=0\), then \(U=P=0\) and
\(Q=1-K^2\le0\), contradicting its positive-square value.  Thus
\(l\ne0\), and \(f=2t+1\ne0\) was automatic.  We have recovered
\(f^2l^2\Delta>0\), exactly the old bridge hypothesis, without placing
the factor \(f^2l^2\) in the new guard.

All hypotheses of the reverse bridge now hold.  It yields the binomial source
contract, which decodes a positive zero of the pinned parent.  This proves
soundness for all signed integer assignments, including degenerate values of
the individual bridge variables.

## 7. Completeness of the new congruence restrictions

Suppose the parent has a positive zero.  Choose a sufficiently large
\(b=4^s\), \(s\ge1\), in the cofinal source construction.  Then
\(t=(b-4)/6\in\mathbb Z\), and the encoded \(g\) is a multiple of
\(b^2\).  In fact
\[
 X+1\equiv-g\equiv0\pmod{b^2}.
\]
Apply the constructive bridge.  It gives the exact values
\(C=u_{2X+1}(A)\), \(K=u_{X+1}(P)\) and positive \(l,w\), as stated
above.  We show its \(h,k\) already have the imposed forms.

The index \(X+1\) is even.  The recurrence shows that \(u_{2j}(P)\) is
divisible by \(P\).  Since \(2b\mid U\), we have \(4b^2\mid P\),
and thus \(b^2\mid K\).  Since \(P\equiv0\pmod4\),
\(v_2(P-2)=1\).  In
\[
 (P-2)k=K-X-1,
\]
the right side is divisible by \(b^2\).  As \(b\) is a power of two,
\(b^2/2\mid k\), hence \(b\mid k\).  Also \(P\equiv X\equiv0\pmod3\)
and \(K\equiv0\pmod3\), so \(k\equiv2\pmod3\).  Because
\(b\equiv1\pmod3\), the integer \(k/b\) is 2 modulo 3.  It is exactly
of the form \(3k_0+2\).

For the other restriction, the recurrence gives
\(u_{2j+1}(A)\equiv(-1)^j\pmod{A^2}\).  Since \(X\) is odd,
\(C+1\) is divisible by \(A^2\), hence by \(4b^2\).  Also
\(B_*+1=2(X+1)\) is divisible by \(2b^2\).  Thus
\(2b^2\mid C-B_*\).  The constructive \(A\) is a multiple of four,
so \(v_2(A-2)=1\).  Therefore
\[
 h=(C-B_*)/(A-2)
\]
is divisible by \(b^2\), in particular by \(b\); write \(h=bh_0\).
All normalization restrictions thus preserve completeness, with no change
to the constructive \(l,w,C,K\).

These witnesses have \(\Delta>0\), and \(b,Q\) positive squares.  Set
\(r=bQ\), also a positive square.  The positive integer
\(\delta=3\Delta-1\equiv2\pmod3\) is nonsquare.  Hence \(\delta r\)
is a positive nonsquare.  Pell's theorem gives integers \(u,z>0\) with
\[
 u^2-\delta r z^2=1.
\]
It follows that \(a=ru^2\) is a square.

It remains to use the two free certificate variables without losing this
chosen \(z\).  Since \(S\mid T\), write \(q=T/S\).  First apply the residue interpolation
theorem with prescribed divisor \(z\) to obtain its positive \(\xi\).
Then choose a residue class of \(y\) for which \(\pi(q+y)\equiv0\pmod\xi\).
The polynomial \(\pi\) has a root modulo every positive integer, so this
residue exists.  Interpolation supplies the square \(d=DFI_*\), and
\(x=\xi/z\) is integral.  Then
\(\Theta=S^5\pi(q+y)\) is divisible by \(\Sigma=\xi S^5\).
Choose
\[
 m=\Theta/\Sigma+\sqrt a+\sqrt d\in\mathbb Z.
\]
The polynomial identity for \(F_{10}\) now gives \(F_{10}=0\).

For the local-root fact used here, the cubic \(v^3-v-1\) has discriminant
\(-23\).  At an odd prime other than 23, either it has a simple linear
factor, or its irreducibility makes the discriminant a square modulo the
prime, so \(v^2+23\) has a simple root.  At 23 the cubic has simple root
3.  At 2, \(-23\equiv1\pmod8\) is a square in \(\mathbb Z_2\).
Hensel lifting and the Chinese remainder theorem prove the assertion.
The cubic has no rational root by the rational-root theorem, and neither
does \(v^2+23\).  These are exactly the inherited quintic merger facts.

## 8. Exact complexity and finite checks

The emitted gate list has ten variable leaves, twelve fixed leaves, and
586 live binary arithmetic operations.  Addition, subtraction, multiplication,
and multiplication by a numeral all count; reused nodes count once.  Fixed
integer construction is outside this arithmetic-circuit cost.  The coefficient
payload is unchanged; this is not a bit-complexity reduction.

The crucial total degrees are

| Register | Degree |
|---|---:|
| \(X\) | 22,964 |
| \(Y\) | 11,863 |
| \(A\) | 46,694 |
| \(C\) | 46,696 |
| \(K\) | 81,524 |
| \(Q\) | 326,092 |
| \(\Delta\) | 187,881 |
| \(a\) | 840,069 |
| \(d=DFI_*\) | 4,109,198 |
| \(\Sigma\) | 233,472 |
| \(Z\) | 233,490 |
| \(F_{10}\) | 9,152,284 |

The top term of \(F_{10}\) is \(\Sigma^4d^2\).  Indeed,
\(\deg(\Sigma^2d)=4,576,142\) exceeds the degrees of both \(Z^2\) and
\(\Sigma^2a\), and \(\deg(\Sigma^4ad)=5,883,155\) is strictly below
9,152,284.  The independent verifier propagates syntactic upper degrees and
then computes the coefficient at that upper degree after setting every free
variable equal to one indeterminate.  A nonzero modular residue with the
actual fixed coefficients proves that the top term survives and that the
degree is exact.  It also checks the literal source recipes, all selective
interactions, every live gate, the payload hashes, independent direct-formula
evaluations, the two-root norm identity, and finite congruence probes.

The pinned incoming selective ten-integer construction had degree 21,111,400
and 659 operations.  This component reduces the degree by about 56.65 percent
and the gate count by about 11.08 percent, with the same ten unrestricted
variables.  These are comparisons of the supplied explicit circuits, not
universal lower bounds or claims that the consistency equivalence itself is new.

## References and inherited endpoint

1. Z.-W. Sun, *Further results on Hilbert's Tenth Problem*, Science China
   Mathematics 64 (2021), 281--306; Theorems 4.12--4.13 and equation (4.16).
   <https://arxiv.org/html/1704.03504v7>.
2. Z.-W. Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
   2026 preprint; Theorems 3.1, 4.1 and Propositions 6.1--6.2.
   <https://arxiv.org/html/2609.01594v1>.
3. ProveIt incoming selective quadratic construction, audited at repository
   commit `4b4349064a750ba6347293b55874a7f92abdd0db`; the source support code,
   sparse-borrow adapter, mask-population calibration, parent equation, and
   coefficient tuple are inherited and explicitly identified in this release.
4. `upstream/QUARTIC31_PROOF.md`, `upstream/COEFFICIENT_PROOF.md`,
   `upstream/SIGNED10_PROOF.md` preserve the historical parent/tuple/bridge
   proofs and their original dependency boundaries.  The historical signed10
   finalizer in that last file is replaced by Sections 4--7 above.
