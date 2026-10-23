# Seventeen unrestricted integers: complete new reduction

This note defines and proves a fixed polynomial specialization. All imported
data are pinned to ProveIt commit
ae3007ca4467011e0e051c84acb4a1dd13971b0e, package 18-jones9. Its existing
Jones ratio theorem, quartic/compiler proof, and K215 calibration are imported
ordinary mathematical theorems. No new proof-assistant certificate is claimed.

The new contribution is a concrete signed-domain specialization with 17
unrestricted integer unknowns. This improves the **delivered concrete
26-integer count** in the inspected direct compiler family, at the cost of
astronomic degree. It is not a new universal-variable bound. In particular,
Sun's September 2026 ten-integer theorem already gives a smaller abstract
general bound. We do not instantiate its different source compiler here.

## 1. Exact source interface

The base coordinates are
\[
 (\varepsilon,g_0,h_0,s_0,w_0,\phi,i_0,j_0)\in\mathbb Z^8.
\]
Use exactly the polynomial expressions in
upstream/nine/nine_section.tex, through a_0,a_1 and m, with
\(g=g_0+1,h=h_0+1,s=s_0+1,w=w_0+1,i=i_0+1,j=j_0+1\).
The old ninth variable n and its finalizer are discarded.
For self-contained notation, the full base is as follows.

The fixed constants are those in
upstream/nine/generated/constants.json and index_bound_s.json. Put
\(\nu=32,\ L=5^{33}\).
The 32 positive coordinates of the pinned quartic are shifted by 1.
If the resulting coefficient of the exponent vector \(\alpha\in
\mathbb N^{33}\), \(|\alpha|\le4\), is \(p_\alpha\), the weighted coefficient
is \(c_\alpha=(4-|\alpha|)!\prod_r\alpha_r!p_\alpha\).
Here the first coordinate is the unused dummy input, fixed to 1.
The exact four compiler ports are the whole T4 tuple from the binding file.
If \(\rho_j\) is the positive-coefficient bound on the shifted j-th residual
supplied by index_bound_s.json, put
\[
 s_\star=2+24\sum_j\rho_j^2,\quad z_\star=2^{s_\star},\quad
 e_\star(T)=\sum_{|\alpha|\le4}(z_\star+c_\alpha)
 T^{L-\sum_r\alpha_r5^r},\quad y_\star=e_\star(2z_\star).
\]
These are fixed integers, not variables. Every exponent in the polynomial is
a fixed natural number. The recipe proves \(z_\star>|c_\alpha|+1\) for every
coefficient, including the unlisted zero coefficients. In particular
\(y_\star\ge 2z_\star\).

Define
\[
 b=y_\star+1+\varepsilon,\quad \mathcal B=b^5,\quad
 q=\mathcal B^L,\quad
 \ell=\sum_{r=1}^{\nu}\mathcal B^{5^r},\quad
 \lambda=\sum_{r=0}^{4L-1}\mathcal B^r,\quad
 e=e_\star(\mathcal B),\quad \theta=\mathcal B-2z_\star,
\]
\[
 N=q^{16},\qquad G=32b\mathcal B^{5^\nu}.
\]
Then
\[
\begin{split}
 R={}&[g+eq^3+\ell q^5+
 (2(e-z_\star\lambda)(1+\mathcal B+g)^4+
 \lambda\mathcal B+\lambda\mathcal Bq^4)q^7](N^2-N)\\
 &+[q^3-b\ell+\ell+\theta\lambda q^3+
 (\mathcal B-2)q^8](N^2-1).
\end{split}
\]
The remaining abbreviations are
\[
\begin{gathered}
 U=N^2w,\quad Y=N^2s,\quad M=RY,\quad
 P=2M^2U,\quad K=R+1+h(P-1),\quad A=M(U+1),\\
 B_1=2R+1,\quad W_1=bw,\quad C=B_1+W_1+\phi,\quad
 J=4A-5,\quad Q=3W_1C-2(W_1^2-1),\\
 D=(A^2-1)C^2+1,\quad E=iJDC^2,\quad
 F=(A^2-1)E^2+1,\quad G_1=A+F(CD+1-A),\\
 H=B_1+jC,\quad I=(G_1^2-1)H^2+1,\\
 a_0=(P^2-1)K^2+1,\qquad a_1=DFI,\\
 m=K^2G-4(C-KY)^2G-8gK^2,\\
 D_0=JF,\qquad T_0=QF+J(H-C).
\end{gathered}
\]
The imported Jones ratio equivalence says that there exists a tuple of
eight nonnegative base coordinates satisfying
\[
 a_0,a_1\in\operatorname{Sq}(\mathbb Z),\quad D_0\mid T_0,\quad m>0
 \tag{JR}
\]
if and only if the pinned 32-variable quartic has a positive solution.
By the imported compiler and K215 calibration, that occurs if and only if
there is a finite ZFC refutation.

This is precisely the source interface actually used. We do not assert that
any unspecified nine-variable polynomial has this extra signed structure.

## 2. Two guards can be removed

Only the following six base coordinates require explicit nonnegativity:
\[
 {\bf x}=(\varepsilon,g_0,s_0,w_0,\phi,j_0).
\]

**Lemma 1 (denominator).** For all integer base coordinates, \(D_0\ne0\).

Proof. \(J=4A-5\ne0\). If \(F=0\), the integer equation
\((A^2-1)E^2=-1\) forces \(A=0,E=\pm1\).
But then \(J=-5\) and \(E=iJDC^2\) is divisible by 5, impossible.

**Lemma 2 (signed i).** If \(i\ne0\), replacing i by \(|i|\) does not change
\(a_0,a_1,D_0,T_0,m\).

Proof. The only nonsquared occurrence of i is in E, and the only consumer of E
among these five expressions is E squared in F. Thus all five expressions
are unchanged. The corresponding new coordinate \(i_0=|i|-1\) is nonnegative.

**Lemma 3 (the h guard is implied).** Suppose the six coordinates x are
nonnegative, \(a_0\) is an integer square, and \(m>0\). Then \(h\ge1\), hence
\(h_0\ge0\).

Proof. The index recipe gives \(b\ge2\), \(\mathcal B=b^5\ge32\),
\(e\ge0\), and \(\mathcal B>2z_\star\).
Write \(t=5^\nu\). Since g is positive, \(m>0\) first implies
\(K\ne0\), \(g<G/8=4b\mathcal B^t\), and
\[
 4(C-KY)^2<K^2.
 \tag{1}
\]
To see the bound on g, use
\(m\le (G-8g)K^2\); to see (1), discard the strictly positive
term \(8gK^2\) from the margin inequality and divide by G.

Since \(b\le\mathcal B\) and \(\mathcal B>5\),
\[
 1+\mathcal B+g
 <1+\mathcal B+4\mathcal B^{t+1}
 \le5\mathcal B^{t+1}
 <\mathcal B^{t+2}\le\mathcal B^{5t}=q.
 \tag{2}
\]
Also \(\ell<\mathcal B^{t+1}\), because its distinct exponents lie between
0 and t and \(\sum_{r=0}^t\mathcal B^r<\mathcal B^{t+1}\).
Thus \(b\ell<\mathcal B^{t+2}\le q<q^3\).
Let \(V=1+\mathcal B+g\). The potentially negative part of the first
bracket defining R is
\[
 \lambda\mathcal Bq^4-2z_\star\lambda V^4>0
\]
by (2) and \(\mathcal B>2z_\star\). All other terms in that bracket,
after writing \(2(e-z_\star\lambda)V^4=2eV^4-2z_\star\lambda V^4\),
are nonnegative, and g is positive. The second bracket is positive by
\(q^3>b\ell\), \(\theta>0\), and \(\mathcal B>2\).
Consequently \(R\ge N^2-N\ge2\).

Now \(Y,U\ge1\), \(C=2R+1+bw+\phi>0\), and
\(P=2R^2Y^2U\ge2R^2>R+2\).
If \(K\le0\), then \(K=0\) contradicts (1), while \(K<0\) gives
\(|C-KY|=C+|K|Y>|K|\), also contradicting (1).
Hence \(K>0\).

Suppose h were at most zero. Then \(1\le K\le R+1<P\).
If K=1, the relation \(K=R+1+h(P-1)\) implies \(P-1\mid R\), impossible
because \(0<R<P-1\).
If \(2\le K<P\), the radicand lies strictly between consecutive squares:
\[
 (PK-1)^2<(P^2-1)K^2+1<(PK)^2.
\]
The left difference is \(K(2P-K)>0\); the right difference is \(K^2-1>0\).
This contradicts \(a_0\in\operatorname{Sq}(\mathbb Z)\).
Therefore h is positive.

Combining these lemmas, the existential predicate (JR) is unchanged if
h0 and i0 range over arbitrary integers, provided i=i0+1 is nonzero and
the other six coordinates remain nonnegative.

## 3. One square condition packages all seven inequalities

Introduce seven integer variables \(z_1,\ldots,z_7\).
Let \(C_0=1\). In the listed order of the six coordinates \(x_1,\ldots,x_6\),
put
\[
 d_j=3x_j+2,\qquad
 B_j=1+4d_jC_{j-1}^2z_j^2,\qquad C_j=C_{j-1}B_j
 \quad(1\le j\le6).
\]
Finally put
\[
 d_7=3m-1,\qquad B_7=1+4d_7C_6^2z_7^2,\qquad C_7=C_6B_7.
 \tag{3}
\]

**Lemma 4 (coprime positive-square stack).** Subject to
\(z_1\cdots z_7\ne0\), the single condition
\(C_7\in\operatorname{Sq}(\mathbb Z)\) implies
\(x_1,\ldots,x_6\ge0\) and \(m>0\).
Conversely, if those inequalities hold, z1,...,z7 can be chosen nonzero
so that C7 is a square.

Proof. Every Bj is 1 modulo 4, so it is nonzero, and
\(\gcd(B_j,C_{j-1})=1\). Thus the Bj are pairwise coprime.
If their product is a square, unique factorization implies that each
\(|B_j|\) is a square. A negative square is 0 or 3 modulo 4, so
\(B_j\equiv1\pmod4\) forces Bj to be a *positive* square.
As Cj-1 and zj are nonzero, if dj were negative then
\(B_j\le1-4=-3\). Thus every dj is nonnegative; its residue 2 modulo 3
excludes zero. Therefore \(d_j>0\), which means \(x_j\ge0\) for j<=6
and \(m\ge1\) for j=7.

For the converse, every dj is positive and is 2 modulo 3, hence is
not a square. The Pell equation \(u^2-d_jv^2=1\) has a nontrivial
positive solution. It has one with v divisible by any prescribed
positive integer: powers of its unit matrix in
\(\mathrm{SL}_2(\mathbb Z/M\mathbb Z)\) eventually equal the identity,
so the lower-left Pell coordinate is 0 modulo M. Use
\(M=2|C_{j-1}|\), and put \(z_j=v/(2C_{j-1})\).
Then Bj is u squared. Induction makes all seven factors positive squares.

The zero case is not silently lost: Bj is never zero, and all nonzero
requirements on z are imposed later through one divisibility condition.

## 4. A degree-five intersective polynomial

Set
\[
 \Pi(t)=(t^3-t-1)(t^2+23).
\]

**Lemma 5.** Pi has no rational root, but for every nonzero integer N
there is an integer t with \(N\mid\Pi(t)\).

Proof. The cubic is monic with constant term -1, so its only possible
rational roots are 1 and -1, and neither is a root. The quadratic has
no real root.

We construct a root modulo every prime power and apply the Chinese
remainder theorem. The cubic has discriminant -23.
For an odd prime p other than 23, if it has a root modulo p, that root
is simple and lifts to all p-powers. If it has no root modulo p,
it is irreducible of degree three. Its roots lie in \(\mathbb F_{p^3}\),
and Frobenius permutes them by a three-cycle. The product of their
pairwise differences is invariant under that even permutation, hence
lies in \(\mathbb F_p\), and its square is -23. It is nonzero.
Therefore \(t^2+23\) has a simple root modulo p, which also lifts.
At p=23, the cubic has the simple root 3, since f(3)=23 and
f'(3)=26 is not divisible by 23.

For p=2, use the quadratic: -23 is 1 modulo 8.
If an odd t solves \(t^2=-23\pmod{2^e}\) for e>=3, then one of
t and \(t+2^{e-1}\) solves it modulo \(2^{e+1}\), since their squares
differ by \(2^et\pmod{2^{e+1}}\). The initial cases are immediate.
This gives all 2-powers. The asserted CRT conclusion follows.

This is a classical intersectivity mechanism; the present work claims
only its application to this fixed equation, not novelty of the general
idea or of Pi.

Define the homogeneous polynomial
\[
 \mathcal R(D,T,v)=
 \big((T+Dv)^3-D^2(T+Dv)-D^3\big)
 \big((T+Dv)^2+23D^2\big).
 \tag{4}
\]

**Lemma 6 (divisibility and nonvanishing).** For integers D,T,Z with D nonzero,
\[
 (D\mid T\ \land\ Z\ne0)
 \quad\Longleftrightarrow\quad
 \exists v\in\mathbb Z:\ ZD^5\mid\mathcal R(D,T,v).
 \tag{5}
\]
Moreover \(\mathcal R(D,T,v)\ne0\) for every integer v.

Proof. Since D is nonzero, division by D in the identity
\(\mathcal R(D,T,v)=D^5\Pi(T/D+v)\) proves nonvanishing, using
the no-rational-root part of Lemma 5.

If D divides T and Z is nonzero, write T=Dq and use Lemma 5 to choose
v so that \(Z\mid\Pi(q+v)\). This proves the forward direction.

Conversely, if Z were zero, divisibility would assert
\(\mathcal R=0\), impossible. If D did not divide T, choose a prime p
with \(\alpha=v_p(D)>\beta=v_p(T)\); T is then necessarily nonzero.
For \(r=T+Dv\), one has \(v_p(r)=\beta\).
In \(r^3-D^2r-D^3\), the first term has the unique least valuation
\(3\beta\), while in \(r^2+23D^2\) the first term has the unique least
valuation \(2\beta\). Consequently
\(v_p(\mathcal R)=5\beta<5\alpha=v_p(D^5)\), contradicting divisibility.

## 5. The actual polynomial in seventeen variables

The variables are the eight base coordinates, the seven z variables,
and two further integers v and u: exactly 17 variables.

Using (3), put
\[
 C_\ast=C_7,\quad
 w_1=1+C_\ast^2,\quad
 w_2=w_1(P^2+K^2+2),\quad
 Z=(i_0+1)z_1\cdots z_7,
\]
\[
 S=ZD_0^5,\quad T=\mathcal R(D_0,T_0,v),\quad X=Su-T,
\]
\[
 A_0=S^2C_\ast,\quad A_1=S^2w_1^2a_0,\quad
 A_2=S^2w_2^2a_1,
\]
\[
 V=X^2+A_2-A_0-A_1,\qquad
 W=V^2+4X^2A_2-4A_0A_1.
\]
Define the fixed integer polynomial
\[
 \boxed{P_{17}=W^2-16V^2X^2A_2.}
 \tag{6}
\]
All intermediate letters are polynomial abbreviations. No intermediate
letter is an additional quantified variable.

**Lemma 7 (three-root finalizer).** With the other sixteen coordinates fixed,
the assertion \(\exists u\in\mathbb Z:P_{17}=0\) is equivalent to
\[
 S\ne0,\quad S\mid T,\quad
 C_\ast,a_0,a_1\in\operatorname{Sq}(\mathbb Z).
 \tag{7}
\]
In the forward direction (7) is necessary for every assignment;
in the reverse direction, given the earlier coordinates and (7),
an integer u can be chosen.

Proof. Lemmas 1 and 6 give \(T\ne0\). If S=0, then
\(A_0=A_1=A_2=0,\ X=-T,\ P_{17}=T^8\ne0\).
So every zero has S nonzero.

For complex roots \(r_0^2=C_\ast,r_1^2=a_0,r_2^2=a_1\),
direct multiplication gives
\[
 P_{17}=\prod_{\epsilon_0,\epsilon_1,\epsilon_2\in\{-1,1\}}
 \big(X-S(\epsilon_0r_0+\epsilon_1w_1r_1+\epsilon_2w_2r_2)\big).
 \tag{8}
\]
A zero therefore makes one of the signed sums equal to the rational
number \(u-T/S\).

For every integer Cstar,
\(\sqrt{|C_\ast|}\le C_\ast^2\), with the zero case included.
For every pair of real numbers P,K,
\[
 \sqrt{|(P^2-1)K^2+1|}\le P^2+K^2+1.
 \tag{9}
\]
For example, square both nonnegative sides after using
\(|(P^2-1)K^2+1|\le(P^2+1)K^2+1\); the difference is
\(P^4+K^4+P^2K^2+2P^2+K^2\ge0\).
Thus
\[
 w_1>\sqrt{|C_\ast|},\qquad
 w_2>\sqrt{|C_\ast|}+w_1\sqrt{|a_0|}.
 \tag{10}
\]
If two signed sums in (8) differ, take the largest coordinate at which
a nonzero root's sign differs. The absolute value of that root is at
least 1, because its nonzero square is an integer. Its weighted
contribution strictly exceeds the sum of the absolute values of all
earlier contributions by (10). Hence distinct nonzero sign patterns
give distinct sums. This triangle-inequality argument works for negative
radicands as well as positive ones.

The field generated by the three complex roots is a finite Galois
extension of the rationals. Each automorphism changes root signs.
Since one encoded sum is rational, it is fixed by every automorphism;
the separation property forces every root in that sum to be fixed
individually. Each root is therefore rational. A rational number whose
square is an integer is an integer, so the three radicands are
nonnegative integer squares. Zero radicands cause no difficulty:
their roots are already zero, and signs on them are ignored.
The encoded sum is now an integer, hence \(T/S\) is an integer.
This proves necessity.

Conversely, choose integer roots of the three squares and put
\(u=T/S+r_0+w_1r_1+w_2r_2\). One factor in (8) vanishes.

## 6. Equivalence to the pinned consistency statement

**Theorem.** With the fixed coefficients above,
\[
 \mathrm{ZFC}\vdash
 \big(\nexists{\bf z}\in\mathbb Z^{17}:P_{17}({\bf z})=0\big)
 \longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

Proof. A zero yields (7). Since D0 is nonzero, S nonzero gives
i and every zj nonzero. Lemma 6 gives \(D_0\mid T_0\).
Lemma 4 gives the six nonnegative base coordinates and \(m>0\).
Lemma 3 gives \(h_0\ge0\); Lemma 2 permits replacement of i by \(|i|\),
yielding \(i_0\ge0\) without changing the ratio conditions.
Thus a solution of the original eight-natural-variable predicate (JR)
exists. Its imported equivalence supplies a finite ZFC refutation.

Conversely, such a refutation supplies a source solution of (JR).
Its i is positive. Lemma 4 supplies the seven nonzero z variables and
a square Cstar. Lemma 6 supplies v with \(S\mid T\), and S is nonzero.
Lemma 7 supplies u. Thus P17 has an integer zero.
Negating this equivalence proves the stated theorem.
All new arguments are ordinary elementary number theory and finite
Galois theory formalizable in ZFC. The theorem is an equivalence, not
a proof of either consistency or inconsistency.

## 7. Reproducible complexity and evidence

The delivered DAG has exactly 20,607 binary operations:
672 additions, 26 subtractions, and 19,909 multiplications.
Every multiplication by a numeral and every square is charged.
Fixed coefficient construction is not included in this arithmetic
evaluation cost, consistently with package 18. There are 348 named
fixed coefficient leaves, all fixed by the inherited recipe.

The exact degree is
\[
 424296\,5^{33}+53824
 =49\,394\,555\,389\,881\,134\,033\,203\,178\,824.
\]
It is an astronomic-degree alternative, not a competitor to the moderate-degree
26-integer polynomials on degree or bit complexity.

For auditing, let L=5^33. The source exact degrees are
\[
 \deg m=2221L+11,\quad \deg a_0=3800L+14,\quad
 \deg a_1=24640L+68,\quad \deg D_0=6875L+20.
\]
The first six guard stacks have degree recurrence \(c_j=3c_{j-1}+3\),
so \(\deg C_6=1092\). Consequently
\[
\begin{array}{c|r}
 C_\ast&2221L+3289\\
 w_1&4442L+6578\\
 w_2&6342L+6586\\
 S&34375L+108\\
 T&34375L+105\\
 X&34375L+109\\
 A_2&106074L+13456
\end{array}
\]
A2 has strictly larger degree than X squared, A0, and A1.
Thus V has leading term A2, W has leading term A2 squared, and
P17 has leading term A2 to the fourth power.
The source leading coefficient and the guard-stack leading coefficients
are nonzero, giving the exact degree displayed above.
The program independently propagates structural degree bounds and the
diagonal leading coefficient modulo 1,000,003; it certifies that the
output leading coefficient is nonzero and independent of every fixed port.

The executable finite checks include 24 exact modular comparisons
using the actual original T4 coefficients; 150 independent eight-factor
norm evaluations; roots of Pi modulo every modulus from 1 through 1200;
10,098 consecutive-square gap checks; and the signed-i symmetry.
These supplement, and do not replace, the universal proofs above.

Run
    python3 build_signed17.py
from this directory. The generator only uses the standard library and
the included source modules/data. It writes generated/signed17.json
and generated/signed17_checks.json. The latter is a diagnostic receipt,
not a formal proof certificate.

## 8. Source boundaries and further directions

The unchanged source expression and coefficient modules are from
18-jones9 at the stated repository commit. That package's original
source-acquisition pin was f0ae4e0991ca44a7bb4e5671d42e33d775e48035.
All nineteen imported source files are authenticated byte-for-byte against
the pinned Git blob identifiers, with SHA-256 hashes recorded in SOURCE_PINS.json.
The literal quartic and ordered tile list additionally match the hashes in
the upstream coefficient binding. The generator checks every source pin
before rebuilding the polynomial.

The reduction is inspired by the relation-combining method, coprime Pell
radicands, and intersective divisibility/nonvanishing merger. A recent
relevant primary source is Zhi-Wei Sun, “Ten unknowns for Hilbert's tenth
problem over the integers,” arXiv:2609.01594 (2026), whose Section 5 uses
a degree-six intersective polynomial. The degree-five version and all
application-specific arguments needed here have been proved above.
We have not completed an exhaustive novelty search and make no global
priority claim for these general devices.

Useful follow-up problems:
1. Determine whether the remaining j or phi positivity guard can be
   recovered from the source ratio conditions, removing another variable.
2. Instantiate the published ten-integer compiler on this exact quartic
   with a fully printed fixed-index recipe.
3. Formalize the square-stack lemma, homogeneous divisibility merger,
   and signed-i/h interface in Lean or Rocq.
4. Optimize the large digit-polynomial DAG; its approximately 20,500
   operations dominate this 17-integer specialization.
5. Rebind the entire construction to the smaller verified 943-tile
   coefficient tuple only after proving its complete quartic interface.
   No splicing of coefficient ports is valid.

