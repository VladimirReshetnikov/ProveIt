# Retaining the Pell ordinate: a code-free degree tradeoff

This is a separate, unreviewed ordinary proposal. ROOT suggested retaining
the independent Pell ordinate Y and supplied an initial degree estimate.
The author independently checked all local maps, the whole eighteen-call
bootstrap, every constructor degree and every source of a large degree.
Neither ROOT's conceptual lead nor the author's work is a peer review.
The frozen 554-variable source, its 5555-byte page plan and the separate
428-variable successor remain unchanged.

The new literal equation uses 21 private coordinates and 11 residuals
per power copy. The hand census is 446 natural coordinates and 224 squared
residuals. A hand polynomial-degree proof below gives exact total degree
2,097,684, the same as the original 554/332 recipe. In contrast, the frozen
428/206 recipe has exact degree 4,194,312 by the separate hand proof here.
These are unreviewed algebraic deductions for THESE three printed families,
not generated coefficient metrics or accepted consistency endpoints.
No shorter page, smaller support/height, lower arithmetic cost or current
frontier dominance is claimed. No application or mathematical helper ran.

## 1. Complete unchanged front and all eighteen triples

Every free coordinate ranges over N={0,1,2,...}. They are

\[
 h,e,g,\beta,\xi_0,\ldots,\xi_8,F,x,N,\ell,z_0,z_t,z_B,
 \quad(D_i)_{i=0}^{3},\quad(P_j)_{j=0}^{10},
 \quad(r_j,s_j,w_j)_{j=0}^{10},\quad(\theta_j)_{j=0}^{17}.
\]

Each \(\theta_j\) is the exact 21-tuple in section 3. Define polynomial
abbreviations, not additional coordinates, by

\[
\begin{aligned}
 t&=16+h,&y&=F+1+e,&q&=2+g,&B&=1+\beta,\\
 (C,a,b,c,d,S,T,u,v)&=(1+\xi_i)_{i=0}^{8},\\
 H&=2+C+a+b+c+d+S+T+u+v,\\
 (k_i)_{i=0}^{3}&=(t,t+1,y+1,x),\\
 (U_j)_{j=0}^{10}&=(F^2+t,C,a,b,c,d,S,T,u,v,J),\\
 (\sigma_j)_{j=0}^{10}&=(0,0,1,1,1,1,2,2,3,3,1),\\
 \mathcal T&=\bigl((2(t+1),t,F),(B,x,N),(BH,x,q),\\
 &\hspace{30pt}(q,k_i,D_i)_{i=0}^{3},
       (q+1,U_j,P_j)_{j=0}^{10}\bigr).
\end{aligned}
\]

Here J is the fully printed polynomial below. The ordered concatenation
has 3+4+11=18 entries. Set \((n_j,k'_j,m_j)=\mathcal T_j\) in that order,
and pair it with \(\theta_j\). All index ranges in the equation are fixed.

## 2. The entire unchanged numerical C222 polynomial

\[
\begin{aligned}
 I(a,b)&=2(a+b)(a+b+1)+4b,\\
 M(a,b)&=I(a,b)+1,&A(a,b)&=I(a,b)+2,&E(a,b)&=I(a,b)+3,\\
 \nu(a)&=I(a,1),&X(a,b)&=\nu(A(a,\nu(b))),\\
 c_1&=X(a,E(a,b)),\\
 c_2&=I(A(a,I(b,c)),I(A(a,b),A(a,c))),\\
 c_3&=I(E(a,b),I(M(c,a),M(c,b))),\\
 c_4&=I(A(a,A(b,c)),A(b,A(a,c))),\\
 c_5&=I(E(c,a),I(M(c,b),M(a,b))),\\
 c_6&=I(X(a,A(a,b)),b),\\
 c_7&=I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),\\
 c_8&=I(I(I(c,d),a),I(I(a,c),I(b,c))).
\end{aligned}
\]

The full guarded ninth bundle is

\[
\begin{aligned}
 R(b,k,z)&=A(b,I(z,\nu(A(b,I(z,\nu(M(b,k))))))),\\
 Q(a,b,k)&=A(k,I(M(k,a),M(k,b))),\\
 C_0(a,b,k,z)&=I(Q(a,b,k),R(b,k,z)),\\
 C_1(a,b,k,z)&=\nu(A(a,C_0(a,b,k,z))),\\
 C_2(a,b,k,z)&=\nu(A(a,I(z,C_1(a,b,k,z)))),\\
 C_*(a,b,k,z)&=A(b,I(M(b,k),C_2(a,b,k,z))),\\
 V(a,b,c)&=I(M(a,b),A(c,M(a,b))),\\
 K(a,b,c)&=A(c,I(C_*(a,b,c,c),\nu(R(b,c,c)))),\\
 c_9(a,b,c)&=\nu(I(V(a,b,c),K(a,b,c))).
\end{aligned}
\]

Each \(c_i\) is evaluated on \((a,b,c,d)\) and ignores unused arguments.
Define

\[
\begin{aligned}
 W_z&=1+Fz,\\
 J(a,b,c,d)&=\sum_{i=1}^{9}c_i+a+b+I(a,b)+A(a,b)+1,\\
 G&=((c-a)^2(c-b)^2-(d+1)^2)^2,\\
 \mathcal H&=(T-S)^2\prod_{i=1}^{8}(TW_{c_i}-S)^2\\
 &\quad\cdot\bigl((TW_{c_9}-S)^2+G\bigr)
       (TW_b-SW_aW_{I(a,b)})^2
       (TW_{A(a,b)}-SW_b)^2,\\
 L(i,a,b,c,d,S,T,u,v)
 &=\mathcal H+(x-S-(1+(i+1)y)u)^2
             +(x-T-(1+(i+2)y)v)^2.
\end{aligned}
\]

The twelve Horn branches, full guarded bundle and its natural disequality
witness, derived label range and both beta conditions are unchanged.
This is an explicit polynomial recipe, not an external syntax/coefficients
table, and no logical simplification has changed its numerical codes.

## 3. The complete new 21-coordinate graph

For scalar arguments \((n,k,m)\) let the private natural tuple be

\[
 \theta=(Y,Z,X,U,S,R,a_0,y_0,f,d,
 b_+,b_-,s_+,s_-,r_+,r_-,x_+,x_-,g,w_n,w_k).
\]

All names in this paragraph are LOCAL to that copy, independently of the
front and the other copies. Unlike the twenty-coordinate graph, Y is a
FREE coordinate. Define only these FIVE polynomial abbreviations:

\[
 A=a_0+2,\quad V=Y^2(d+1),\quad B=1+4Y(f+1),\quad
 \tau=m+g+1,\quad W=n+w_n,
 \qquad\mathcal N(a,x,y)=x^2+y^2-1-a^2y^2.
\]

The polynomial \(\mathcal P_{21}(n,k,m;\theta)\) is the sum of the squares
of exactly the following eleven residuals, in order:

\[
\begin{gathered}
 Y-k-y_0,\\
 \mathcal N(A,X,Y),\quad\mathcal N(A,U,V),\quad
 \mathcal N(B,S,R),\\
 B+Ub_+-A-Ub_-,\quad S+Us_+-X-Us_-,\\
 R+4Yr_+-k-4Yr_-,\\
 X+Yn+\tau x_+-YA-m-\tau x_-,\\
 2An-\tau-n^2-1,\quad W-k-w_k,\quad
 \mathcal N(W+1,A,WZ).
\end{gathered}
\]

In particular Y is NOT substituted by k+y_0 when computing this
polynomial's degree. That equality is one of its residuals. The original
W>=n,k and strict output conditions are retained through the definitions
and residuals; no stronger W bound or new Pell theorem is assumed.

## 4. The entire single equation

\[
\boxed{\begin{aligned}
 \mathcal Q_{21}={}&\sum_{j=0}^{17}
       \mathcal P_{21}(n_j,k'_j,m_j;\theta_j)\\
 &+(x-F-1-(y+1)z_0)^2
   +(x-1-(1+(t+1)y)z_t)^2\\
 &+(Bz_B-C-F^2-1)^2
   +(L(C,a,b,c,d,S,T,u,v)-N\ell)^2\\
 &+(P_0-D_0(qw_0+B)-r_0)^2\\
 &+\sum_{j=1}^{10}(P_j-D_{\sigma_j}Nw_j-r_j)^2
   +\sum_{j=0}^{10}(D_{\sigma_j}-r_j-s_j-1)^2=0.
\end{aligned}}
\]

All coefficient data are on the preceding literal definitions. Fixed
compositions and fixed sums/products give an ordinary integer polynomial.
There is no variable exponent or variable-length program in its definition.

## 5. Full natural maps, including the Y-row obligation

The old 27-coordinate graph is EXACTLY section 3 of the original pinned
554-variable source. Write its private quotient as f_old. For fixed
\(n,m\in\mathbb N\), \(k\ge1\), an old zero gives Y=k+y_0>=1,
B=b_0+2>=2 and B=1+4Y f_old. Thus f_old>=1. Project to the new tuple
by retaining the TWENTY common coordinates (including Y), and set
f=f_old-1 as the twenty-first. Every new residual vanishes by an old row.

Conversely, at a NEW ZERO the retained FIRST row gives Y=k+y_0>=1.
Restore A,V,B,tau,W by the five definitions, restore f_old=f+1, and set
b_0=B-2=4Y(f+1)-1>=3. All old coordinates are natural. This naturality
uses the retained Y row: for arbitrary ambient new tuples, positive k
alone would not bound an independent Y from below. No ambient-natural
bijection, or zero-index extension, is asserted.

The complete old-to-new residual table is

| Old row | Original residual | New pullback |
|---:|---|---|
| 1 | A-a_0-2 | 0 |
| 2 | Y-k-y_0 | New 1 |
| 3 | B-b_0-2 | 0 |
| 4 | N(A,X,Y) | New 2 |
| 5 | N(A,U,V) | New 3 |
| 6 | N(B,S,R) | New 4 |
| 7 | B-1-4Y f_old | 0 |
| 8 | V-Y^2(d+1) | 0 |
| 9 | B+U b_+-A-U b_- | New 5 |
| 10 | S+U s_+-X-U s_- | New 6 |
| 11 | R+4Y r_+-k-4Yr_- | New 7 |
| 12 | X+Yn+tau x_+-YA-m-tau x_- | New 8 |
| 13 | 2An-tau-n^2-1 | New 9 |
| 14 | tau-m-g-1 | 0 |
| 15 | W-n-w_n | 0 |
| 16 | W-k-w_k | New 10 |
| 17 | N(W+1,A,WZ) | New 11 |

`N` in this table is the printed norm, not the outer amplification variable.
Thus six defining rows disappear and all eleven retained rows are covered.
The pullback identity P_27(iota_21(theta))=P_21(theta) holds over integers
as a ring identity. Its natural-zero interpretation uses the Y row above.
The two map composites recover f by (f+1)-1 and f_old by (f_old-1)+1;
they recover the five eliminated values by their old defining rows, and
b_0 by B-2. Every other coordinate, including Y, is fixed. Hence they
are inverse bijections of the natural zero sets at fixed positive k.

For the full equation, restore only slot 0 first: its k=t>=16, n>=34
and its retained Y row make this valid. The old power theorem gives
F=(2(t+1))^t>=1, and the first endpoint gives x>=F+1>=2. This proves
ALL eighteen calls have positive index, before restoring the others:

| Slots | Base(s) | Index/indices | Why positive |
|---|---|---|---|
| 0 | 2(t+1) | t | t>=16 |
| 1--2 | B,BH | x,x | B>=1,H>=11,x>=2 |
| 3--6 | q | t,t+1,y+1,x | q>=2,t>=16,y>=1,x>=2 |
| 7 | q+1 | F^2+t | q+1>=3,F^2+t>=16 |
| 8--16 | q+1 | C,a,b,c,d,S,T,u,v | All nine actual representatives are >=1 |
| 17 | q+1 | J | Nonnegative constructors and +1 give J>=1 |

Keep the entire 68-coordinate front, and apply the local maps to all
eighteen copies. The 26 outside rows are unchanged. Both global maps
therefore preserve the ENTIRE equations and are inverse on every named
coordinate. The corresponding whole ring identity is Q_27 composed with
the polynomial restoration equals Q_21. No subset of ports or private
witnesses is being transported in place of a whole zero.

The exact original ordinary sections 5.1--5.5 and 6, pinned below, now
transfer: soundness restores an original zero and uses all carrier/range/
CRT/majorant/guarded-Horn arguments; completeness constructs the ENTIRE
original zero from a refutation, and projects all eighteen private tuples.
The original standard positive-power theorem and C222/ZF/ZFC calibration
are the only retained mathematical foundations. There is no new Pell,
prime/controller, native-rank or choice-of-private-center premise.

Deleting the new first row and replacing Y everywhere by k+y_0 also
gives EXACTLY the frozen twenty-coordinate graph. Projection forgets Y;
its inverse restores Y=k+y_0. These are inverse natural zero maps (indeed
the restoration is natural for nonnegative k), and their local polynomial
pullback is P_20. The same first-slot argument transports complete whole
zeros. This explains the degree tradeoff without changing either source.

## 6. Independent hand degree proof for all three families

Degree means ordinary TOTAL DEGREE in the free ambient coordinates of
the printed polynomial. No equation is substituted into another when
measuring degree, except the definitions explicitly declared polynomial
abbreviations in that particular source. These calculations use hand
composition and leading homogeneous forms, not expansion or a helper.

For nonconstant nonnegative-coefficient inputs, the degree of I is
twice their maximum degree: its leading quadratic square cannot cancel.
The constructors M,A,E add constants to I and have that same degree;
nu=I(_,1) doubles a positive input degree. Starting at degree one gives
these EXACT degrees from the printed constructors:

| Polynomial(s) | Degree(s) |
|---|---|
| c_1,...,c_8 | 16,8,8,8,8,32,16,8 (sum 104) |
| R,Q,C_0,C_1,C_2 | 128,8,256,1024,8192 |
| C_*,V,K,c_9 | 32768,8,131072,524288 |
| J | 524288 |

The R and Q arguments used inside the bundle are variables or repeated
variables, with no subtraction. Repeated actual argument c in two positions
therefore cannot cancel their leading forms. The affine positive shifts
1+xi_i likewise preserve degree. All these constructor polynomials have
nonnegative coefficients, so their leading forms and the top form J_top
are nonzero. Set D=524288 below.

The exact degrees of the Horn factors are

| Factor | Degree |
|---|---:|
| (T-S)^2 | 2 |
| Product of eight unconditional factors | 2*104+8*4=240 |
| Guarded bundle factor | 2*D+4=1048580 |
| Modus ponens factor | 12 |
| Generalization factor | 8 |

The bundle guard G has degree 8 and is strictly lower than the other
term of its factor. Each unconditional factor has degree 2*deg(c_i)+4.
In the MP inner difference the second term has degree 6 and the first
degree 3; in generalization they have degrees 4 and 3. The truth factor
is nonzero because S,T are independent affine coordinates. Thus every
listed leading form is nonzero, their product is nonzero, and

\[
 \deg\mathcal H=2+240+1048580+12+8=1048842.
\]

Both beta-error squares in L(C,...) have degree 6. Consequently
deg L=1048842. The outer residual L-N*ell has the same degree, and its
square has exact degree 2097684. All other outside squared rows have
degree at most 6. This dominant outside row is identical in all families.

All eighteen base arguments have degree at most two (only BH reaches
two); outputs have degree one. All requested indices have degree at most
two EXCEPT the last, J, of degree D. These facts follow from the FULL
printed table, not just its J slot.

In the ORIGINAL 27-coordinate graph all rows except the three containing
k have squared degree at most 12 after substitution. Those index-linear rows
can have degree D before squaring: Y-k-y_0, the R congruence, and
W-k-w_k. Thus every private squared row has degree at most 2D=1048576.
The outside L square dominates. Hence Q_27 has EXACT degree 2097684.

In the TWENTY-coordinate graph at its last slot,

\[
 \deg Y=D,\quad \deg V=2D+1=1048577,\quad
 \deg\mathcal N(A,U,V)=4D+4=2097156.
\]

Its square has degree 8D+8=4194312. Its top homogeneous form is exactly
\(a_{0,17}^4 d_{17}^4 J_{\rm top}^8\), which is nonzero. In this same
slot the other norm squares have degrees 4D+4 and 4D+8; each remaining
squared row is at most 2D+2, apart from the small final frame. Every OTHER
slot has degree at most 24: its index has degree at most two, its base at
most two, and its output degree one. Therefore no other row reaches
4194312, and Q_20 has EXACTLY that degree.

In the present TWENTY-ONE-coordinate graph, independent Y has degree one,
V has degree three, A and tau degree one, B degree two and W degree at
most two. Parts not involving the requested index have squared degree
at most 20: the final frame reaches this bound when n=BH. The THREE
rows containing k linearly are Y-k-y_0, R+4Yr_+-k-4Yr_-, and W-k-w_k.
All three have degree D at the J slot, hence square degree 2D=1048576.
No other large-index occurrence is present. Thus every private squared
row has degree below 2097684 and the unchanged L square dominates:
Q_21 has EXACT degree 2097684.

Finally, a sum of squares cannot cancel away its maximal even degree:
its top form is the sum of squares of the maximal-degree residuals'
nonzero leading forms, and that real polynomial is not identically zero.
This also justifies the dominance arguments if a row's leading form is
not coefficientwise positive. Uniform translation to positive coordinates
is invertible affine and preserves each of these total degrees.

## 7. Counts, exact proof bindings, and author boundary

The private family has 18*21=378 coordinates; adding the unchanged 68
gives 446. Its squared rows number 18*11=198, plus the unchanged 26,
giving 224. It adds exactly eighteen coordinates and eighteen rows to
the twenty-coordinate source, and removes 108 of each from the original.
Uniformly replace every free z by p_z-1, p_z>=1, for the exactly equivalent
446-positive-variable version. No variable optimum is claimed.

The complete original proof input is the 510-line README at actual commit
674fbc315ac72fc8d2a66428f4d736a17ddc00ae, path
`Computability/DiophantineConsistency/research/direct-c222-one-page-template/README.md`,
SHA-256 `11280fd509b34641e500a8b733778f663bce713c83958d18fb457ed19cb5acb2`;
its manifest is `5fd0b9115ec010c0bb626d0ff7f97cc9a23583d0a10705cf37c4972f5c9913bf`.
The exact twenty-coordinate comparator is the separately frozen source
`../direct-c222-twenty-power-template/`, manifest
`a8dec16d8e0c5b18ed21ca394c365e4c24e413bb26cd5b06690adff58e8016bf`.
All full proof scopes, actual Git/current pins and preserved old page-plan
records are in `SOURCE_PINS.md`. No later peer verdict is used as a premise.

The original ordinary Con(ZFC) calibration and Pell theorem have their
original inherited proof boundary; their transitive Lean closure is not
newly checked. The algebraic maps and degree proof here are unreviewed.
Nothing accepts an original or new endpoint, proves consistency, gives
a complete proof-assistant result, predicts a finite residue, or establishes
a page/text saving. No new TeX is prepared. No source, main page, old plan,
review or Lean file is edited or resealed. No app/import/AST/helper/math
evaluation/collector/Pell computation, Lean, TeX/PDF/render, commit or
promotion was run. All work is hand mathematics and inert text/metadata.
