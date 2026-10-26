# Twenty-coordinate power copies: a code-free successor

This is a separate, unreviewed ordinary research proposal. The original
554-natural-variable source and its 5555-byte TeX plan remain immutable.
ROOT suggested the six polynomial definitions and the positive-quotient
shift below; the author independently checked both natural zero maps,
every deleted and retained residual, and the positivity of all eighteen
call sites. This is author work, not an independent peer review.

The proposed change gives a bijection with the original natural zero set.
Each power copy uses 20 private coordinates and 10 residuals in place of
27 and 17. The whole literal family has a hand census of 428 natural
coordinates and 206 squared residuals. This saves 126 coordinates and
126 residuals relative to that 554/332 source. Substitution can increase
degree and expression size. No exact global degree, support, height,
operation count, text-size saving or physical-page result is claimed.
There is no new accepted consistency endpoint or Lean formalization.

## 1. The complete unchanged arithmetic front

Every free coordinate is in N={0,1,2,...}. The free coordinates are

\[
 h,e,g,\beta,\xi_0,\ldots,\xi_8,F,x,N,\ell,z_0,z_t,z_B,
 \quad(D_i)_{i=0}^{3},\quad(P_j)_{j=0}^{10},
 \quad(r_j,s_j,w_j)_{j=0}^{10},\quad(\eta_j)_{j=0}^{17}.
\]

Each \(\eta_j\) is the exact 20-tuple in section 3. All other names
below are polynomial abbreviations, not additional free coordinates:

\[
\begin{aligned}
 t&=16+h,&y&=F+1+e,&q&=2+g,&B&=1+\beta,\\
 (C,a,b,c,d,S,T,u,v)&=(1+\xi_i)_{i=0}^{8},\\
 H&=2+C+a+b+c+d+S+T+u+v.
\end{aligned}
\]

Use the full polynomials \(J,L\) in section 2. Define every argument
and denominator selector by

\[
\begin{aligned}
 (k_i)_{i=0}^{3}&=(t,t+1,y+1,x),\\
 (U_j)_{j=0}^{10}&=(F^2+t,C,a,b,c,d,S,T,u,v,J),\\
 (\sigma_j)_{j=0}^{10}&=(0,0,1,1,1,1,2,2,3,3,1),\\
 \mathcal T&=\bigl((2(t+1),t,F),(B,x,N),(BH,x,q),\\
 &\hspace{35pt}(q,k_i,D_i)_{i=0}^{3},
       (q+1,U_j,P_j)_{j=0}^{10}\bigr).
\end{aligned}
\]

The concatenation is ordered and has precisely 3+4+11=18 entries.
Write \((n_j,k_j',m_j)=\mathcal T_j\), \(0\le j\le17\), and pair
it with \(\eta_j\). This is the entire argument table. It contains
polynomial expressions, with no variable exponent or variable index limit.

## 2. The complete unchanged C222 polynomial

The constructors and all nine codes are printed here so the equation
definition requires no external coefficient table or program:

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

The whole ninth bundle is

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

Each \(c_i\) is evaluated on \((a,b,c,d)\) and ignores unused
arguments. Define the complete label bound, guard, Horn factor and
local polynomial by

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

The guarded branch retains exactly the natural witness for both
disequalities \(c\ne a,c\ne b\). The Horn product includes truth,
the eight unconditional axioms, the full guarded bundle, modus ponens
and generalization. Nothing in this section is changed or weakened.
Every displayed sum/product has a fixed integer limit.

## 3. The new complete 20-coordinate power polynomial

For scalar arguments \(n,k,m\), the private natural tuple is

\[
 \eta=(Z,X,U,S,R,a_0,y_0,f,d,
 b_+,b_-,s_+,s_-,r_+,r_-,x_+,x_-,g,w_n,w_k).
\]

Every name here and every abbreviation in this paragraph is LOCAL to
this power copy. In particular its \(B,S,R,g\) are independent of the
arithmetic front and of the other seventeen copies. Put

\[
\begin{aligned}
 A&=a_0+2,&Y&=k+y_0,&V&=Y^2(d+1),\\
 B&=1+4Y(f+1),&\tau&=m+g+1,&W&=n+w_n,
\end{aligned}
\qquad
 \mathcal N(a,x,y)=x^2+y^2-1-a^2y^2.
\]

These SIX names are polynomial abbreviations, not coordinates. Let
\(\mathcal P_{20}(n,k,m;\eta)\) be the sum of the squares of EXACTLY
the following ten residuals, in order:

\[
\begin{gathered}
 \mathcal N(A,X,Y),\quad\mathcal N(A,U,V),\quad
 \mathcal N(B,S,R),\\
 B+Ub_+-A-Ub_-,\quad S+Us_+-X-Us_-,\\
 R+4Yr_+-k-4Yr_-,\\
 X+Yn+\tau x_+-YA-m-\tau x_-,\\
 2An-\tau-n^2-1,\quad W-k-w_k,\quad
 \mathcal N(W+1,A,WZ).
\end{gathered}
\]

No quotient, square root, variable power or external data is used in
these definitions. No strengthened bound such as \(W\ge m\) has been
added. The final norm and the same original \(W\ge n,k\) conditions
are retained exactly, with \(W\ge n\) written as its natural definition.

## 4. The whole successor equation

The one polynomial is

\[
\boxed{\begin{aligned}
 \mathcal Q_{20}={}&\sum_{j=0}^{17}
       \mathcal P_{20}(n_j,k_j',m_j;\eta_j)\\
 &+(x-F-1-(y+1)z_0)^2
   +(x-1-(1+(t+1)y)z_t)^2\\
 &+(Bz_B-C-F^2-1)^2
   +(L(C,a,b,c,d,S,T,u,v)-N\ell)^2\\
 &+(P_0-D_0(qw_0+B)-r_0)^2\\
 &+\sum_{j=1}^{10}(P_j-D_{\sigma_j}Nw_j-r_j)^2
   +\sum_{j=0}^{10}(D_{\sigma_j}-r_j-s_j-1)^2=0.
\end{aligned}}
\]

All coefficient data are defined in sections 1--3; the entire equation
is a finite composition of integer polynomials. There are still eleven
digit residuals and eleven natural remainder bounds. The outside 26
residuals and their natural coordinates are literally unchanged.

## 5. Exact local maps, including the lost lower-bound coordinate

Let \(\mathcal P_{27}\) be the EXACT seventeen-residual polynomial in
section 3 of the pinned original source. For this comparison write its
private quotient as \(f_{\rm old}\); its 27-tuple is

\[
 \zeta=(W,A,\tau,Z,X,Y,U,V,S,R,B,
 a_0,y_0,b_0,f_{\rm old},d,
 b_+,b_-,s_+,s_-,r_+,r_-,x_+,x_-,g,w_n,w_k).
\]

Fix \(n,m\in\mathbb N\) and \(k\ge1\). The claimed maps concern
natural ZERO SETS at these fixed arguments. They are not a bijection of
all natural ambient tuples and do not assert a zero-index extension.

### 5.1 Old to new

At an old zero its defining equations give

\[
 A=a_0+2,\ Y=k+y_0,\ B=b_0+2,\ B=1+4Yf_{\rm old},
 \ V=Y^2(d+1),\ \tau=m+g+1,\ W=n+w_n.
\]

Since \(k\ge1\), \(Y\ge1\). Also \(B\ge2\), so
\(f_{\rm old}=0\) would force \(B=1\), a contradiction. Hence
\(f_{\rm old}\ge1\). Define \(\pi(\zeta)=\eta\) by retaining the
nineteen common coordinates and setting \(f=f_{\rm old}-1\).
Every retained coordinate is natural and so is \(f\). The six new
abbreviations recover the old six values, including
\(1+4Y(f+1)=1+4Yf_{\rm old}=B\). Each of the ten new residuals is
therefore an old zero residual. Thus \(\pi\) maps old zeros to new zeros.

### 5.2 New to old

For a new zero define \(\iota(\eta)=\zeta\) by retaining every named
coordinate except the shifted \(f\), and restoring

\[
\begin{aligned}
 A&=a_0+2,&Y&=k+y_0,&V&=Y^2(d+1),\\
 B&=1+4Y(f+1),&\tau&=m+g+1,&W&=n+w_n,\\
 f_{\rm old}&=f+1,&b_0&=B-2=4Y(f+1)-1.
\end{aligned}
\]

The only potentially negative restoration is \(b_0\). But
\(Y\ge k\ge1\) and \(f+1\ge1\), so \(b_0\ge3\). Thus ALL 27
restored coordinates are natural. No divisibility or rational witness
has been introduced. The seven removed rows are zero by the definitions,
and the other ten are exactly the new rows. Therefore the restored tuple
is an old zero.

### 5.3 Every residual, not only the leading norm

The following is the complete old-to-new residual correspondence.
Old numbering is the order in the pinned original section 3; new
numbering is the order in this section 3.

| Old row | Original residual | Pullback under iota |
|---:|---|---|
| 1 | A-a_0-2 | 0 by definition |
| 2 | Y-k-y_0 | 0 by definition |
| 3 | B-b_0-2 | 0 by b_0=B-2 |
| 4 | N(A,X,Y) | New 1 |
| 5 | N(A,U,V) | New 2 |
| 6 | N(B,S,R) | New 3 |
| 7 | B-1-4Y f_old | 0 by f_old=f+1 |
| 8 | V-Y^2(d+1) | 0 by definition |
| 9 | B+U b_+-A-U b_- | New 4 |
| 10 | S+U s_+-X-U s_- | New 5 |
| 11 | R+4Y r_+-k-4Y r_- | New 6 |
| 12 | X+Yn+tau x_+-YA-m-tau x_- | New 7 |
| 13 | 2An-tau-n^2-1 | New 8 |
| 14 | tau-m-g-1 | 0 by definition |
| 15 | W-n-w_n | 0 by definition |
| 16 | W-k-w_k | New 9 |
| 17 | N(W+1,A,WZ) | New 10 |

Here `N(a,x,y)` in the table denotes the printed norm polynomial
\(\mathcal N\), not the outer amplification coordinate \(N\).
In particular there are exactly seven deleted rows and ten retained rows.
Substitution gives the polynomial identity

\[
 \mathcal P_{27}(n,k,m;\iota(\eta))
       =\mathcal P_{20}(n,k,m;\eta).
\]

As a ring identity this holds even outside the positive-index domain;
the DOMAIN statement about natural restored coordinates uses \(k\ge1\).
No finite expansion or coefficient collector is needed for this exact
seventeen-row substitution proof.

### 5.4 Both composites and the inherited power theorem

For any new zero, \(\pi\iota\) keeps every coordinate, including
\((f+1)-1=f\). For any old zero, \(\iota\pi\) restores its six
deleted values by its own defining rows; its quotient is
\((f_{\rm old}-1)+1=f_{\rm old}\), and its removed lower-bound witness
is \(B-2=b_0\). Every other named coordinate was retained. Both
composites are therefore the identity on the respective natural zero sets.

Consequently, for positive \(n,k\), the new graph has a natural zero
exactly when the old standard graph does, hence exactly when \(m=n^k\).
This invokes precisely the inherited standard Pell theorem, with no new
Pell assertion or stronger inequality. The maps also transport all
private existence witnesses rather than merely proving one implication.

## 6. Every call's positivity and the whole-instance bijection

The local inverse must not be used at an unproved positive index. Here
is the complete whole-instance bootstrap, valid for BOTH whole equations.

At a new zero, the first slot has \(k=t\ge16\) and
\(n=2(t+1)\ge34\), before interpreting any other graph. Restore only
that copy by \(\iota\); its old positive-power theorem gives
\(F=(2(t+1))^t\ge1\). The unchanged first endpoint now gives
\(x=F+1+(y+1)z_0\ge F+1\ge2\).
At an old zero the same conclusion follows directly from its first
standard power copy and the same endpoint.

The COMPLETE eighteen-site positivity ledger is therefore:

| Slot(s) | Base | Index | Positivity reason |
|---|---|---|---|
| 0 | 2(t+1) | t | t>=16 before every semantic step |
| 1 | B | x | B=1+beta>=1; x>=2 after slot 0 |
| 2 | BH | x | B>=1; H=2+sum of nine positive reps>=11; x>=2 |
| 3--6 | q | t,t+1,y+1,x | q=2+g>=2; t>=16; y=F+1+e>=1; x>=2 |
| 7 | q+1 | F^2+t | q+1>=3; F^2+t>=16 |
| 8--16 | q+1 | C,a,b,c,d,S,T,u,v | Each actual representative is 1+xi_i>=1 |
| 17 | q+1 | J | Nonnegative constructor polynomials and final +1 give J>=1 |

All bases and indices required by the LOCAL natural-map theorem have
now been proved positive without using any later binomial, local-row,
label, or CRT interpretation. The order of slots 1 and 2 is irrelevant
to that positivity statement, but both follow the first-slot bootstrap.

Define the global \(\Pi\) from an old zero by keeping all 68 front/digit
coordinates and applying \(\pi\) to each of its eighteen private tuples.
The preceding ledger proves each application is valid. Define global
\(\mathit I\) from a new zero by keeping the same 68 coordinates and
applying \(\iota\) to each private tuple, after the first-slot bootstrap.
All twenty-six outside residuals are unchanged and all private blocks
vanish by section 5. Thus both maps preserve the entire equations.
Their composites are the identity on every named coordinate, because
the front is fixed and the eighteen local composites are identities.

There is also the direct whole polynomial identity
\(\mathcal Q_{27}\circ\mathit I=\mathcal Q_{20}\), obtained by the
complete residual table and the fixed front. As before, its ring-identity
meaning is unrestricted, while its natural-zero-map meaning uses the
proved call positivity. No assumed common center, index, native rank or
coefficient tuple is being transferred between unrelated constructions.

## 7. Exact unchanged ordinary proof and calibration boundary

For the consistency interpretation, the unchanged mathematical source
is the EXACT 510-line README at actual commit
`674fbc315ac72fc8d2a66428f4d736a17ddc00ae`, path
`Computability/DiophantineConsistency/research/direct-c222-one-page-template/README.md`,
SHA-256 `11280fd509b34641e500a8b733778f663bce713c83958d18fb457ed19cb5acb2`.
Its full literal front and all table data have been reprinted above.
Its ordinary sections 5.1--5.5 and 6 are the specifically retained proof,
not an unnamed compiler or an inferred finite-test theorem.

In the soundness direction, restore the whole old zero by section 6 and
apply those exact arguments: recover all powers and the true binomial
carrier; use its hand C222 majorants \(L<r^{7,341,512}<r^{2^{23}}\) and
\(J<r^{2^{22}}\); use the endpoint budgets to decode all ten ranges;
use full prime-power coverage for every row and every prime; glue the
beta states; recover label multiplicities by large polynomial evaluation;
and close truth under the actual single-conclusion rules to derive falsity.
All inputs to those arguments are literally the unchanged restored front.
The complete guarded bundle, derived J range, strict u,v<x ranges and
both endpoint rows remain present. No consistency assumption is used.

In the converse direction, use the exact original section 6 from a finite
C222 refutation. It chooses a fresh proof horizon, pending-weight path,
beta CRT code and all-primes precision-2x representatives, then every true
power and its ordinary private witnesses. Its first-slot positivity and
the ledger above ensure \(f_{\rm old}\ge1\) in every such private copy.
Apply \(\Pi\) to this ENTIRE constructed zero. This retains the complete
front, all remainder witnesses, all 18 actual triples and their full
private data after the explicit maps; it yields a new zero with no division
of a witness or claim about only selected ports.

Thus the successor is exactly equivalent to the original equation's
zero-existence statement. Composing the retained ordinary proof with
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` gives the SAME
proposed ordinary Con(ZFC) equivalence. Those inherited calibration and
Pell facts retain the original source's stated proof boundary. Neither
their transitive Lean closure nor a new object-ZFC proof was compiled.
This is not a claim that an unreviewed source or this successor has been
accepted; the whole source and these maps still require independent review.

## 8. Counts, domain maps and scope

The front has \(20+15+33=68\) natural coordinates. The new private
family has \(18\cdot20=360\), giving 428 total. Its power residuals
number \(18\cdot10=180\), and the unchanged outside family has
\(4+1+10+11=26\), giving 206. The original differences are
\(18(27-20)=126\) coordinates and \(18(17-10)=126\) residuals.
These are hand counts of the printed unquadraticized polynomial family.
They are not generated coefficient metrics, arithmetic-operation counts
or a variable optimum. The same uniform substitution \(z=p_z-1\) for
each free coordinate gives an exactly equivalent 428-positive-variable
equation and transports both whole maps.

Deleting monic definitions raises the degree of retained expressions.
In particular the norm using \(V=Y^2(d+1)\) now contains
\(-A^2Y^4(d+1)^2\). No unchanged-degree, smaller-support, smaller-height,
shorter printed page, lower arithmetic-cost or current-frontier dominance
claim follows from the coordinate and row savings. No new TeX or PDF is
prepared as part of this mathematical note; a separate literal plan could
be made after review if useful.

The author reread the entire exact 510-line original mathematical source,
authenticated its three files as current bytes and actual Git blobs, and
preserved the original 5555-byte page plan. No new incoming proposal or
peer verdict is a premise. Exact pins, read scope and before/after records
are in `SOURCE_PINS.md`. Only inert text/Git/hash/metadata reads, hand
mathematics and author Markdown/inert manifest writing were used. No
program, helper, import, AST, coefficient collector, mathematical evaluator,
prime/order/residue/Pell computation, native application, Lean, TeX/PDF,
render/visual tool, source repair, main edit, commit or promotion was run.
