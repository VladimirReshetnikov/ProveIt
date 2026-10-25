# A complete indexed C222 recipe: code-free text-size exploration

This is an unreviewed ordinary research draft. It proposes a fresh equation
over natural numbers, using a fully printed C222 calculus and eighteen
independent copies of a fully printed positive-power certificate. It does
not specialize a machine, use the 436-symbol seed, import a coefficient
table, or depend on an unprinted gate graph. No incoming program, evaluator,
compiler, proof assistant, TeX engine, or renderer was run in this research.

The concrete feasibility result is that all the data needed for this recipe
fit into the formulas in sections 1--4: one constructor recipe, an explicit
eighteen-entry argument family, seventeen power residuals, eleven digit
checks, and four outer residuals. All index ranges are fixed integers.
Whether those formulas are legible on one physical page is UNTESTED. Their
text length has not been measured against the maintained page.

This deliberately spends variables and degree to reduce the amount of data
that must be printed. It is not the incoming 242-integer-variable quartic,
and does not improve the maintained fifteen-positive-variable, 66-operation,
degree-157 point in those metrics. A hand census of THIS literal recipe is
554 natural variables and 332 squared residuals. Its nested syntax
constructors make it a fixed high-degree polynomial; no exact expanded
degree, support, height, arithmetic-operation count, or byte saving is
claimed. The census and ordinary argument still require independent review.

## 1. All variables and the literal arithmetic front

Every free coordinate below ranges over N={0,1,2,...}. The independent
coordinates are

\[
 h,e,g,\beta,\xi_0,\ldots,\xi_8,F,x,N,\ell,z_0,z_t,z_B,
 \quad D_0,\ldots,D_3,\quad P_0,\ldots,P_{10},
 \quad (r_j,s_j,w_j)_{0\le j\le10},
 \quad (\zeta_j)_{0\le j\le17}.
\]

Each \(\zeta_j\) is exactly the 27-tuple printed in section 3. All the
following names are polynomial abbreviations, NOT additional coordinates:

\[
 t=16+h,\quad y=F+1+e,\quad q=2+g,\quad B=1+\beta,
 \quad (C,a,b,c,d,S,T,u,v)=(1+\xi_i)_{i=0}^{8},
 \quad H=2+C+a+b+c+d+S+T+u+v.
\]

Use the fully specified \(J,L\) of section 2 and put

\[
\begin{aligned}
 (k_i)_{i=0}^{3}&=(t,t+1,y+1,x),\\
 (U_j)_{j=0}^{10}&=(F^2+t,C,a,b,c,d,S,T,u,v,J),\\
 (\sigma_j)_{j=0}^{10}&=(0,0,1,1,1,1,2,2,3,3,1).
\end{aligned}
\]

The complete ordered eighteen-entry argument family is

\[
 \mathcal T=
 \bigl((2(t+1),t,F),(B,x,N),(BH,x,q),
       (q,k_i,D_i)_{i=0}^{3},
       (q+1,U_j,P_j)_{j=0}^{10}\bigr).
\]

The order associates its entries with \(\zeta_0,\ldots,\zeta_{17}\).
This displayed family is the entire power-request table. The equation has
no variable exponent: each triple is an argument to the polynomial
\(\mathcal P\) in section 3.

## 2. Every C222 constructor and local residual

Define these integer polynomials, using the same definitions at every
appearance:

\[
\begin{aligned}
 I(a,b)&=2(a+b)(a+b+1)+4b,\\
 M(a,b)&=I(a,b)+1,& A(a,b)&=I(a,b)+2,& E(a,b)&=I(a,b)+3,\\
 \nu(a)&=I(a,1),& X(a,b)&=\nu(A(a,\nu(b))).
\end{aligned}
\]

The eight unconditional axiom codes are

\[
\begin{aligned}
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

For the ninth, guarded code the following definitions specify the whole
bundle, including all argument positions:

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

Here \(c_1,\ldots,c_8\) also denote the displayed polynomials in their
four available arguments. They simply ignore any unused argument.
Write \(W_z=1+Fz\) and define

\[
\begin{aligned}
 J(a,b,c,d)&=\sum_{i=1}^{9}c_i+a+b+I(a,b)+A(a,b)+1,\\
 G&=((c-a)^2(c-b)^2-(d+1)^2)^2,\\
 \mathcal H&=(T-S)^2\prod_{i=1}^{8}(T W_{c_i}-S)^2\\
 &\quad\cdot\bigl((T W_{c_9}-S)^2+G\bigr)
 (T W_b-S W_aW_{I(a,b)})^2
 (T W_{A(a,b)}-S W_b)^2,\\
 L(i,a,b,c,d,S,T,u,v)
 &=\mathcal H+(x-S-(1+(i+1)y)u)^2
             +(x-T-(1+(i+2)y)v)^2.
\end{aligned}
\]

All products here have the FIXED limits printed. The argument \(i\) is
substituted by \(C\) in the final polynomial; there is no product or sum
with variable limit \(t\) in that polynomial. The guard says precisely
\(c\ne a,c\ne b\) on a vanishing guarded branch: its natural witness is
\(d=|(c-a)(c-b)|-1\). The other factors are truth, the eight axioms,
modus ponens, and generalization. The full bundle has been retained.

## 3. The entire positive-power polynomial

The auxiliary 27-tuple for a call \((n,k,m)\) is

\[
 \zeta=(W,A,\tau,Z,X,Y,U,V,S,R,B,
 a_0,y_0,b_0,f,d,
 b_+,b_-,s_+,s_-,r_+,r_-,x_+,x_-,g,w_n,w_k).
\]

Names in this tuple are LOCAL to this copy. In particular its \(B,S,R\)
notation does not identify any coordinate with the arithmetic front;
the modulus coordinate here is named \(\tau\), not \(T\).
For \(\mathcal N(a,x,y)=x^2+y^2-1-a^2y^2\), let
\(\mathcal P(n,k,m;\zeta)\) be the sum of the squares of EXACTLY the
following seventeen expressions:

\[
\begin{gathered}
 A-a_0-2,\quad Y-k-y_0,\quad B-b_0-2,\\
 \mathcal N(A,X,Y),\quad\mathcal N(A,U,V),\quad
 \mathcal N(B,S,R),\\
 B-1-4Yf,\quad V-Y^2(d+1),\\
 B+Ub_+-A-Ub_-,\quad S+Us_+-X-Us_-,\\
 R+4Yr_+-k-4Yr_-,\\
 X+Yn+\tau x_+-YA-m-\tau x_-,\\
 2An-\tau-n^2-1,\quad \tau-m-g-1,\\
 W-n-w_n,\quad W-k-w_k,\quad \mathcal N(W+1,A,WZ).
\end{gathered}
\]

For positive integers \(n,k\), the retained standard Pell criterion says
that this polynomial has a natural auxiliary zero exactly when
\(m=n^k\). This is the literal 27-coordinate graph in the retained
`primitives.tex`, with local letters renamed. Its internal polynomial
has no variable exponent or opaque constant. The inherited foundational
input is the ordinary Pell-index criterion and classification of Pell
solutions, not an unprinted instruction tape.

## 4. The single proposed equation

With \((n_j,k_j',m_j)\) the ordered entries of \(\mathcal T\), put

\[
\boxed{\begin{aligned}
 \mathcal Q={}&\sum_{j=0}^{17}\mathcal P(n_j,k_j',m_j;\zeta_j)\\
 &+(x-F-1-(y+1)z_0)^2
   +(x-1-(1+(t+1)y)z_t)^2\\
 &+(Bz_B-C-F^2-1)^2
   +(L(C,a,b,c,d,S,T,u,v)-N\ell)^2\\
 &+(P_0-D_0(qw_0+B)-r_0)^2\\
 &+\sum_{j=1}^{10}(P_j-D_{\sigma_j}Nw_j-r_j)^2
   +\sum_{j=0}^{10}(D_{\sigma_j}-r_j-s_j-1)^2=0.
\end{aligned}}
\]

Every abbreviation in this display has been explicitly defined above.
Expanding fixed compositions, fixed sums and fixed products gives one
ordinary polynomial with integer coefficients. Its natural variables
are exactly the listed coordinates. To use positive unknowns instead,
replace each free coordinate, uniformly and independently, by a positive
coordinate minus one. This is an exact bijection between the domains and
adds neither a coordinate nor an equation. It is not a claim about the
existing fifteen-positive-variable circuit.

The hand census is 20 outer coordinates, 15 denominator/numerator
coordinates, 33 digit witnesses, and \(18\cdot27=486\) private power
coordinates: 554 total. There are \(18\cdot17=306\) power residuals,
four outer residuals, one carrier digit residual, ten fused range
residuals and eleven remainder bounds: 332 total. These are counts of
the displayed UNQUADRATICIZED family, not incoming finite-audit metrics.

## 5. Ordinary soundness argument and its proof boundary

The following is a proposed full ordinary reduction relative to two
identified inherited mathematical inputs: the positive-power graph in
section 3, and the exact C222/ZF/ZFC-refutation calibration. It has not
received independent review. It is not an accepted endpoint or new Lean
formalization. The later finite exports, contractions and coefficient
audits of the incoming quartic are not premises of this draft.

### 5.1 All power calls, growth, and the carrier digit

At a zero every squared residual is zero. The first call has positive
base \(2(t+1)\) and index \(t\ge16\), so
\(F=(2(t+1))^t>2^{80}\), in particular \(F>t!\),
\(F>(t+1)^t\), \(F\ge t\), and \(F\ge7\). The first endpoint gives
\(x\ge F+1\). In the last endpoint \(z_t=0\) would give \(x=1\),
so \(z_t\ge1\) and

\[
 x\ge2+(t+1)y,\qquad y\ge F+1.
\]

Thus the next two power calls have positive bases and indices, and give
\(N=B^x\), \(q=(BH)^x\). In particular \(q\ge2^x\), \(N\mid q\),
and \(B<q\). All four denominator indices are positive and at most
\(x\). All eleven numerator indices are positive: the nine actual
representatives were explicitly shifted by one and \(J\ge1\).
Consequently the power criterion applies to EVERY remaining call.
This recovery order makes no assumption about a binomial digit.

For \(0\le j\le t\),

\[
 \binom{F^2+t}{j}\le(F^2+t)^t
 \le(F^2+F)^t\le2^{t(F-1)}<2^x\le q.
\]

The elementary inequality \(F^2+F\le2^{F-1}\) starts at \(F=7\)
and follows by induction since
\(2(F^2+F)-((F+1)^2+(F+1))=(F-2)(F+1)\ge0\).
The natural remainder row gives \(0\le r_0<D_0=q^t\).
Uniqueness of the base-\(q\) remainder and \(0<B<q\) now identifies

\[
 B=\binom{F^2+t}{t}>F^2+1\ge2.
\]

There was no factorial-authenticity assumption. The strict inequality
uses \(t\ge2\): the binomial product has first factor \(F^2+1\)
and every subsequent factor is greater than one.

### 5.2 A hand majorant without an external circuit ledger

Here are enough explicit bounds to replace a hidden gate ledger. If
\(r\ge2,d\ge1\), and two nonnegative inputs are less than \(r^d\),
each of \(I,M,A,E\) is less than \(r^{2d+6}\). Indeed even
\(I+3<16r^{2d}\le r^{2d+4}\); the extra two powers are spare.
The same depth accounting includes \(\nu\), which is an \(I\) with
second input one. Starting with exponent one, depth \(s\) is bounded
by \(f^s(1)=7\cdot2^s-6\), for \(f(d)=2d+6\).

The eight axiom depths are respectively
\((4,3,3,3,3,5,4,3)\), with exponents
\((106,50,50,50,50,218,106,50)\), whose sum is 680.
The helper depths for the bundle are
\(R:7,Q:3,C_0:8,C_1:10,C_2:13,C_*:15,V:3,K:17,c_9:19\).
Thus its exponent is \(D=3,670,010\). These depths follow directly
from the printed formulas, counting each \(I,M,A,E,\nu\) as one
constructor and \(X\) as its three printed constructors.

For local bounded inputs put \(r=2+t+x+y+F\). All local inputs,
\(i\), and \(F\) are less than \(r\). The fourteen terms of \(J\)
are each less than \(r^D\), so
\(J<r^{D+4}<r^{2^{22}}\). Applying the identical argument at base
\(H\) gives \(J(a,b,c,d)<H^{2^{22}}\) for the actual representatives.

For completeness of the local bound, the truth factor is less than
\(r^4\); the eight axiom factors are less than
\(r^{2d_i+8}\); the guarded-bundle factor is less than
\(r^{2D+9}\); the modus-ponens factor is less than \(r^{30}\);
and the generalization factor is less than \(r^{24}\).
The guard square alone is less than \(r^{10}\).
The product is therefore less than
\(r^{2D+1491}\). Each beta-error square is less than \(r^{10}\),
so

\[
 0\le L<r^{7,341,512}<r^{2^{23}},\qquad
 0<J<r^{2^{22}}.
\]

These are generous bounds for precisely the complete polynomials printed
above. They do not quantify over an unnamed circuit. In particular the
guarded bundle has not been shortened to a weaker logical calculus.

The endpoint bounds give \(r<2x\). For \(x\ge2^{32}\),
\((2x)^{2^{23}}<2^x\): if \(2^a\le x<2^{a+1}\), then
\(a\ge32\), \(2^{23}(a+2)<2^a\le x\), with the first inequality
following from its case \(a=32\) and induction. Hence \(L<2^x\).
Also \(F>2^{22}\) gives \(x>2^{22}(t+1)\).

### 5.3 All ten range digits

Every ordinary upper representative is less than \(H\). Its coefficients
through any needed index \(k\le x\) are at most \(H^x<q\), since
\(q=B^xH^x\) and \(B\ge2\). The derived upper index obeys
\(J<H^{2^{22}}\), so its coefficients through \(t+1\) are also
less than \(H^x<q\). Zero coefficients above an upper index are included.

Thus every fused digit residual and its natural remainder bound says
exactly

\[
 N\mid\binom Ct,\quad
 N\mid\binom a{t+1},\binom b{t+1},\binom c{t+1},\binom d{t+1},
 \binom S{y+1},\binom T{y+1},\binom ux,\binom vx,
 \binom J{t+1}.
\]

The reason is \(N\mid q\): the quotient after division by the lower
power of \(q\) is the desired binomial plus a multiple of \(q\).
The remaining outer rows are \(B\mid C+F^2+1\) and
\(N\mid L(C,a,b,c,d,S,T,u,v)\).

### 5.4 Both directions of the binomial CRT step

For clarity, use the sufficient, weaker threshold \(F>t!\) already
proved, rather than assuming the new incoming numerical coefficients.
Put \(R=F^2>(t!)^2\). Each row \(i=1,\ldots,t\) has a full prime
power \(p^e\Vert B\) with \(p^e\mid R+i\) and \(p^e>t\).
To see this, \(R+i>(t!)^2\) gives a prime with
\(v=v_p(R+i)>2a\), where \(a=v_p(t!)\). Other factors have valuations
\(v_p(j-i)\), so
\(e=v+v_p((i-1)!(t-i)!)-a\), with \(a<e\le v\).
Since \(a\ge\lfloor\log_p t\rfloor\), this gives \(p^e>t\).

For EVERY prime power \(p^e\Vert B\), some compatible row satisfies
\(p^e\mid R+i\). Legendre's carry formula gives
\(e\le\max_i v_p(R+i)\): its terms are zero or one, and above
that maximum the interval has no multiple and all terms vanish.
This second fact is needed for completeness at all primes, not just
the selected row witnesses.

The elementary range fact
\(p^a\mid\binom nk\Rightarrow n\bmod p^a<k\)
for \(n\ge0,k,a\ge1\) follows from the same carry formula: if the
last \(k\) integers contain no multiple of \(p^a\), they contain no
multiple of a higher power, leaving at most \(a-1\) nonzero carry
terms. This uses no false converse of that range implication.

For soundness, choose the prime power for a row \(i\). The index range
gives \(C\equiv c_*\pmod{p^{xe}}\), \(0\le c_*<t\), while the raw
index congruence gives \(c_*\equiv i-1\pmod{p^e}\). Since \(p^e>t\),
\(c_*=i-1\). The eight other ranges give bounded local values
\(a,b,c,d\le t\), \(S,T\le y\), and \(u,v<x\), modulo \(p^{xe}\).
The local value of \(L\) is divisible by \(p^{xe}\ge2^x\) and lies
in \([0,2^x)\), so is zero. The derived \(J\) range, its nonnegative
local bound below \(2^x\), and polynomial congruence similarly give
the ACTUAL local label value \(J\le t\).

Conversely, for a valid bounded tuple at every row, choose a compatible
row for EVERY prime \(p\mid B\), and prescribe all nine representatives
modulo \(p^{2xe}\) by that tuple and its index. CRT gives positive
representatives in \([1,N^2]\). The raw index and local congruence follow.
For every range lower index \(k\le x\), the falling factorial contains
a factor divisible by \(p^{2xe}\); division by \(k!\) loses at most
\(v_p(k!)\le k-1<x\le xe\). Thus all ranges are divisible by
\(p^{xe}\), including the derived \(J\) range. If the upper argument
is below \(k\), the binomial is zero and needs no denominator argument.
Every prime has been covered, so all divisibilities hold modulo \(N\).

### 5.5 From local rows to an actual C222 refutation

The two beta equalities at neighboring rows give the same unique residue
in \([0,y]\) at their common modulus. They therefore glue the local
states into one path. The endpoints force its initial state \(F+1\)
and final state one. Every Horn factor is nonnegative; a vanishing
factor supplies one of the twelve displayed valid rules. The guarded
branch enforces both disequalities. All labels lie in \([0,t]\), by
the ACTUAL local \(J\) range.

The selected rule at each row has
\(T_i W_{v_i}=S_i W_{p_i}W_{q_i}\). Positive weights and the positive
initial state force all path states positive. Multiplication and
cancellation give

\[
 \prod_{i<t}W_{v_i}=(1+F)\prod_{i<t}W_{p_i}W_{q_i}.
\]

Remove label-zero unit factors. The two sides must have the same number
of nonunit factors: if the smaller count is \(r\le t\), the larger
side is at least \((F+1)^{r+1}\), while the smaller is at most
\(t^r(F+1)^r\), contradicting \(F+1>t^t\). The common count is at
most \(t\). Replacing \(F\) by an indeterminate gives two polynomials
whose coefficient sums are at most \((t+1)^t<F\). Their difference
cannot vanish at \(F\) unless it is identically zero: its lowest
nonzero coefficient would be a nonzero multiple of \(F\) of absolute
value less than \(F\). Unique factorization of the distinct linear
factors \(1+jz\) recovers conclusion-minus-premise multiplicities
\(\delta_{j1}\) for positive labels.

Take closure of truth under the finitely many selected rule instances.
If falsity is outside, every outside conclusion has an outside premise.
Summing their multiplicity balances outside the closure is then at
most zero, whereas the balance at falsity makes it one. Thus falsity
has a finite genuine C222 derivation. No acyclicity or coprimality of
the evaluated label weights was assumed.

## 6. Fresh completeness; no private witness division or rank transfer

Start from a finite C222 refutation, expand its proof DAG to a finite
proof tree, and choose \(t\ge16\) beyond its size, every schema parameter,
and every FULL label sum \(J\) of its parameter tuples and the truth
padding tuple. Such a \(t\) has the form \(16+h\). This choice precedes
the definition of \(F\). With \(F=(2(t+1))^t\), the pending-multiset
construction gives a positive state path from \(F+1\) to one satisfying
every local rule; pad to exactly \(t\) rows with truth rules.

Choose \(y\) to be a multiple of \(t!\), greater than \(F\), and at
least every state. Its \(t+1\) moduli \(1+(i+1)y\) are pairwise coprime:
a common prime divides an index difference at most \(t\), hence \(y\),
contradicting its being a divisor of either modulus. CRT supplies a
common \(x\), which can be increased by their product until all endpoint
and local quotients are nonnegative. Each local quotient is strictly
below \(x\), since its modulus is at least two. These choices give the
bounded local zeros used in section 5.4, and \(e=y-F-1\ge0\).

Set \(B=\binom{F^2+t}{t}\), \(N=B^x\), and choose the nine positive
representatives by the ALL-primes precision-\(2x\) CRT construction.
Their positive shifts give \(\xi_i\ge0\); \(\beta=B-1\ge0\).
The local polynomial is nonnegative on ALL natural inputs, so its
divisibility supplies \(\ell\ge0\). The raw index quotient \(z_B\)
is also natural. Form \(H\), then \(q=(BH)^x\), giving \(g=q-2\ge0\).
The coefficient bounds already proved apply to these fresh values.
Ordinary Euclidean division supplies all eleven natural digit quotients,
remainders and slacks. In the fused cases the quotient is a multiple
of \(N\), since both the intended binomial and \(q\) are.

Finally instantiate the standard positive-power existence direction
INDEPENDENTLY at the eighteen true triples. Each has positive base
and index. Every private 27-tuple is newly chosen; no common center,
odd semantic anchor, rank, native tiling, prime controller, or inherited
private witness is transferred or divided. This supplies a natural
zero of the displayed equation.

Thus the proposed ordinary argument has both existence implications,
relative to the two inherited foundational inputs identified in section 5.
Composing with the ordinary calibration
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` would give the desired
ZFC equivalence after this complete recipe and its proof have been reviewed.
No consistency assumption appears in either reduction. No new Lean proof,
checked proof closure, endpoint acceptance, or minimum claim is supplied.

## 7. Prior art, remaining obligations, and read scope

The factorial-free binomial-prime-power carrier and large-evaluation
label proof come from the new incoming Factorial Free submission. The
literal calculus, positive-power graph, beta path, range method, and
C222 calibration are retained earlier work, explicitly printed here
instead of being represented by a program index or coefficient table.
The new research choice is to spend independent natural witnesses and
degree for a short complete fixed-family presentation. It intentionally
does not adopt the incoming signed quartic compiler or its exact metrics.

Before any endpoint or page claim, the full proposal needs independent
ordinary reviews of the literal recipe, graph interface, hand majorant,
both CRT directions and logical calibration scope. A physical layout
would then need a separately authorized complete TeX/render/visual audit.
Neither a page count nor a complete-source byte saving follows merely
from displaying short residual families. The inherited Pell criterion
and C222 calibration remain named mathematical dependencies; their
transitive proof-assistant closures were not rebuilt here.

For this exploration the author read the incoming root README, the full
factorial-free ordinary proof note, all 843 lines of `report/main.tex`,
the full literal `calculus.tex`, the full `primitives.tex`, the full
`INHERITED_shared_powers.md`, `ORIENTATION_FIRST_PROOF.md`, direct `PROOF.md`,
the full literal `direct_calculus.py`, and all 112 lines of
`build_factorial_free.py` as INERT TEXT. The first 180 lines of retained
`direct_arithmetic.tex` were reread separately after an earlier combined
tool output truncated that member. No full-read claim is made for the
unread remainder of that file, the incoming numerical audit artifacts,
the Shared Factorial Error proof, or the inherited Lean closure.

The Shared Factorial Error root README was also read as comparison only.
Its reported 240-integer-variable endpoint and the Factorial Free
submission's reported 242/241-integer-variable quartics are unverified
reported metrics here. Neither is used as a correctness premise.
The current maintained page and every accepted or held candidate,
probe, source, review, and Lean file were left unchanged.

Exact archive/member authentication is recorded in `SOURCE_PINS.md`.
Only generic archive membership, plaintext streaming, hashing, file
reading and author Markdown writing were used. There was no extraction,
import, application, AST, mathematical helper, polynomial expansion,
prime/residue/order evaluation, compilation, TeX/PDF production, or commit.
