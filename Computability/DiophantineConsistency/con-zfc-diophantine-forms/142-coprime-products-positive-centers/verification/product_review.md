# Independent review of the preferred compact product constructions

Review date: 25 October 2026. Parent snapshot:
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`.

**Result: all three local compression theorems pass this independent
review.** No remaining soundness, integrality, positivity, or completion
gap was found. The review also corrected the provisional degree 435 of
the anchored thirteen-variable graph to its exact degree **433**.

| Preferred graph | Positive unknowns | Binary operations | Exact degree |
|---|---:|---:|---:|
| `equation_14_raw.json` (root-saturated) | 14 | 70 | 189 |
| `equation_14_reduced.json` | 14 | 71 | 157 |
| `equation_13_anchored.json` | 13 | 72 | 433 |

The files are in the portable `products` component. This is a review of
ordinary mathematics formalizable in ZFC. It is not a new proof term
checked by a proof-assistant kernel. The fixed-instance calibration to
refutations remains the inherited P66 calibration. The initially
reviewed points 14/70/233 and 13/72/465 are superseded by the first and
third rows above.

## 1. Scope of the inherited interface

The constructions retain the exact four fixed ports `beta,K0,MC,MF` of the
indexed943/radix67 P66 instance. In particular, `MF` is the already
shifted mask. The consistency theorem does not replace these constants
by arbitrary parameters.

Write the common outer quantities as in the product proofs. To avoid
confusing the first radicand with the main Pell base, use

\[
 A=1+\ell(\ell+k),\qquad a_*=a+2,\qquad
 \Delta=a_*^2-1=a^2+4a+3.
\]

For positive input coordinates and the actual positive fixed tuple,
\(A>1\), \(c>1\), and \(\Delta>0\). The congruence
\(\Delta\equiv0\text{ or }3\pmod4\) holds identically. The common main
factor is \(N_1=D^2-\Delta c^2\), where \(D>0\); the other outer
factors are \(N_k,N_t\).

The normalized P66 equation is a product of six integer factors equal
to one. A new positive zero maps to a positive zero of that exact
equation without needing to decide the individual signs of
\(N_k,N_t\), provided their product is one. The inherited source
soundness theorem then applies.

Conversely, the source supplies a canonical completion of each
refutation with

\[
 N_1=N_k=N_t=1,\quad \tau^2=A,\quad
 c=\psi_{a_*}(R),\quad R>0,\quad R\equiv3\pmod4,
\]

and a positive strong Pell pair

\[
 f_0^2-\Delta i_0^2c^4=1.
\]

The variables of this strong pair and its auxiliary completion are
private: replacing them does not change the outer quantities. The
completeness maps below use these canonical source witnesses. They do
not claim an arbitrary pointwise division map from every P66 zero into
a new zero.

## 2. The product-square extraction lemma

Suppose \(G,B,t\) are positive integers and \(C\) is an integer with

\[
 Bt^2=GC,\qquad \gcd(G,B)=\gcd(G,C)=1.
\]

For every prime \(p\mid G\), valuation in the equality gives

\[
 2v_p(t)=v_p(G).
\]

Thus \(G=g^2\) and \(g\mid t\). In the applications,
\(B=Q-1>0\), \(C=QV^2-1\). If \(G\mid Q\), the two coprimalities
hold immediately, because both \(B,C\) are \(-1\) modulo \(G\).
The anchored thirteen-variable case proves them separately; it does
**not** assert \(G\mid Q\).

The argument makes no positivity assumption on \(V\). The equality
itself forces \(C>0\), so \(V=0\) cannot occur. The valuation argument
is an unbounded arithmetic proof, not an inference from finite tests.

## 3. Root-saturated fourteen-variable soundness

Set

\[
 I=ic^2,\quad W=\Delta A I^2,\quad Q=\Delta W,
\]
\[
 N_s=f^2-W,\quad V=f^2(cT-R)-c,
\]
\[
 E=Q(t^2-AV^2)-t^2+A
   =(Q-1)t^2-A(QV^2-1).
\]

The new equation is

\[
 N_1N_kN_t(3E+1)N_s=1.
\]

Every factor is an integer unit. Since \(3E+1\equiv1\pmod3\), this
factor cannot be \(-1\), and hence \(E=0\). Also \(N_1\ne-1\):
modulo four, \(x^2-\Delta y^2\) is a square or a sum of two squares,
and never three. Therefore \(N_1=1\).

At this point the sign of \(N_s\) has deliberately not been determined.
The actual polynomial \(Q=\Delta^2AI^2\) is positive, greater than
one, and divisible by \(A\). The extraction lemma with \(G=A\)
gives \(A=\tau^2\) and \(\tau\mid t\). Only now use

\[
 N_s=f^2-\Delta(\tau I)^2
\]

to exclude its negative unit by the same modulo-four argument. Thus
\(N_s=1\) and \(N_kN_t=1\). Restore

\[
 i_{\rm old}=\tau i,\quad S=\Delta\tau I,\quad y=t/\tau.
\]

These are positive integers. Moreover, \(Q=S^2\), and division of the
product equation by \(A\) gives

\[
 S^2V^2-(S^2-1)y^2=1.
\]

Consequently the first, main, auxiliary, and normalized strong parent
factors are one, and the other two have product one. This is a positive
zero of the exact P66 polynomial. The order of recovery is essential:
squarehood of \(A\) is proved before excluding \(N_s=-1\).

## 4. Reduced fourteen-variable soundness

This graph retains the older multiplier placement

\[
 I=Aic^2,\quad W=\Delta I^2,\quad
 N_s=f^2-W,\quad Q=\Delta(f^2-1).
\]

The other formulas and final product are as in Section 3. This time
\(N_s=-1\) is excluded directly by its displayed quadratic norm.
The unit argument gives

\[
 N_1=N_s=1,\quad E=0,\quad N_kN_t=1.
\]

Only after recovering \(N_s=1\) infer

\[
 Q=\Delta(f^2-1)=\Delta^2I^2=S^2,
 \qquad S=\Delta I.
\]

Now \(A\mid S\), so the extraction lemma gives \(A=\tau^2\),
\(\tau\mid t\), and the auxiliary norm as before. Restore
\(i_{\rm old}=Ai\) and \(y=t/\tau\). This proves soundness of the
degree-157 graph without assuming its strong norm prematurely.

## 5. Anchored thirteen-variable soundness

Define

\[
 m=a_*Di,\quad I=mc^2,\quad W=\Delta AI^2,\quad
 F_2=1+W,\quad Q=\Delta W,\quad G=AF_2,
\]
\[
 V=F_2(cT-R)-c,\qquad
 E=(Q-1)t^2-G(QV^2-1).
\]

The new equation is

\[
 N_1N_kN_t(3E+1)=1.
\]

The unit argument independently recovers \(N_1=1\), \(E=0\), and
\(N_kN_t=1\). Put \(B=Q-1\), \(C=QV^2-1\). Since
\(A\mid Q\) and \(F_2\equiv1\pmod A\),

\[
 \gcd(A,B)=\gcd(A,C)=\gcd(A,F_2)=1.
\]

For the other part of \(G\), use the exact congruences

\[
 B=\Delta F_2-(\Delta+1)
   \equiv-a_*^2\pmod{F_2},
\]
\[
 C\equiv-\Delta c^2-1=-D^2\pmod{F_2}.
\]

The last equality uses the already established main norm
\(D^2-\Delta c^2=1\). Because \(I=a_*Di c^2\),

\[
 F_2=1+\Delta AI^2\equiv1\pmod{a_*D}.
\]

Thus \(F_2\) is relatively prime to \(a_*D\), and consequently to
both \(B\) and \(C\). The extraction lemma now applies to the full
product \(G=AF_2\). It gives \(G=g^2\) and \(g\mid t\). Since
\(\gcd(A,F_2)=1\), recover positive integers

\[
 A=\tau^2,\quad F_2=f^2,\quad g=\tau f.
\]

Restore

\[
 i_{\rm old}=\tau m=\tau a_*Di,\quad
 S=\Delta\tau I,\quad y=t/(\tau f).
\]

The last quotient is integral by the extraction lemma. The exact
identities

\[
 f^2-\Delta i_{\rm old}^2c^4=1,\qquad
 Q=S^2,\qquad V=f^2(cT-R)-c
\]

give the strong and auxiliary parent factors one. The first and main
factors are already one, and \(N_kN_t=1\). This reconstructs all three
deleted roots and a positive zero of P66.

## 6. Completeness and the fresh auxiliary completion

The necessary divisibility can be imposed without changing any outer
coordinate. Given a positive strong pair \(f_0,i_0\), the matrix

\[
 M_0=\begin{pmatrix}f_0&f_0^2-1\\1&f_0\end{pmatrix}
\]

has determinant one. Modulo any positive integer \(d\), it lies in a
finite group of at most \(d^4\) matrices. Some positive power is the
identity. Its lower-left entry is \(\psi_{f_0}(n)\), so

\[
 f_1=\chi_{f_0}(n),\qquad i_1=i_0\psi_{f_0}(n)
\]

is a positive strong pair with \(d\mid i_1\). Taking
\(n=(d^4)!\) suffices. A smaller positive matrix period also suffices.
No factorial appears in the new polynomial.

Use the following modulus and new coordinate:

| Graph | Divisibility modulus \(d\) | New input \(i\) |
|---|---|---|
| Root-saturated P14 | \(\tau\) | \(i_1/\tau\) |
| Reduced P14 | \(A\) | \(i_1/A\) |
| Anchored P13 | \(\tau a_*D\) | \(i_1/(\tau a_*D)\) |

All quotients are positive integers. Substitution gives the exact
strong ordinate \(i_1c^2\) after the soundness restoration. For P13,
in particular, \(W=f_1^2-1\), \(F_2=f_1^2\), and
\(G=\tau^2f_1^2\).

For this chosen final strong pair, construct the auxiliary coordinates
afresh. Put \(S=\Delta i_1c^2\). The canonical source facts
\(c=\psi_{a_*}(R)\), \(R\equiv3\pmod4\), and the exact
integer-polynomial identities in P66 Section 4 imply

\[
 V_*={\chi_S(R)\over S}\in\mathbb Z_{>0},\qquad
 y_*=\psi_S(R)>0,
\]
\[
 V_*\equiv-c\pmod{f_1^2},\qquad
 V_*\equiv-R\pmod c.
\]

The strong norm gives \(f_1^2\equiv1\pmod c\) and
\(\gcd(f_1,c)=1\). Therefore

\[
 T_*={V_*+c+Rf_1^2\over cf_1^2}
\]

is a positive integer: its numerator is divisible by each of the two
coprime denominator factors, and all three summands are positive. This
gives the required expression \(V_*=f_1^2(cT_*-R)-c\) and the auxiliary
Pell norm one. Use \(t=\tau y_*\) in either P14 graph and
\(t=\tau f_1y_*\) in P13. All new product factors have value one.
No old auxiliary coordinate is assumed to remain divisible or unchanged.

Composition with the inherited fixed-instance calibration proves in
ZFC that absence of positive integer zeros of each preferred graph is
equivalent to \(\operatorname{Con}(\mathrm{ZFC})\). No consistency
assumption is used to prove the equivalence.

## 7. Independent exact degree calculation

Give each quantified coordinate degree one and each fixed port degree
zero. Define the homogeneous leading parts

\[
 q_0=\beta J,\quad k_0=\eta+\zeta,\quad
 e_0=wsq_0^4,\quad c_0=k_0sq_0^3,\quad
 A_0=(ws^2k_0q_0^7)^2,
\]
\[
 L_t=w(q_0-F-\alpha)-zq_0.
\]

The top parts of \(N_k,N_t\) are \(-he_0,L_t\). For \(N_1\),
the apparent degree-22 terms cancel. With \(Z=X+\gamma H\),

\[
 N_1=2acZ+Z^2-Hc^2
\]

shows its degree is 18, with top part \(8\gamma e_0^2c_0\). The main
Pell base has degree 6 and leading part \(e_0\); \(D\) has degree
11 and leading part \(e_0c_0\).

For root-saturated P14 the successive degrees of
\(I,W,N_s,Q,V,E\) are \(11,56,56,68,8,106\). Its degree-189 top part is

\[
 -24\gamma h i^4A_0^3e_0^9c_0^{11}f^4T^2L_t.
\]

For reduced P14 the degrees of \(I,W,N_s,Q,V,E\) are
\(33,78,78,14,8,52\). Its degree-157 top part is

\[
 -24\gamma h i^2A_0^3e_0^7c_0^7f^6T^2L_t.
\]

For anchored P13 the successive degrees of
\(m,I,W,F_2,Q,G,V,E\) are
\(18,28,90,90,102,112,96,406\). Its degree-433 top part is

\[
 24\gamma h i^8A_0^5e_0^{29}c_0^{27}T^2L_t.
\]

Selecting the \(-zq_0\) summand of \(L_t\) and the pure \(\eta\)
summand of the powers of \(k_0\) gives these explicit nonzero terms:

| Graph | Monomial | Coefficient |
|---|---|---|
| Root-saturated P14 | \(J^{112}w^{15}s^{32}\eta^{17}i^4f^4T^2\gamma hz\) | \(+24\beta^{112}\) |
| Reduced P14 | \(J^{92}w^{13}s^{26}\eta^{13}i^2f^6T^2\gamma hz\) | \(+24\beta^{92}\) |
| Anchored P13 | \(J^{268}w^{39}s^{76}\eta^{37}i^8T^2\gamma hz\) | \(-24\beta^{268}\) |

They prove that the upper bounds are attained for the actual fixed
\(\beta>0\). No complete multivariate expansion is needed.

## 8. Literal-graph and reporting checks

An independent standard-library walk of the final JSON graphs checks
the coordinate counts, unique and correctly ordered gate bindings,
permitted arithmetic operations, and reachability of every input, fixed
port, and gate from the output. The operation breakdowns are

```
P14 root-saturated: 40 multiplications + 17 additions + 13 subtractions = 70
P14 reduced:       40 multiplications + 17 additions + 14 subtractions = 71
P13 anchored:      41 multiplications + 19 additions + 12 subtractions = 72
```

The final P13 literal graph was read against the construction above.
In particular, its `mult`, `I`, `S0`, `W0`, `W`, `f2`, `Q`, `G`, and
`Eprod` gates have the exact meanings used in the proof. The temporary
gate `S0` is \(\Delta mc^2\); it is not prematurely asserted to be the
final strong Pell base \(\Delta\tau mc^2\).

The exact final graph digests are recorded in
`product_review_checks.json`:

```
equation_14_raw.json
3f1912e0f37fdf8df116698e5a4ae5718d1c743fb7f35239ceb64e6ea97a65db
equation_14_reduced.json
4793bc610935d3f96b664658d34ec1bc1a3c6a9c7c77d0e2515e8e098daa42ff
equation_13_anchored.json
84b307586101c5deb9535046301e94ef769e915f5ad25339d1bd956772e0ad5d
```

Independent degree propagation, with the proved degree-18 main-norm
cancellation, gives 189, 157, and 433. The displayed leading monomials
prove equality. This check caught the provisional 435 overstatement
before publication.

Credit for the general coprime-product and cofinal Pell ideas should
follow the incoming manuscripts identified in the product proof. The
new claim is the dependency-ordered use of these identities in the
exact P66 graphs and their measured improvements, rather than global
novelty for the general identities or an absolute smallest equation.
