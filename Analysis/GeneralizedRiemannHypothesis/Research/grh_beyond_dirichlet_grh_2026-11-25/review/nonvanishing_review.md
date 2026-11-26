# Independent review: explicit bounded torsion nonvanishing

**Verdict: valid.** The proposed theorem, including the dimension-independent bound, follows by an elementary integral division argument. It needs no RH or GRH input. The bound is sharp in the one-power case with the stated radial restriction. The full proof below avoids assuming Noetherianity of the valuation ring of C_p.

## 1. Statement

Fix a prime p, normalize v(p)=1 on C_p, and set v(0)=+infinity. Write O for its valuation ring. Let r>0 be rational, let B>=0 be real, and let F_1,...,F_n belong to O[[T_1,...,T_s]]. For every i suppose there is a witness x_i=(x_i1,...,x_is) in C_p^s with

- v(x_ia)>=r for all a;
- sum_i v(F_i(x_i))<=B<infinity.

All series evaluations converge. Put

\[
\rho_h=\frac1{\varphi(p^h)},\qquad
h_*(r)=\min\{h\ge1:\rho_h\le r\},\qquad
H=h_*(r)+\lfloor B\rfloor.
\]

Then one can choose roots of unity zeta_a, each of order p^{h_a} with

\[
h_*(r)\le h_a\le H,
\]

such that

\[
F_i(\zeta_1-1,\ldots,\zeta_s-1)\ne0\quad\text{for every }i.
\]

Thus the same tuple works for the entire finite family. In particular v(zeta_a-1)<=r and the orders divide p^H. H is independent of the number of variables, polynomial degrees or power-series supports; the aggregate witness budget B records the dependence on the family.

The case s=0 is immediate. The case n=0 is vacuous and any tuple in the nonempty grid works. Below assume s,n>=1.

## 2. Gauss valuation for integral formal series

For an integral series F=sum_alpha a_alpha T^alpha define

\[
w_r(F)=\min_\alpha\{v(a_\alpha)+r|\alpha|\},\qquad w_r(0)=+\infty.
\]

The minimum exists for nonzero F: integrality implies all sufficiently large total degrees have weighted valuation exceeding any fixed nonzero coefficient's weighted valuation. Since r>0, evaluation on v(x_a)>=r converges and

\[
v(F(x))\ge w_r(F).
\]

Moreover

\[
w_r(FG)=w_r(F)+w_r(G).
\]

One proof chooses c in C_p with v(c)=r, scales T_a=cU_a, divides each nonzero series by a coefficient of its minimal valuation, and reduces modulo the maximal ideal. Only finitely many coefficients survive this reduction, giving nonzero polynomials over the residue field. Their product is nonzero because that polynomial ring is an integral domain. This proves the equality without any convergence issue at the unit boundary.

Consequently for F=product_i F_i,

\[
w_r(F)=\sum_i w_r(F_i)\le\sum_i v(F_i(x_i))\le B.
\]

Different witnesses x_i are harmless: they are used only to bound the separate Gauss minima before multiplication.

## 3. The cyclotomic grid

Let L=H-h_*(r)+1=floor(B)+1>B and define

\[
g(T)=\prod_{h=h_*(r)}^H\Phi_{p^h}(1+T).
\]

Let d=deg(g), and let A be its roots in C_p. They are exactly the numbers zeta-1 for primitive p^h-th roots zeta in the displayed interval of h. The d roots are distinct. Each has positive valuation, at most r.

For h>=1, Phi_{p^h}(1+T) is monic, has constant coefficient p, and reduces modulo p to T^{phi(p^h)}. Since r phi(p^h)>=1 on this interval, its weighted Gauss valuation is exactly 1: all lower coefficients have valuation at least 1, the leading weighted valuation is at least 1, and the constant coefficient attains 1. Thus

\[
w_r(g)=L.
\]

Also g=T^d+a(T), where deg(a)<d and every coefficient of a is divisible by p. This last uniform divisibility makes the integral division argument particularly simple.

## 4. Integral division, proved by contraction

Let R_s=O[[T_1,...,T_s]] with the supremum norm on coefficients. It is a complete nonarchimedean normed ring: it is the closed unit ball in the complete space of bounded C_p-valued coefficient sequences. Formal multiplication is bounded, because the coefficient of any monomial is a finite sum.

Fix one variable T_j. Let S_d discard terms of T_j-degree less than d and shift the remaining exponents down by d. This operator has norm at most 1. Multiplication by a(T_j) has norm at most p^{-1}, so

\[
E=S_d\circ M_{a(T_j)}
\]

has norm at most p^{-1}. The series

\[
Q=\sum_{n\ge0}(-E)^nS_dF
\]

therefore converges uniformly coefficientwise to an integral formal series, and satisfies

\[
Q+S_d(a(T_j)Q)=S_dF.
\]

It follows that

\[
F=g(T_j)Q+R,\qquad \deg_{T_j}(R)<d.
\]

This proof works over O_Cp despite its non-Noetherianity. If F already has bounded degree in some other variables, so do Q and R, since the operations involve T_j only.

Repeat the division successively in T_1,...,T_s. The result is

\[
F=\sum_{j=1}^s g(T_j)Q_j+R,
\]

with every Q_j integral and R a polynomial satisfying deg_{T_j}(R)<d for each j.

## 5. Vanishing ideal of the grid and the contradiction

Suppose all points in A^s make at least one F_i vanish. Then F=product_i F_i vanishes on A^s. Because every coordinate of every grid point has positive valuation, all Q_j evaluations converge and the division identity can be evaluated. Hence R vanishes on A^s.

A polynomial of degree less than d in each variable which vanishes on the d-by-...-by-d product of d distinct points is zero. This follows by repeated use of the univariate root bound, or tensor-product Lagrange interpolation. Thus R=0.

Since Q_j is integral, w_r(Q_j)>=0. The ultrametric inequality and w_r(g(T_j))=L give

\[
w_r(F)=w_r\left(\sum_jg(T_j)Q_j\right)\ge L>B,
\]

contradicting Section 2. Therefore some grid point makes every F_i nonzero.

## 6. Sharpness for one power

Let k=floor B. If k>=1, form in one variable

\[
F(T)=\prod_{h=h_*(r)}^{h_*(r)+k-1}\Phi_{p^h}(1+T).
\]

At the witness x=0, v(F(0))=k<=B. Yet F vanishes at every permitted root zeta-1 of order dividing p^{h_*(r)+k-1}, with v(zeta-1)<=r. Hence the exponent H=h_*(r)+floor B cannot be lowered in general. If k=0, h_*(r) is already the least available torsion level under the radial restriction. This is exact sharpness for the universal nonvanishing statement with m=1; no optimality for the power-orbit variant below is claimed.

## 7. The first m powers simultaneously

For m>=1 define

\[
G_{i,j}(T_1,...,T_s)
 =F_i((1+T_1)^j-1,...,(1+T_s)^j-1),\qquad1\le j\le m.
\]

Formal composition is valid because each substituted polynomial has constant coefficient zero; all coefficients remain integral.

For every x with v(x)>=r, there exists y with

\[
(1+y)^j-1=x,\qquad v(y)\ge r/j\ge r/m.
\]

For x=0 choose y=0. Otherwise the monic polynomial (1+Y)^j-1-x has j integral roots (with multiplicities), whose valuation sum is v(x); at least one has valuation >=v(x)/j. Apply this coordinatewise, separately for each (i,j). The resulting witness y_{i,j} satisfies

\[
v(G_{i,j}(y_{i,j}))=v(F_i(x_i)).
\]

Their aggregate budget is at most mB. The base theorem, with radius r/m, therefore supplies roots zeta_a of order dividing p^H with

\[
H=h_*(r/m)+\lfloor mB\rfloor,
\]

such that

\[
F_i(\zeta_1^j-1,...,\zeta_s^j-1)\ne0
\quad\text{for all }i,\ 1\le j\le m.
\]

The original roots satisfy v(zeta_a-1)<=r/m. A power zeta_a^j can equal 1; this does not invalidate convergence or the assertion. If such a point would force one of the listed F_i to vanish, the common nonvanishing condition automatically excludes it.

## 8. Matrix and Fitting implications

For a finite family of matrices over O_Cp[[T]], choose one nonzero minor at each desired rank and a witness where it is nonzero. Use its finite valuation as the corresponding budget term. The nonvanishing theorem yields one bounded torsion tuple preserving all these rank lower bounds, and simultaneously the first m powers if desired. If the chosen rank is each matrix's generic rank, all larger minors are identically zero, so the specialization has exactly the generic rank.

For the stronger quantitative theorem from the upstream polynomial lemma, one chosen k-minor per matrix and baseline is sufficient. If

\[
\mu_{A,k}(x)=\min_{I,J,|I|=|J|=k}v(\det A_{I,J}(x))<\infty,
\]

choose a minor attaining this minimum and apply the same-H power-series extension to it. This gives

\[
\mu_{A,k}(\zeta^j-1)\le\mu_{A,k}(x_{A,k})+\varepsilon
\]

simultaneously. These are bounds on cumulative smallest Smith valuations/determinantal-ideal valuations, not on each individual invariant factor. No equality with the baseline is implied. Only finitely presented explicit matrices are being discussed; application to actual Selmer or Iwasawa modules needs a separate arithmetic identification.

## 9. Claim boundaries

- The nonvanishing bound is an independent paper proof, inspired by the source's torsion-grid specialization mechanism. It does not require the full source theorem or its harmonic-order bound.
- Nonvanishing is much weaker than retaining valuations within an arbitrarily prescribed epsilon. The explicit linear exponent H should not be attached to the stronger quantitative statement without an additional argument.
- No assertion of literature priority follows from the absence of the result in the five prior ProveIt reports. Related torsion specialization and p-adic analytic zero-set literature should be cited and compared.
- C_p coefficients and arbitrary integral formal series are allowed because all evaluations have strictly positive coordinate valuation, and because division converges in the bounded coefficient supremum norm. Neither claim would follow for unrestricted evaluation at torsion units themselves.
