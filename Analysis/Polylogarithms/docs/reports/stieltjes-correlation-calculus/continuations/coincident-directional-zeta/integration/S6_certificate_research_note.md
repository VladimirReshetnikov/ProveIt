# A focused exact-certificate target for S6

## Scope and pinned sources

This is a targeted certificate audit at ProveIt revision
`dcd95baeb7c0e914b138bddef6829c5b1d52b726`. It proves the explicit single-by-double identity in the accompanying `S6_depth_three_bridge.tex`, normalizes the existing conjecture into a compact exact word target, and identifies a finite next certificate problem. It does **not** prove the conjecture, perform a large relation search, or claim that the target lies outside a larger algebra.

Paths below are relative to the pinned repository. The principal sources are:

1. `Analysis/Polylogarithms/docs/manuscript/chapters/04-cyclotomic-quotients.tex`: the presentation in `cycloquot:eq:formal-stuffle` and `cycloquot:eq:formal-shuffle`; `cycloquot:thm:level-four`; the separator `cycloquot:eq:separating`; the exact basket change `s6change:eq:identity`; and the frozen conjecture `cycloquot:conj:S6` / `cycloquot:eq:S6`.
2. `Analysis/Polylogarithms/docs/manuscript/chapters/04-S4-proof.tex`: word convention `s4proof:eq:s4-word-convention`, convergent involution `s4proof:eq:s4-convergent-duality`, seed `s4proof:eq:s4-duality-seed`, row schemas `s4proof:eq:s4-ds-row` and `s4proof:eq:s4-distribution-row`, and equality `s4proof:eq:s4-certificate-equality`.
3. The certificate actually corresponding to that manuscript equality is `Analysis/Polylogarithms/docs/reports/rigidity-and-reflected-moments/results/S4_certificate.json`, replayed by the adjacent `code/verify_s4.py`. It has 713 convergent double-shuffle rows, 181 single-divergence double-shuffle rows, 17 lifted convergent distribution rows, and one separate octahedral seed.
4. A newer, different exact S4 certificate is `Analysis/Polylogarithms/docs/reports/cayley-s4-continuation/data/S4_certificate.json`, replayed by `code/verify_s4.py` and independently by `code/verify_s4_independent.py`; `code/word_algebra.py` specifies its letter convention. It has 852 double-shuffle rows (729 convergent and 123 single-divergence) and one Cayley row, with no distribution rows. Its Cayley word is `[-1,-1,-1,1,1]`. Here `-1` encodes `dt/t` and `j` encodes `i^j dt/(1-i^j t)`. Thus this is the word of `g_{4,1}`, not the older manuscript seed `g_{1,4}`. The alphabets are equivalent, but the stored integer encodings and forms must not be interchanged.

The second S4 certificate demonstrates that lifted distribution is optional in at least one successful S4 route. Neither certificate, by itself, proves that its selected octahedral seed is necessary among all possible larger relation families.

Both pinned replay programs were executed during this audit and returned exact zero residuals. Their distinct row counts above were checked from the replay output as well as the certificate descriptors.

## 1. Exact primitive word target

The frozen basket is

\[
(S_6,g_{6,1},g_{4,3},g_{2,5},\pi^7,
 G\zeta(5),\beta(4)\zeta(3),\beta(6)\log2)
\]

with integer vector

\[
(485683200,-665395200,-36864000,401080320,
-258247,11750400,109347840,971366400).
\]

Write its linear combination as \(R_6\). Use the exact identities

\[
S_6=g_{6,1}+K_{6,1},\quad
K_{6,1}=\operatorname{Im}\Li_{6,1}(i,-1),\quad
\beta(7)=\frac{61\pi^7}{184320},\quad \Li_1(-1)=-\log2.
\]

Then \(F_7=(61/46080)R_6\) is the following primitive integer word target:

\[
\begin{aligned}
F_7={}&642940K_{6,1}-237900g_{6,1}-48800g_{4,3}
       +530944g_{2,5}-1032988\operatorname{Im}\Li_7(i)\\
&+15555\operatorname{Im}[\Li_2(i)\Li_5(1)]
 +144753\operatorname{Im}[\Li_4(i)\Li_3(1)]\\
&-1285880\operatorname{Im}[\Li_6(i)\Li_1(-1)].
\end{aligned}
\]

Its coefficients have gcd one. Expand all three products by integral shuffle before constructing a formal word vector. The equality \(F_7=0\) is exactly the existing conjecture; it is not a newly fitted relation. The script `verify_s6_target.py` checks the rational conversion without evaluating any period.

For an alternative target eliminating the logarithmic product, the manuscript's already-proved all-exponent endpoint theorem specializes to

\[
K_{6,1}=A_{1,6}+\frac{4499\pi^7}{3870720}
-\frac{15}{16}G\zeta(5)-\frac34\beta(4)\zeta(3)
-2\beta(6)\log2,
\quad A_{1,6}=\operatorname{Im}\Li_{1,6}(i,i).
\]

Substitution cancels the logarithmic term in the conjecture exactly. This is a useful alternative search target, but is a specialization of an existing theorem, not a proof of the remaining reduction.

## 2. What the separating functional proves

At weight seven set \(A(X,Y)=(Y-X)^5\), \(K(X,Y)=X^5\), and \(V(X,Y)=-Y^5\) in the pinned theorem. The resulting functional has

\[
\ell(A_{a,7-a})=(1,-5,10,-10,5,-1)_a,
\qquad \ell(K_{6,1})=1,
\qquad \ell(\operatorname{Im}\Li_{1,6}(-1,i))=-1.
\]

All other entries vanish, except the conjugate entries with opposite signs. Singles, products of two singles, and the selected g-family belong to the background and are killed. The functional annihilates all defining single-by-single shuffle/stuffle rows, including the stated regularized rows. It gives

\[
\ell(R_6)=485683200,\qquad \ell(F_7)=642940.
\]

Therefore neither target follows from **that specified presentation**. This statement is an exact proof-strategy obstruction. It is not a statement about linear independence of the evaluated constants, the full cyclotomic double-shuffle algebra, or an arbitrary extension of the functional to higher depths. In particular, the proof does not distinguish which of the larger relation families is indispensable.

## 3. A specific admissible row outside the presentation

Consider the product

\[
P=\Li_1(i)\Li_{5,1}(1,-1).
\]

Its seven integral shuffles and five series stuffles give

\[
\begin{aligned}
K_{6,1}+\operatorname{Im}\Li_{5,2}(1,-i)
={}&\sum_{a=1}^{5}\operatorname{Im}\Li_{a,6-a,1}(i,-i,-1)\\
&+\operatorname{Im}\Li_{5,1,1}(1,i,i)
 +\operatorname{Im}\Li_{5,1,1}(1,-1,-i)\\
&-\operatorname{Im}\Li_{1,5,1}(i,1,-1)
 -\operatorname{Im}\Li_{5,1,1}(1,i,-1)\\
&-\operatorname{Im}\Li_{5,1,1}(1,-1,i).
\end{aligned}
\]

Every term converges. There is no divergent factor or regularization correction. A proof with explicit forms and color conventions is in `S6_depth_three_bridge.tex`.

Extend the old separator to the free word space by zero on all depth-three symbols. The displayed shuffle-minus-stuffle row then has value \(-1\): the depth-two collision \(-K_{6,1}\) contributes \(-1\), while \(-\operatorname{Im}\Li_{5,2}(1,-i)\) contributes zero. Thus this naive extension fails even a single, elementary, convergent single-by-double row. This gives a concrete reason that the old separator must not be described as an obstruction to all double shuffle.

This row supplies an exact depth-three reduction of the mixed target. It does not finish the conjecture: one must still eliminate the resulting depth-three combination to the frozen basket. It also does not show that no other extension of the separator could annihilate all larger rows.

More explicitly, let \(Q_7\) be the ten-term right side above. The ordinary stuffle of \(\Li_5(1)\Li_2(-i)\) gives

\[
\operatorname{Im}\Li_{5,2}(1,-i)=g_{2,5}+\beta(7)-G\zeta(5).
\]

Consequently there is an exact reduction

\[
S_6=g_{6,1}-g_{2,5}+G\zeta(5)-\beta(7)+Q_7.
\]

Thus the missing reduction can be stated with complete precision: the frozen conjecture is equivalent to the vanishing of

\[
\begin{aligned}
642940Q_7-237900g_{6,1}-48800g_{4,3}-111996g_{2,5}
-1675928\beta(7)\\
{}+658495G\zeta(5)+144753\beta(4)\zeta(3)
+1285880\beta(6)\log2.
\end{aligned}
\]

This equality is an exact restatement of the still-open target, not an additional conjecture chosen by a numerical fit.

## 4. A finite and explicit next certificate problem

Use the geometric alphabet \(\{0,1,-1,i,-i\}\) with \(\omega_a=dt/(t-a)\), outer-letter-first integration, and the signed word convention in `s4proof:eq:s4-word-convention`. Include all length-seven convergent words (first letter not 1, last letter not 0), at every depth. Before further relations there are

\[
16\cdot5^5=50000
\]

such words, of which \(4\cdot3^5=972\) are fixed by conjugation. Hence formal imaginary projection leaves \((50000-972)/2=24514\) coordinates. This is a count of free coordinates, not a dimension of periods or of the relation quotient. For comparison the analogous weight-five count is 946.

Start with the following precisely delimited relation schemas:

1. Shuffle-minus-stuffle rows of all admissible factors of total weight seven, allowing arbitrary factor depth, including the single-by-double example above.
2. Rows with one factor \(\Li_1(1)\) and the other admissible of weight six. Compare the shuffle and stuffle regularizations with the formal real parameter \(T\). The comparison operator is
   \[
   \rho(e^{Tz})=\exp\left(\sum_{k\ge2}\frac{(-1)^k\zeta(k)}k z^k\right)e^{Tz}.
   \]
   In this single-divergence case only degrees zero and one occur, and \(\rho(1)=1,\rho(T)=T\). The verifier must reject other divergent input patterns and verify that the final row is admissible. Applying this identity comparison blindly to two divergent factors would be incorrect.
3. Optionally include ordinary distribution rows and their products with admissible complementary-weight factors:
   \[
   Z(\boldsymbol s;2\boldsymbol c)
   -2^{w-d}\sum_{\boldsymbol\epsilon\in\{0,2\}^d}
      Z(\boldsymbol s;\boldsymbol c+\boldsymbol\epsilon)=0,
   \]
   with \(c_j\in\{0,1\}\) and every term convergent. Expand lifted products by integral shuffle. No regularized distribution is assumed. The newer S4 certificate shows that this family need not be included in the first attempt.
4. Convergent Cayley relations from \(\phi(t)=(1-t)/(1+t)\). In the omega convention let \(\tau\omega_a=\omega_{\phi(a)}-\omega_{-1}\) for \(a\ne-1\), and \(\tau\omega_{-1}=-\omega_{-1}\). At weight seven,
   \[
   \mathcal I(w)+\mathcal I(\operatorname{reverse}(\tau w))=0.
   \]
   Every transformed term is convergent when the original word is; no tangential-basepoint correction occurs for these rows.

Two natural initial Cayley seeds directly parallel the two pinned S4 certificates:

\[
\begin{aligned}
D_7^{(1,6)}={}&\operatorname{Im}\{\mathcal I(e_{-i}e_0^5e_{-i})
 +\mathcal I((e_i-e_{-1})(e_1-e_{-1})^5(e_i-e_{-1}))\}=0,\\
D_7^{(6,1)}={}&\operatorname{Im}\{\mathcal I(e_0^5e_{-i}^2)
 +\mathcal I((e_i-e_{-1})^2(e_1-e_{-1})^5)\}=0.
\end{aligned}
\]

Each transformed product has exactly 128 convergent terms, all of depth seven. Products here mean noncommutative concatenation. The verifier checks both term counts and convergence. A restriction to depth at most two or three would therefore discard the direct Cayley expansions before they could be reduced.

The next finite target is to find rational coefficients such that the **same** formal vector \(F_7\) equals a sum of the above standard rows and selected Cayley rows. One can start with the newer S4 schemas and the \((6,1)\) seed, then enlarge the seed set if needed; there is no evidence here that a single seed will suffice. A modular calculation could discover a candidate sparse combination, but the deliverable must replay it over exact rational arithmetic from the target and row descriptors, independently regenerate all shuffles/stuffles/Cayley images, check admissibility, and end with an empty coefficient dictionary. No numerical period evaluation or conjectural independence assumption belongs in that proof.

## Delivered exact audit

- `verify_s6_target.py`: self-contained Python standard-library verifier; no solver and no numerical periods.
- `s6_target_audit.json`: exact target vector, its scale, 192 restricted-row checks, the full 12-coordinate single-by-double row, separator diagnostic −1, alphabet counts, and both Cayley seed diagnostics.
- `S6_depth_three_bridge.tex`: ready-to-integrate subsection with definitions, proof, and precise role in the unfinished S6 problem.

All checks pass. The unresolved assertion is exactly the rational row membership needed to prove \(F_7=0\); that membership was not calculated or asserted in this focused audit.
