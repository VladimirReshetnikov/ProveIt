# Correction register for the Polylogarithms documents

## Scope and integration status

This register accompanies the research continuation dated **2026-10-08**. Source paths below are relative to **Analysis/Polylogarithms/docs/** in ProveIt commit **3a6d80ed618d839915deb0d19ab687f45e81d995**. Line numbers refer to that snapshot; LaTeX labels and section titles are the preferred anchors.

The entries describe proposed source edits and the evidence supporting them. The historical source files have not been patched by this package. This is a targeted review of specified passages, not a complete audit of all 31 reports or every displayed formula. “Already flagged” means recorded in the existing README under “Status of claims, and known defects”; “Additional” means a finding or stronger diagnosis supplied by this audit.

Detailed proofs are in [corrections_gamma.tex](sections/corrections_gamma.tex), [corrections_polylogs.tex](sections/corrections_polylogs.tex), and [corrections_additional.tex](sections/corrections_additional.tex). The register also points to repairs proved elsewhere in the new article. Numerical checks support regression testing; exact arithmetic checks verify the finite calculations identified in their corresponding proofs.

## Corrections already identified at intake

### C01. Incorrect constant in an external dilogarithm identity

**Source:** `reports/report-1.tex`, “Rational Arguments and High-Order Polylogarithms,” line 49. **Status:** Already flagged; exact error.

**Evidence and replacement:**

$$
6\operatorname{Li}_2(1/3)-\operatorname{Li}_2(1/9)
=\frac{\pi^2}{3}-\log^2 3,
$$

where the source prints $\pi^2/6$. Duplication, Landen's identity at $1/3$ and $-1/3$, and the classical value of $\operatorname{Li}_2(1/2)$ give the corrected formula. The error is exactly $\pi^2/6$.

**Action:** Correct the displayed coefficient and regenerate its PDF. Preserve the README's identification of `report-1` as an external research input; this isolated repair does not validate its other assertions.

### C02. Koblitz–Ogus versus Rohrlich completeness

**Source:** `articles/gamma-lattice-and-certificates.tex`, `law:ko` (lines 133–138), abstract, introduction, and descriptions of irreducible bases. **Status:** Already flagged; theorem attribution and scope.

**Evidence:** The Koblitz–Ogus sufficient algebraicity criterion does not prove the converse that every algebraic gamma monomial at rational arguments follows from the standard reflection and multiplication relations. That converse is Rohrlich's conjecture.

**Action:** Replace the asserted completeness theorem by a conjecture or conditional statement. Retain exact reductions and basis claims **within the specified formal relation space**. Qualify claims of completeness among all algebraic relations throughout the abstract, text, and tables. See `corr:gamma-certificates` in the new article.

### C03. Failed integer-relation searches do not establish nonreduction

**Sources and anchors:**

- `reports/cleo-arctan-sin-chi2__31ffeac4a7ca.tex`: `prop:class` and `sec:minimal`, especially lines 147–160 and 217–222.
- `articles/gaussian-multiple-polylog-depth.tex`: `thm:alternation`, `sec:depth-two-weight-five`, and accompanying minimal-depth statements.
- `articles/polylog-polygamma-bridge.tex`: `res:crystal` and the “new atoms” discussion in `sec:collapse`.
- `articles/stieltjes-parameter-derivative-tower.tex`: `sec:atoms`, lines 303–315, asserting mutual independence of six second-$s$-derivative constants.
- `articles/eisenstein-row-sums-cm-polygamma.tex`: `neg:sums`, lines 357–364, and `res:genus`, lines 399–412, where finite searches support asserted irrationality or algebraic degree.

**Status:** The first three instances were already flagged by the README. The Stieltjes second-derivative and CM-point instances are additional audit findings.

**Evidence:** A failed height-bounded PSLQ/LLL search gives no unrestricted lower bound on the number or depth of constants needed. A zero coefficient on an added numerical canary is a useful diagnostic, not an exact proof of an identity or of independence.

In particular, the reported 200-digit searches for $\zeta''(2)$, $\zeta''(3)$, $\beta''(2)$, $\beta''(3)$, $L''(2,\chi_{-3})$, and $L''(3,\chi_{-3})$ do not prove their mutual independence or their independence from the lower-layer inventory. At CM points, failure to find a rational relation of bounded height does not prove irrationality, and failure to find a quadratic polynomial of bounded height does not establish degree four.

**Action:** Report the tested inventory, precision, coefficient bound, and observed failure. Withdraw “minimal,” “non-elementary,” “irreducible,” and “exactly when” conclusions unless separately proved. Preserve valid positive identities. The new article proves the all-even-weight Gaussian reduction, `gau:all-weights` in [gaussian_reduction.tex](sections/gaussian_reduction.tex); it does not prove the odd-weight nonmembership half of `thm:alternation`. The Clausen character formulas remain exact; the claimed independence of the additional $L$-value components remains a separate question. The stronger depth-three error is addressed in C10.

Replace the six Stieltjes “mutually independent atoms” by six unreduced candidates for the reported searches. Likewise qualify the CM nonrationality and degree assertions unless an exact arithmetic proof is supplied. The formal rank theorems in this package do not establish these missing independence or minimal-polynomial claims. See `audit:additional` for the corresponding article discussion.

### C04. Finite rank experiments extrapolated to every denominator

**Source:** `articles/stieltjes-parameter-derivative-tower.tex`, `thm:rank`, lines 195–209. Related source: `articles/stieltjes-antiderivative-ladder.tex`, `prop:jetrank`. **Status:** Positive-tower gap already flagged; unrestricted proofs now supplied.

**Evidence:** The original positive-tower verification covers $3\leq q\leq30$, $1\leq k\leq3$. The negative-jet proposition likewise had finite experimental coverage. Such checks alone do not prove unrestricted quantifiers.

**Action:** Cite the all-denominator proofs in [distribution_ranks.tex](sections/distribution_ranks.tex), especially `rank:main` and `rank:reflection`. State the background inventory explicitly: endpoint values and the inhomogeneous lower-layer terms are prescribed data. The proved positive-tower **formal** residual dimension is $\varphi(q)-1$. For negative jets, $q\geq3$,

$$
r_{q,k}=
\begin{cases}
\varphi(q)/2-1,&k\ \text{odd},\\
\varphi(q)/2,&k\ \text{even}.
\end{cases}
$$

These are ranks of specified relation modules, not independence theorems for evaluated constants. Update the README to distinguish the original experimental support from the newly supplied proof.

## Definitions, convergence, and polylogarithm ladders

### C05. Absolute convergence on the boundary

**Source:** `articles/multiple-polylogarithms-introduction.tex`, theorem “Domain of absolute convergence,” lines 231–235 and its following paragraph. **Status:** Additional; exact counterexample.

**Evidence:** $\operatorname{Li}_1(i)=\sum i^n/n$ satisfies the printed hypotheses $\Re s_j\geq1$, $|z_j|\leq1$, $(s_1,z_1)\ne(1,1)$, but its absolute-value series diverges.

**Action:** Under the other stated hypotheses, use the sufficient condition

$$
|z_1|<1\quad\text{or}\quad \Re s_1>1.
$$

The nested absolute sum is bounded by

$$
\frac1{(k-1)!}\sum_{n\geq1}
\frac{|z_1|^n(1+\log n)^{k-1}}{n^{\Re s_1}}.
$$

Discuss conditional boundary convergence separately. Retain $s_1\geq2$ as the usual positive-integer MZV admissibility condition. Proof: `audit:poly:convergence`.

### C06. The ordinary series defining $S_0$ diverges

**Source:** `articles/gaussian-multiple-polylog-depth.tex`, definition of $S_p$, lines 128–132. **Status:** Additional; domain correction.

**Evidence:** At the allowed endpoint $p=0$, the terms are $(-1)^nH_n$, which do not tend to zero.

**Action:** Change the ordinary-series domain to $p\geq1$. Any value at $p=0$ must be introduced by an explicitly named regularization and must not be identified with a convergent series. See `audit:poly:convergence`.

### C07. Inconsistent ordering of iterated-integral letters

**Sources:** `articles/gaussian-eisenstein-double-polylogs.tex`, `eq:G-def` and `eq:goncharov-dbl`; `articles/multiple-polylogarithms-introduction.tex`, subsection “Goncharov's iterated integral and GeneralizedPolyLog,” lines 276–282. **Status:** Additional; incompatible definitions.

**Evidence:** Attaching $a_j$ to $t_j$ on $0<t_1<\cdots<t_n<1$ makes the printed integral for $G(0,z^{-1};1)$ contain the divergent inner integral $\int_0^{t_2}dt_1/t_1$. Its claimed value $-\operatorname{Li}_2(z)$ is finite at $z=1/2$.

**Action:** Adopt the leftmost-letter-outermost recursion

$$
G(a_1,\ldots,a_n;z)=\int_0^z
\frac{G(a_2,\ldots,a_n;t)}{t-a_1}\,dt.
$$

The matching simplex is $0<t_n<\cdots<t_1<1$, and

$$
\operatorname{Li}_{a,b}(u,v)
=G(0^{a-1},u^{-1},0^{b-1},(uv)^{-1};1).
$$

At depth $k$, its nonzero letters are $(z_1\cdots z_j)^{-1}$ for $j=1,\ldots,k$, in that order. Correct the general dictionary consistently. Alternatively reverse every word while keeping the original simplex convention. State any endpoint regularization separately. See `audit:poly:integral-order`.

### C08. Two divergent uncolored MZVs used in a comparison

**Source:** `articles/gaussian-multiple-polylog-depth.tex`, weight-four symmetric-triple discussion, line 351. **Status:** Additional; ordinary-series divergence.

**Evidence:** Both $\zeta(1,2,1)$ and $\zeta(1,1,2)$ diverge in the stated nested-sum convention. Their inner sums have a fixed positive lower bound for all sufficiently large outer indices, leaving a harmonic lower bound.

**Action:** Remove the comparison with
$\zeta(2,1,1)+\zeta(1,2,1)+\zeta(1,1,2)$, or supply a precisely specified regularized identity. Keep the convergent value $\zeta(2,1,1)=\zeta(4)$. See `audit:poly:other`.

### C09. Modified polylogarithm includes an erroneous $\operatorname{Li}_0$ term

**Source:** `reports/ladders-as-bloch-elements__ce20ea60a460.tex`, `eq:Pm`, lines 41–44; complex-embedding computation, lines 95–96. **Status:** Additional; formula and numerical-value correction.

**Evidence:** For $m\geq2$, replace the upper summation endpoint $m$ by $m-1$:

$$
P_m(z)=\operatorname{Re}_m
\sum_{j=0}^{m-1}\frac{2^jB_j}{j!}
\log^j|z|\,\operatorname{Li}_{m-j}(z).
$$

Here $B_1=-1/2$, with real part for odd $m$ and imaginary part for even $m$. The extra printed term gives an exact excess $2\log^2(2)/15$ at $m=2,z=i/2$.

**Action:** Correct the definition and recompute affected even-weight complex-embedding values. At the lower nonreal root of $z^3+z-1=0$, the corrected value is

$$
P_4(z_-)=-0.916010467826680838722383200166\ldots,
$$

rather than $-0.915999527027516872882916723105\ldots$. Odd-weight checks and the test $z=i$ cannot detect this endpoint error. See `audit:poly:modified` and `audit:poly:correct-P`.

## Depth and dimension claims

### C10. The binomial formula is not the ordinary depth dimension

**Source:** `articles/gaussian-eisenstein-double-polylogs.tex`, `thm:deligne`, `eq:binomial-dim`, `eq:gr3-positive`, `cor:depth3`. **Status:** README flagged conditional numerical depth-three claims; this audit identifies a stronger error in the stated motivic argument.

**Evidence:** At weight six the level-four single polylogarithms lie in the span of $\zeta(6)$ and $i\beta(6)$:

$$
\operatorname{Li}_6(-1)=-\frac{31}{32}\zeta(6),\qquad
\operatorname{Li}_6(\pm i)=-\frac{31}{2048}\zeta(6)\pm i\beta(6).
$$

Thus ordinary depth one has dimension at most two, whereas the asserted $\binom61$ gives six. The positive-weight depth-zero component is also not $\binom n0=1$.

**Action:** Withdraw the displayed depth-dimension formula and the stated proof of `cor:depth3`. A weight Hilbert series does not specify a depth filtration. Even a correct nonzero ambient motivic depth-three space would not establish independence or nonvanishing of these particular triples. Supply a computation of their classes before making a corresponding conditional numerical claim. Merely adding the period conjecture does not repair the argument. See `audit:poly:depth-dimensions`.

### C11. Seven relations do not make seven individual triples products

**Source:** `articles/gaussian-eisenstein-double-polylogs.tex`, `prop:7of10` and preceding shuffle rank calculation. **Status:** Additional; exact linear-algebra diagnosis.

**Evidence:** The 13 formal product rows have rational rank seven in the ten weight-six triple coordinates. However, none of the ten individual coordinate vectors lies in their row space. Three integer annihilating functionals in `audit:poly:shuffle-rank` detect every coordinate.

**Action:** Say that seven variables can be eliminated **in terms of three survivors and products**, or that seven independent linear combinations are products. The formal quotient has dimension three. This does not determine its dimension after numerical evaluation. Reproduction: [verify_shuffle_audit.py](code/verify_shuffle_audit.py) and [gaussian_shuffle_audit.json](data/gaussian_shuffle_audit.json).

### C12. Formal coranks asserted as numerical dimensions

**Source:** `articles/gaussian-eisenstein-double-polylogs.tex`, `thm:gauss-5` and `thm:eis-1`. **Status:** Additional scope correction, related to the README's independence cautions.

**Evidence:** Relations from a specified matrix yield an upper bound for the dimension of the numerical span. Equality needs completeness of the relations or an independent lower-bound theorem.

**Action:** Identify the formal quotient and product inventory precisely; describe computed coranks as formal dimensions and upper bounds on evaluated spans. Preserve the established shuffle/stuffle identities. See `audit:poly:shuffle-rank`.

### C13. Fifty individual nonmembership tests do not give fifty new directions

**Source:** `articles/gaussian-multiple-polylog-depth.tex`, lines 377–379, “other-point doubles” discussion. **Status:** Additional; logical dimension error.

**Evidence:** Even if all 50 values were proved to lie outside a fixed span, their quotient classes could all be the same nonzero class. Individual nonmembership does not imply joint independence. Failed numerical membership tests prove less.

**Action:** Replace the claimed lower bound of 50 independent directions by a list of tested candidates and search results. Withdraw deductions that the depth-three interpretation has thereby been closed. A joint quotient-rank argument would be required. See `audit:poly:other`.

## Log-gamma, Herglotz, and class-field corrections

### C14. Missing even-character contribution in log-gamma integrals

**Sources:** `articles/polylog-polygamma-bridge.tex`, abstract, `sec:psim2`, and the extrapolation preceding `res:loggamma`; `reports/loggamma-integrals-clausen-bridge__c5013328db83.md`, Section 1. **Status:** Additional; overbroad reduction claim.

**Evidence:** The correct general identity is

$$
\int_0^a\log\Gamma(t)\,dt
=\zeta'(-1,a)-\zeta'(-1)+\frac{a-a^2}{2}
+\frac a2\log(2\pi).
$$

At denominator five, the proved reduction is

$$
\int_0^{1/5}\log\Gamma(t)\,dt
=\frac2{25}+\frac{\log(2\pi)}{10}
+\frac{\operatorname{Cl}_2(2\pi/5)}{4\pi}
-\frac65\zeta'(-1)+\frac1{20}L'(-1,\chi_5)
-\frac{29}{1200}\log5.
$$

**Action:** Preserve the correct examples at denominators 3, 4, and 6. State that the odd reflection component is Clausen-explicit, while the even component retains the relevant Dirichlet-$L$ derivatives absent further proved relations. Reconcile the earlier discussion with the later `stieltjes-antiderivative-ladder.tex`. This is not a proof of transcendence or independence of $L'(-1,\chi_5)$. Proof: `corr:loggamma-five`.

### C15. False denominator criterion for Herglotz reductions

**Source:** `reports/herglotz-arithmetic-study__467d9018ec87.tex`, `prop:collapse`, abstract, and associated necessity claims. **Status:** Additional; exact counterexamples.

**Evidence:** The report's own `thm:F1q` gives

$$
F(1/7)-F(1)=-\frac{19\pi^2}{28}
-\sum_{r=1}^{3}\log^2(2\sin(\pi r/7)),
$$

although $7\nmid30$. Excluding numerator one does not repair the criterion: with $S(q)=\sum_{r=1}^{q-1}\log^2(2\sin(\pi r/q))$,

$$
F(6/7)-F(1)=-\frac{8\pi^2}{63}+\operatorname{Li}_2(6/7)
+\frac12\log^2(7/6)-\frac12S(7)+\frac12S(6).
$$

**Action:** Delete the asserted “if and only if” classification and the unsupported global inventory of only the stated rational dilogarithm atoms. Retain proved families and separately proved reductions. No replacement necessity classification is claimed here. Proof: `corr:herglotz`.

### C16. False exceptional-denominator list for $J$

**Source:** Same report, `prop:J` and abstract. **Status:** Additional; exact counterexample.

**Evidence:** Under the source's convention allowing $\pi^2$ among its “pure-logarithm” expressions,

$$
J(1/2)=\frac{\pi^2}{48}+\frac14\log^22.
$$

This is the omitted $q=4$ instance of $J(2/q)$. It also contradicts the statement that $J(1/q)$ always retains dilogarithms.

**Action:** Remove the exclusivity assertion $q\in\{3,5\}$ and the universal statement about $J(1/q)$. An odd-denominator restriction avoids this counterexample but does not prove necessity. Proof: `corr:J-half`.

### C17. Undefined even-denominator summand and a false non-elementarity claim

**Source:** Same report, `thm:deriv`, lines 196–204. **Status:** Additional; removable-singularity convention and exact counterexample.

**Evidence:** At $r=q/2$, the product $\cot(2\pi r/q)\operatorname{Cl}_2(2\pi r/q)$ is undefined as printed. Its continuous value is $-\log2$. At $q=4$, the corrected formula gives $F'(1/2)=2+\pi^2/4$.

**Action:** Either omit the middle summand and retain the separate even-$q$ term $-\log2$, or include its continuous value and remove that separate term. Do not use both conventions. Delete the universal claim that the derivative family never has elementary values. Proof: `corr:herglotz-derivative`.

### C18. A cubic field is not the quadratic field's degree-six class field

**Source:** `reports/herglotz-stark-regulators__6096eccfa2a0.tex`, “The determinant is a regulator,” lines 113–116; “The cubic ring-class family,” including `tab:family` and its caption. **Status:** Additional; degree mismatch.

**Evidence:** A degree-three field $H_0/\mathbb Q$ cannot contain quadratic $K$. In the intended $S_3$ situation, $[H:K]=3$, $[H:\mathbb Q]=6$, and $H_0$ is a non-Galois cubic subfield of $H$.

**Action:** Use different symbols for the cubic field and the Hilbert/ring class field over $K$. Identify the tabulated cubic polynomial as defining $H_0$, whose normal closure is $H$. Propagate this distinction to regulator notation and captions. See `corr:stark-fields`.

### C19. Missing class-number factor; concrete class numbers now certified

**Source:** Same report, “The regulator as a leading L-value,” lines 218–226. **Status:** Additional omitted hypothesis, with an exact repair supplied for the five concrete fields.

**Evidence:** For the associated Artin (primitive Hecke) $L$-function, Artin formalism and the analytic class number formula give

$$
L_K(s,\chi)=\frac{\zeta_{H_0}(s)}{\zeta(s)},\qquad
L_K^*(0,\chi)=h(H_0)\operatorname{Reg}(H_0).
$$

The five displayed cubics have $h(H_0)=1$, proved in `corr:cubic-class-numbers`. Their discriminants are $148,404,788,257,2708$, with integer Minkowski bounds $2,4,6,3,11$.

**Action:** Include $h(H_0)$ in the general identity, and cite the supplied class-number certificates when specializing to these five fields. The proof checks maximal orders, splitting types, and principal generators for every prime ideal within the bound; it includes the norm-9 prime in the last field. It proves the leading-coefficient specialization, not the report's separate fitted Herglotz formulas. Reproduction: [verify_cubic_class_numbers.py](code/verify_cubic_class_numbers.py) and [cubic_class_number_certificates.json](data/cubic_class_number_certificates.json).

### C20. Numerical branch guards are not exact domain certificates

**Source:** `articles/gamma-lattice-and-certificates.tex`, `sec:certmodel`, lines 311–322; related open direction at line 436. **Status:** Additional proof obligation; no particular value is disproved.

**Evidence:** Exact algebraic cancellation proves the conclusion only if every instantiated functional identity has valid branch conditions. A numerical guard or a small residual does not alone prove those conditions.

**Action:** Include exact branch-domain evidence in each certificate, or list the branch conditions as assumptions. For algebraic arguments, certified algebraic sign tests and specified argument sectors can supply this evidence. A Bloch–Wigner reformulation is applicable only where it proves the intended single-valued statement. The original checker and identity stores are absent from the inspected directory, so this is a correction to the described guarantee, not an audit of their implementation. See `corr:gamma-certificates`.

## Rebuild and status updates

### C21. Stale cross-references in three Herglotz PDFs

**Sources:** `reports/herglotz-bridges__469ff48bb80a.tex`, `reports/herglotz-rational-values__cb565fc1c0d9.tex`, and `reports/herglotz-tables-verification__210c21f70bdd.tex`, with their matching PDFs. **Status:** Already flagged by the README; document build defect.

**Evidence:** The intake README records respectively 3, 19, and 4 unresolved references in the PDFs, with source builds resolving them after two passes.

**Action:** Rebuild affected PDFs from the final sources until cross-references stabilize; inspect unresolved-reference warnings and rendered output. Preserve the intake history while updating current status.

After applying source edits, update abstracts, summaries, captions, and companion reports wherever they repeat the corrected claim. Record which original claims were false, which were insufficiently justified, and which now have a proof. Keep the finite numerical checks distinct from the exact arithmetic certificates and analytical proofs.

The combined numerical checks for C14–C17 are in [verify_corrections.py](code/verify_corrections.py) and [corrections_checks.json](data/corrections_checks.json). The formal shuffle and cubic certificates are exact calculations. None of these check files should be described as establishing unrestricted numerical-period independence.

## Additional convention correction

### C22. Clausen parity in the Eisenstein single-polylogarithm formula

**Source:** `articles/gaussian-eisenstein-double-polylogs.tex`, `eq:eis-single`, lines 393–398. **Status:** Additional; direct mismatch with the Clausen convention used elsewhere in the corpus.

**Evidence:** With $\omega=e^{2\pi i/3}$, the stated real-part formula

$$
\Re\operatorname{Li}_n(\omega)=\tfrac12(3^{1-n}-1)\zeta(n),\qquad n>1,
$$

is correct. The assertion $\Im\operatorname{Li}_n(\omega)=\operatorname{Cl}_n(2\pi/3)$ for every $n$ is not correct under the corpus convention, where $\operatorname{Cl}_n$ is the sine series at even weight and the cosine series at odd weight. For example,

$$
\Im\operatorname{Li}_3(\omega)=\frac{2\pi^3}{81},
\qquad
\operatorname{Cl}_3(2\pi/3)=\Re\operatorname{Li}_3(\omega)
=-\frac49\zeta(3).
$$

The first value follows from the cubic sine Fourier series; the second follows from distribution. They have opposite signs.

**Action:** Restrict the imaginary-part identification with $\operatorname{Cl}_n$ to even $n$. For odd $n$, write the sine series $\sum_{m\geq1}\sin(2\pi m/3)/m^n$ explicitly or introduce a separately named sine-polylogarithm function. Preserve the correct real-part identity and harmonize the notation throughout the article. Numerical checks under an unstated alternative convention do not resolve the mismatch. Full proof: `audit:additional` and `audit:clausen-three` in [corrections_additional.tex](sections/corrections_additional.tex).

