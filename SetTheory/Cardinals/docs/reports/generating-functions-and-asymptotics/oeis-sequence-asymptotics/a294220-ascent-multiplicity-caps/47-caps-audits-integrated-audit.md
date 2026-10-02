# Independent integrated mathematical audit

Audit date: 1 October 2026 (UTC).

## Verdict

**PASS. No substantive mathematical repair is required.** The integrated report proves its stated fixed-cap theorem for every fixed integer \(b\ge3\), including the quantitative logarithmic error \(O_b(n/\log n)\), and correctly derives the length inverse with error \(O_b(L/(\log L)^3)\). The exact zeta first variation, the large-cap nonlinear remainder, and both integer-safe cap brackets are valid. I independently checked the explicit constants \(160\), \(644\), and \(2000\).

This is a mathematical audit of the supplied argument, not journal peer review or an exhaustive novelty certification. The cap-two analytic theorem remains an explicitly imported result from the separately audited companion document. The general-cap proof does not silently use that result to prove its \(b\ge3\) assertions.

### Pinned integrated source

- File: `bounded-multiplicity-report.tex`
- Final reviewed SHA-256: `0e53f4ea4f87c8cfe9167210239472ecd3e1bf6995159d563357c8780ec389ec`
- Initially reviewed SHA-256: `06b23e61fb069619d2e6559213ff742a42387ca4c7eae522aa62bb016d039183`

The complete initial source was read. Two changes were made by the author during this audit: the pair of concentration inequalities was moved into display math, and the length-inverse statement was made explicit with “As \(X\to\infty\) with \(b\) fixed.” Reversing exactly those two replacements reproduces the initial SHA-256. Thus the final pinned version has been checked in its entirety. I did not modify the report.

The initially absent `provenance.json` was supplied during the audit. Its proof-source and companion-file hashes were checked against the available files. No release issue identified in this review remains open.

## 1. Exact counting and indexing

The invariant \(\max(w)\le\operatorname{asc}(w)\) is correct by induction: when a new maximum is appended, the ascent-sequence upper bound is the old ascent count plus one and an ascent occurs; otherwise the old maximum still bounds all values. Therefore the top admissible label is unused and strictly above the last value. Exactly one new top label becomes available after an ascent.

The raw state consisting of ordered positive budgets and the boundary \(k\) is sufficient. The condition \(i\ge k\) correctly describes an ascent even when the old last label has just been exhausted. Removing an exhausted choice gives boundary \(i\); retaining it gives boundary \(i+1\). These are rank boundaries, not positions that move with a budget during subsequent compaction.

The adjacent-budget interchange is a genuine involution on suffixes:

1. Reversing and complementing every maximal binary block exchanges the total usages of the two labels.
2. All prefix usages obey the exchanged quotas because each is bounded by its total usage.
3. Internal block ascents are preserved: a pair \(p<q\) is transformed into the same ordered comparison after reversal and complementation.
4. Every outside comparison is unchanged because no available outside label lies between the adjacent active pair. Exhausted intermediate labels never return, and new labels lie above the initial alphabet.
5. An initial binary block starts with a nonascent on both sides of the map. Ascent counts match at block ends and before outside letters. Altered timing inside a block cannot violate the upper bound, since both block labels were admissible initially and the bound never decreases.

The restriction to swapping labels below the last boundary is essential and is respected. Decrementing a nonexhausted entry only requires moving it to the beginning of its old budget group; all such swaps lie within the first \(i+1\) entries. Exhaustion already leaves the tuple sorted. Thus the grouped population transition is exact rather than an approximation or an unsupported global sorting operation.

The grouped state space preserves \(u\ge1\), \(0\le k<m\), and \(m'\le m+1\). In particular, choosing the final top unused label is necessarily ascending and replaces the unused label it consumes. The indexing is consistent throughout:

\[
\mathcal T^r\mathbf1(x_1)=a_{r+1}^{(b)},\qquad
F(t,x_1)=A_b'(t),\qquad
x_N\text{ is reached by a prefix of length }N.
\]

The coefficient \(\mathcal T^j\mathbf1(x_N)\) therefore injects into words of length \(N+j\), and not \(N+j+1\). Appending the new maximum gives an injection into every larger length and proves monotonicity of the counts. The \(b=1\) remark is also correct: only the increasing word is possible and the displayed integral diverges.

## 2. Characteristic equations and state-uniform barrier

Direct differentiation of \(q=\log E_b(v)\), \(p_j=\log E_{b-j}(v)\), and \(dt/dv=q/(E_b-1)\) gives both characteristic equations. Their removable values at zero are one. The large-\(q\) asymptotics, including the constant

\[
c_b=(b!)^{(b-1)/b}/(b-1)!,
\]

follow from the leading polynomial terms. Differentiated estimates are justified here because the quantities are explicit rational functions of \(v\), with rational \(q\)-differentiation factor \(dv/dq=E_b/E_{b-1}\).

The weight ordering follows from the displayed polynomial identity. More explicitly, the coefficient of \(v^k\), \(1\le k\le r\), in the bracket is

\[
\frac{r+1-k}{(r+1)k!}>0,
\]

and the constant coefficient is one. Thus \(E_{r-1}/E_r\) increases with \(r\), giving the claimed ordering of the \(\rho_j\). The positive limits \((b-j)/b\), continuity, and rational derivative estimates give the fixed-cap lower bound \(c\) and derivative bound \(K\). No uniformity in \(b\) is required or claimed.

The exact child weighted-rank formula is correct. Before compaction, the population weight below the new boundary is \(H+\rho_{j+1}\); an appended new top label is outside this boundary, and every compaction swap stays inside it. Consequently

\[
D_i=D-(\rho_j-\rho_{j+1})+\alpha,
\qquad
r_i=\frac{H+\rho_{j+1}}{D-(\rho_j-\rho_{j+1})+\alpha}.
\]

The inequalities \(D_i\ge1\) and \(D_i\ge D-1\) imply \(D_i\ge D/2\), including small states. Subtraction gives \(\lvert r_i-H/D\rvert\le4/D\). For an ascent, \(r(k)\le H/D\) and \(r_i\ge H/(D+1)\), proving the crucial one-sided loss bound \(r(k)-r_i\le1/(D+1)\le1/2\).

I checked the frozen integral directly by integrating \(\phi_y=-(q\rho_j/D)\phi\) on the two sides of \(k\). The sum before division by \(\phi(k)\) is exactly \(\dot qD\phi(k)\). This works for group zero as well as the used-label groups and extends continuously to \(q=0\).

All frozen ratios are bounded by \(C_be^{\theta q}\). Within each interval cut at group boundaries and \(k\), the integrand decreases and the endpoints are integers, so the left-sum error is state-independent. Exact descending ratios obey the same bound, while exact ascending ratios obey \(C_be^{(\theta+1/2)q}\). Applying the exponential difference inequality, the \(4/D\) rank bound, and \(m/D\le1/c\) yields the stated transition residual. The time derivative is also state-uniform because

\[
|r_q|\le (|h_q|+|D_q|)/D\le2K/c.
\]

The integrated residual is \(O_b((1+q)^3e^{q/2})\). Its being \(o(e^{p_1})\) uses precisely \(\theta>1/2\), which holds for \(b\ge3\) and explains the explicitly stated exclusion of \(b=2\) from this barrier proof.

## 3. Infinite-state comparison and exact radius

The jump chain is nonexplosive because, after \(j\) jumps, its total jump rate is at most \(m(x)+j\). The corresponding linear pure-birth process is nonexplosive. Summation over finite jump paths cancels the survival factors with the potential factor and produces the positive series defining \(F\), including possible value \(+\infty\).

The stopped state region \(m\le M\) is finite for fixed \(b\), so stopped Dynkin comparison is legitimate. The upper comparison needs only positivity of the exit term. The lower comparison correctly retains this term and bounds it using the strictly later-time supersolution:

\[
g_-(v,y)\le C e^{-\eta m(y)}g_+(v+\delta,y).
\]

The population coefficient increments have a common strictly positive minimum on the compact time interval. The rank term is uniformly bounded and the residual corrections have favorable signs. At exit \(m=M+1\), so the exit expectation tends to zero. No unproved infinite-system uniqueness or uniform-integrability assertion is used.

For \(x_N\), the exact rank correction is \(q/(\rho_1N+1)\), and hence the logarithmic barrier error is independent of \(N\). The nonnegative semigroup identity and the one increasing-prefix path at every length give

\[
F(t+h,x_1)\ge\exp(p_1-\mathcal E+h e^{p_1}).
\]

This diverges as \(t\uparrow T_b\), proving divergence at each \(T_b+h\). The comparison proves finiteness below \(T_b\). Differentiation preserves power-series radius, so the conclusion for \(A_b\) is correct. The report correctly recognizes that this alone establishes only the normalized-root limsup.

## 4. Every-length coefficient extraction and the logarithmic error

The Chernoff argument uses barrier values, not derivatives of their error. Its center \(K=NM(q)\) need not be the exact mean. Direct differentiation gives the uniform shifted limits

\[
H_q''(v)\longrightarrow\theta^2e^{-\theta v},
\qquad M(q)d(q+v)\longrightarrow\theta e^{-\theta v}
\quad(|v|\le1).
\]

They give a uniform quadratic upper bound on \(H_q\) and a uniform linear lower bound on the absolute change of \(\log t\). Thus taking \(v=\pm\gamma\varepsilon\), with fixed sufficiently small \(\gamma\), gives a negative main exponent of order \(N\varepsilon^2\), even when \(\varepsilon\) shrinks. The two logarithmic barrier errors are bounded by \(2\mathcal E(q+1)+O_b(q+1)\), independently of \(N\).

For the prescribed choices \(q=(\log n)/2\), \(\varepsilon=(\log n)^{-2}\), and \(N=\lfloor(1-4\varepsilon)n/M(q)\rfloor\),

\[
N\varepsilon^2\asymp_b\frac{n^{1-\theta/2}}{(\log n)^3},
\qquad \mathcal E(q+1)=O_b(n^{1/4}(\log n)^3).
\]

The former dominates the latter; both \(N\) and the floor loss in \(K\) are \(o(\varepsilon n)\). The concentration interval has at most \(2\varepsilon K+3\) integers, so the denominator \(4\varepsilon K+6\) in extraction is valid. The buffers give \(j\ge(1-6\varepsilon)n\) and \(N+j\le n\), establishing a lower bound for every sufficiently large \(n\), rather than merely a subsequence.

The new quantitative extraction is valid. The principal factorial loss is

\[
\log(n!/j!)\le6\varepsilon n\log n=6n/\log n.
\]

Meanwhile, integrating \(dt/dq=1/\dot q\) gives \(T_b-t(q)=O_b((1+q)e^{-\theta q})\). Thus the time-substitution error is

\[
O_b(\varepsilon n+n(1+q)e^{-\theta q})=o_b(n/\log n),
\]

and the same is true of the residual and logarithmic counting losses. The favorable term \(Np(q)\) may be discarded. This proves the asserted lower logarithmic estimate.

For the upper estimate, the coefficient of \(t^{n-1}\) in \(F(t,x_1)\) is \(a_n^{(b)}/(n-1)!\), so the displayed upper inequality has the correct factorial and exponent. Its logarithmic excess is bounded by the stated \(o_b(n/\log n)\) quantity. Together the two estimates prove the announced \(O_b(n/\log n)\) error and the full root limit.

## 5. Length inverse and its scope

As \(X\to\infty\) at fixed \(b\), the threshold inequalities at \(N_b(X)\) and \(N_b(X)-1\) imply

\[
L=G(N_b(X))+O_b(N_b(X)/\log N_b(X)),
\quad G(x)=x\log(x/(eT_b)).
\]

The difference \(G(N)-G(N-1)=O_b(\log N)\) is absorbed by that error. It follows first that \(N\sim L/\log L\). The principal-branch Lambert expression satisfies \(G(n_0)=L\) exactly. On the interval between \(N\) and \(n_0\), \(G'(x)=\log(x/T_b)\asymp\log L\); therefore

\[
N-n_0=O_b(N/(\log N)^2)
=O_b(L/(\log L)^3).
\]

The relative error \(O_b((\log L)^{-2})\) follows as stated. Integer threshold effects and Stirling's logarithmic remainder are smaller than this error. No exact rounding guarantee follows, and the report expressly says so. The explicit final quantifier now removes any ambiguity about the limit being taken.

## 6. Exact first variation and nonlinear remainder

The integral representation of \(f\) gives strict decrease and convexity, proving monotonicity of \(T_b\) and nonnegativity of the first-variation remainder. Domination by the integrable cap-two integrand proves \(T_b\downarrow\pi^2/6\) without invoking the cap-two coefficient theorem.

The expansion

\[
-f'(e^v)=\sum_{h\ge2}((h-1)v-1)e^{-hv}
\]

is correct. Its terms are not all positive, but the report explicitly supplies a summable integrated absolute bound after multiplication by \(R_b\). Thus the stated Fubini step is valid. The integrated coefficient is

\[
\frac{(h-1)k-1}{h^{k+2}},
\qquad
\sum_{k\ge b+1}\frac{(h-1)k-1}{h^{k+2}}
=\frac{b+1}{h^{b+2}},
\]

giving exactly \(L_b=(b+1)(\zeta(b+2)-1)\).

I independently checked the remainder and all constants used later:

- For \(1\le z\le2\), the integral representation gives \(f''(z)\le2/3\), which is below \(16(1+\log z)/z^3\). For \(z\ge2\),
  \[
  f''(z)=\frac{2\log z-3+4/z-1/z^2}{(z-1)^3}
  \le16\log z/z^3.
  \]
- Stirling's upper bound implies \(b!\le3\sqrt b(b/e)^b\). Since \(e^{-v}E_b(v)\) decreases, \(E_b(v)\ge e^v/(3\sqrt b)\) for \(0\le v\le b\). Taylor's factor \(1/2\) therefore gives \(16\cdot27/2=216\).
- Grouping the nonnegative square of the remainder by total degree gives
  \[
  \int_0^\infty(1+v)e^{-3v}R_b(v)^2\,dv
  \le\sum_{S\ge2b+2}\frac{S+4}{9}(2/3)^S
  =\frac{8(b+4)}{27}(4/9)^b.
  \]
  Multiplication by \(216b^{3/2}\) gives the report's central bound \(64b^{3/2}(b+4)(4/9)^b\).
- On \(v\ge b\ge3\), \(E_b(v)\ge2\) and \(\log E_b(v)\le v\). The tail is bounded by \(2b!b^{2-b}/(b-2)\), and hence by \(6b^{5/2}(4/9)^b\).
- Finally, \(64(1+4/b)+6\le64(7/3)+6<160\) for all \(b\ge3\).

Thus the explicit all-\(b\ge3\) bound is established:

\[
0\le H_b\le160b^{5/2}(4/9)^b.
\]

The reciprocal identity is exact. Both \(O(b3^{-b})\) from the remaining zeta terms and \(O(b^24^{-b})\) from the reciprocal correction are absorbed by \(O(b^{5/2}(4/9)^b)\). Dividing by the leading term gives the stated relative error \(O(b^{3/2}(8/9)^b)\).

## 7. Discrete cap inverse and explicit constants

Solving \(h(b)=D(b+1)2^{-b}=\varepsilon\) on its decreasing branch gives exactly

\[
b_0=-\frac{W_{-1}(-\varepsilon\log2/(2D))}{\log2}-1.
\]

The branch and factor \(2D\) are correct. Only the elementary real model is interpolated; no interpolation of \(T_b\) is needed.

Integral comparison gives the reported bounds on \(L_b\) and \(V_b=L_b-M_b\). For \(b\ge3\),

\[
\frac{M_bL_b}{V_b}\le\frac{9b}{8}(3/4)^b
\le\frac{729}{512}<\tau.
\]

The middle maximum is attained at \(b=3,4\), as follows from successive ratios \(3(b+1)/(4b)\). Therefore \(\tau V_b>M_bL_b\), which proves the strict inequality \(d_b>h(b)\). Also \(V_b\le b^{5/2}(4/9)^b\), so

\[
0<d_b-h(b)\le\frac{161}{\tau^2}b^{5/2}(4/9)^b,
\quad
0<\frac{d_b}{h(b)}-1\le644b^{3/2}(8/9)^b.
\]

For \(x\ge13\), \(\phi(x)=x^{3/2}(8/9)^x\) decreases because \(3/(2x)<\log(9/8)\). For \(x\ge2\), \((\log h)'(x)<-1/3\). Consequently every admissible integer \(b\le b_0\) fails the threshold. The case \(b=2\), not covered by the intermediate \(d_b>h(b)\) proof, follows from monotonicity: \(d_2>d_3>h(3)\ge h(b_0)\) when \(b_0\ge13\).

At \(m=\lceil b_0+2000\phi(b_0)\rceil\), the report's bound follows from these monotonicities, and it is strictly below one because

\[
\log(1+644\phi)\le644\phi<(2000/3)\phi.
\]

This proves the explicit floor/ceiling bracket for every \(b_0\ge13\), not only asymptotically. It implies the weaker symmetric asymptotic bracket. The counterexamples to unconditional ceiling at \(\varepsilon=h(n)\), integer \(n\ge3\), are genuine because \(d_n>h(n)\). The description of near-integer transitions is therefore appropriately cautious.

## 8. Provenance, literature, numerical checks, and limits of the claims

The companion report's theorem and error declaration match the imported \(b=2\) statement. Its source SHA-256 is `8d7bb13a64982e1479996719882d9f188e00899108d4f27e44b42076e1687e1f`, and its PDF SHA-256 is `9dbe810153d1936b152c74c4a5c591e3e8b0f6d2d20d7c964186e5b554ad41c1`. These agree with the companion release and its integrated audit manifest, as well as this package's provenance file. I checked the identification of the integral: at \(b=2\), \(p_1=\log(1+v)\) and \(e^{2p_1}=2e^q-1\), giving the companion characteristic curve. Its endpoint evaluation gives \(3\pi^2/8\). The complete separate cap-two analytic proof was not re-audited here.

The literature wording was checked against primary sources on 1 October 2026:

- [OEIS A294220](https://oeis.org/A294220) identifies the maximum-multiplicity array and explicitly cross-references caps two and three as A202058 and A317784. Its displayed finite array agrees with the report.
- The [published Conway–Conway–Elvey Price–Guttmann paper](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/) verifies the authors, title, journal metadata, DOI, cap-two compacted recurrence, binary-block interchange mechanism in Section 2.6, and conjectured \(8/(3\pi^2)\) constant.
- The [Duncan–Steingrímsson preprint](https://arxiv.org/abs/1109.3641) supports the narrow description of its subject and 2011 preprint citation.
- A direct attempt to retrieve A317784 failed in this audit too. The report correctly bases its identification on A294220 and does not make unsupported claims about A317784's current formula section.

The scoped wording avoids claiming an exhaustive priority search or treating a site footer/cache date as the revision date of an individual OEIS entry.

As independent consistency checks, I generated literal ascent-sequence words directly through length nine for caps three and four; both full lists match the report. I also recomputed the integrals for \(b=2,3,4,10\) at 60-digit working precision after the different substitution \(v=x/(1-x)\), integrating over \(0\le x\le1\). The values agree with the recorded quadratures and displayed precision. These numerical checks are not interval certificates and were not used to justify a mathematical estimate. The report's totals 8,460, 5,364, 69,500, and 82,801 correctly sum the corresponding recorded finite-check counts.

The fixed-cap and large-cap limits are consistently separated. Constants in the fixed-cap coefficient estimates may depend on \(b\); the large-cap remainder has an absolute constant. There is no asserted uniform coefficient theorem when \(b=b(n)\), no exact finite-length cap guarantee, no fixed-cap prefactor or asymptotic equivalent, no normalized ratio limit, and no all-orders expansion in either variable. The remaining-questions section accurately preserves those limitations.

## Final status

No substantive gaps, incorrect constants, index errors, or unresolved scope problems were found in the pinned integrated source. The requested quantifier clarification and provenance release check were completed during review. The mathematical verdict applies to the final TeX hash recorded above.
