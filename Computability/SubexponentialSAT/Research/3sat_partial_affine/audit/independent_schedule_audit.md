# Independent audit of the partial affine doubling schedule

## Result and exact scope

The explicit fifteen-group menu and the mixed schedule below give the
normalized low-degree contraction bounds

\[
T(s)\le (s+\mathcal L)^{O(1)}
 2^{(C_T+o(1))s/\sqrt{\log_2s}},\qquad
S(s)\le (s+\mathcal L)^{O(1)}
 2^{(C_S+o(1))s/\sqrt{\log_2s}},
\]

with

\[
C_T=\frac\pi{\ln2}\sqrt{\frac{32012591492467}{5556600000000}}
=10.87878166668154\ldots,
\]

\[
C_S=\frac\pi{\ln2}\sqrt{\frac{32012591492467}{6417873000000}}
=10.12253456921954\ldots.
\]

The initial maximum degree is at most \(\lceil s^{1/12}\rceil\).
Initial precision and truncation order are at most \(s\). The exact
deformation, recovery, packing, entropy and entry-evaluation interface is
imported from the reviewed corpus. This is an independently checked finite
certificate and schedule composition relative to that interface, not a new
formal verification of the imported analytic contraction theorem and not an
implementation of the full SAT algorithm.

The source snapshot for the final comparison is commit
`324f3d9b009ab0323f33be65cd6577867c9c4338`. The following immutable source
anchors identify every imported local ingredient:

- [Exact interface, packing gates, paid recurrence, rectangular backend](https://github.com/VladimirReshetnikov/ProveIt/blob/324f3d9b009ab0323f33be65cd6577867c9c4338/Computability/SubexponentialSAT/Research/sat_pairwise_certificates/sections/interface.tex), equations `eq:gates`, `eq:recurrence`, and `eq:rectangle`.
- [Weighted coupled pair theorem and nine weighted ten-group plans](https://github.com/VladimirReshetnikov/ProveIt/blob/324f3d9b009ab0323f33be65cd6577867c9c4338/Computability/SubexponentialSAT/Research/sat_pairwise_certificates/sections/portfolio.tex), theorem `thm:pair` and equation `eq:beta10`.
- [Exact ten-group coefficient](https://github.com/VladimirReshetnikov/ProveIt/blob/324f3d9b009ab0323f33be65cd6577867c9c4338/Computability/SubexponentialSAT/Research/sat_pairwise_certificates/results/constants.tex), macro `CachedBetaSquared`.
- [Punctured seven-group and fixed four-group coefficients](https://github.com/VladimirReshetnikov/ProveIt/blob/324f3d9b009ab0323f33be65cd6577867c9c4338/Computability/SubexponentialSAT/Research/sat_affine_geometry/review/geometry.tex), final certificate table with \(\beta_7^2=891/2450\) and \(\beta_4^2=13/25\).
- [Cyclic thirteen-group seed and fixed six-group plan](https://github.com/VladimirReshetnikov/ProveIt/blob/324f3d9b009ab0323f33be65cd6577867c9c4338/Computability/SubexponentialSAT/Research/sat_affine_cauchy/sections/menus.tex), subsection “Thirteen cyclic plans” and its final six-group paragraph, which gives \(\beta_6^2=12/25\).

## New local certificate

Label the points of \(\mathbb F_3^2\) by \(3x+y\). Start with its four
parallel classes. Add a second copy of points \(0,1,2,3,4,5\), labeled
\(9,10,11,12,13,14\), to the same block in each class. Preserve the
original point order and append the duplicate labels in order. Split every
ordered block recursively at its midpoint and then contract the final
three blocks. There are four plans, each with thirteen operations.

Use the prior rectangular backend. Its nine integer supports, with
denominator \(D_*=1400000\), are the three distinct permutations of
\((1400007,1400007,0)\) and six permutations of
\((1400000,1175014,750000)\). There are 117 supports per plan in 105
unordered edge coordinates.

The independent checker reconstructs all supports and checks all
\(6\cdot117^2=82134\) pairs. For each pair of plans it maximizes
\(\|v\|^2+\|w\|^2+6v\cdot w\). The six maxima are three copies of
\(580173494513132\), followed by three copies of
\(572279799215680\). The prior coupled pair identity therefore gives

\[
\beta_{15}^2
=\frac{2\sum_{i<j}A_{ij}}{3\cdot16\cdot D_*^2\cdot15^2}
=\frac{32012591492467}{98000000000000}.
\]

The separate independent mixed time/boundary certificate proves joint
selection with \(\rho^2=231/200\). Its local time bound is unchanged and
its local storage coefficient is

\[
\sigma_{15}^2=\beta_{15}^2/\rho^2
=\frac{32012591492467}{113190000000000}.
\]

That certificate includes all singleton, intermediate, and final-block
boundary supports. It checks 82,134 time pairs, 4,374 boundary pairs, and
37,908 mixed pairs. Its exact integer selector uses upward-rounded edge
entropies and minimizes
\(\max\{\widehat T_j^2,2263800000000\widehat B_j^2\}\).
Rounding adds only a fixed constant to each exponent because the support
families and their dimensions are fixed. The root must use this joint
selector to obtain the stated smaller space coefficient.

## Mixed schedule: all packing and precision gates

Put \(\lambda=\lceil\log_2s\rceil\),
\(g=\lceil6\log_2\lambda\rceil\),
\(u_d=\lfloor\eta_d\lambda\rfloor\), and
\(a_d=\sum_{j\le d}(u_j+g)\). Use relative padding slack
\(\lambda^{-3}\) and stop at \(H=\lceil s/\lambda\rceil\) wires.
The schedule is

| Depth | Groups \(r_d\) | Taper \(\eta_d\) | Cumulative leading capacity |
|---|---:|---:|---:|
| 0 | 15 | \(567/5000\) | \(567/5000\) |
| 1 | 10 | \(87/5000\) | \(327/2500\) |
| 2 | 7 | \(407/20000\) | \(3023/20000\) |
| \(d\ge3\) | 4 | \((1443/80000)(63/100)^{d-3}\) | at most \(1999/10000\) |

At every depth, both side degrees are at most
\(s^{A_d+o(1)}\), where \(A_d=\sum_{j\le d}\eta_j\). This bound
includes original degree \(s^{1/12}\), since \(1/12<\eta_0\), and
every earlier fresh degree \(2^{a_j+1}\). With \(Q_d=r_d^{a_d}\), the
three numerators in the imported gates

\[
Q_dR/M=o(1),\quad Q_d^2C(\log s)^2/M=o(1),\quad
2^{a_d}Q_d^2/M=o(1)
\]

all have exponent at most \(A_d(1+2\log_2r_d)+o(1)\). The following
exact integer inequalities prove a strict gap below one at every stage:

\[
450^{567}<2^{5000},\qquad
200^{327}<2^{2500},\qquad
98^{3023}<2^{20000},\qquad
5\cdot\frac{1999}{10000}<1.
\]

These fixed gaps absorb \(s/M\le\lambda\), the padding and packing
polylogarithms, and the total guard contribution
\(O((\log\lambda)^2)\).

To avoid a circular depth argument, first consider hypothetical tail depths
up to \(\log_{20/11}\lambda+O(1)\). The least retained taper is then

\[
\lambda^{1-\ln(100/63)/\ln(20/11)+o(1)},
\]

which diverges because \(100/63<20/11\). Thus floors and guards are
uniformly negligible throughout that range, the packing gates apply, and
the true tail child ratio \(1/2+o(1)\) is less than \(11/20\). An active
path cannot exceed the hypothetical range. The first three stages add
only a fixed number of depths. All accumulated padding errors are
\(1+o(1)\).

For a retained valuation \(i<u_d\),
\(D=2^{a_d-i}\ge2^{a_{d-1}+g+1}\). The inherited creation-precision
bound is \(p=O(s\lambda^2 2^{a_{d-1}})\). Hence uniformly at active
nodes,

\[
\frac{p}{MD/u_d}
\le O(\lambda^4 2^{-g})=o(1).
\]

The sharp working precision \((6+o(1))MD/u_d\) and entropy bound are
therefore available. Precision, field dimension, and all finite budget
descriptions remain polynomial in \(s\).

## Fully charged recurrence and space

Let \(\kappa=\pi\sqrt2/\ln2\),
\(\alpha_r=\sqrt{2(r-1)}/r\), and
\(K_d^*=\kappa m_d/\sqrt{\eta_d}\), where

\[
m_0=1,\quad m_1=2/15,\quad m_2=2/75,\quad m_3=4/525.
\]

For the tail, \(m_{3+t}=m_3 2^{-t}\), so its normalized scale decays
by \(\gamma=5/\sqrt{63}<1\). The local coefficients are the new
\(\beta_{15}\), the imported weighted \(\beta_{10}\), and the imported
\(\beta_7,\beta_4\) cited above. In particular,

\[
\beta_{10}^2=\frac{15952347164548384057}{49000000000000000000}.
\]

Every cache entry is paid through the inherited recurrence

\[
T_d\le\operatorname{poly}(s)
\bigl[2^{(\alpha_{r_d}+o(1))K_d}T_{d+1}
+2^{(\beta_{r_d}+o(1))K_d}\bigr].
\]

Write \(P_j=\sum_{i<j}\alpha_{r_i}K_i^*\). Because
\(\alpha_4/(1-\gamma)>\beta_4\), all possible tail stopping depths
are bounded by the full tail path. The complete time bound is the maximum
of precisely these four coefficients:

| Charged route | Exact expression | Certified enclosing decimal interval |
|---|---|---|
| Root operation | \(\beta_{15}K_0^*\) | [10.87878166668154, 10.87878166668155] |
| Depth-one operation | \(P_1+\beta_{10}K_1^*\) | [10.41133801093930, 10.41133801093931] |
| Depth-two operation | \(P_2+\beta_7K_2^*\) | [10.18595932806891, 10.18595932806892] |
| Full tail path | \(P_3+\alpha_4K_3^*/(1-\gamma)\) | [10.65805953246521, 10.65805953246522] |

The root strictly dominates. Leaf work \(2^{O(s/\lambda)}\), original
entry work \(2^{O(s^{9/10})}\), and fresh entry work
\(\exp(s^{1999/10000+o(1)})\) are lower order on
\(s/\sqrt\lambda\), including after the already charged ancestor
entry multiplicities. Creation-time descriptions remain frozen, so entry
evaluation does not silently re-expand a previous contraction algorithm.
Polynomial overhead over \(O(\log\lambda)\) levels adds only
\(O(\lambda\log\lambda)=o(s/\sqrt\lambda)\) to the exponent.

For space, the joint root selector gives
\(\sigma_{15}K_0^*\in[10.12253456921954,10.12253456921955]\).
The other local table bounds can conservatively use their time
coefficients. Their enclosing upper endpoints are 3.69673039341755 at
depth one, 0.72257302549579 at depth two, and 0.26221262435019 at the
first tail depth; subsequent tail bounds decrease by \(\gamma\).
The matrix backend processes one child product at a time and uses space
bounded by a polynomial factor times its largest input/output array.
The boundary certificate covers the root singleton caches as well as all
intermediate arrays. Tail array-size costs are covered by the local time
branch. Live ancestor caches add in size, rather than multiplying. A depth
first traversal therefore stores only a polynomial factor times the
largest local bound. The entry routines and leaf computation add lower
order space. This proves the stated \(C_S\); the charged time prefixes
must not be added to memory exponents.

## Strong compatible comparison built entirely from prior ingredients

The printed cached low-degree coefficient 13.37965 is not the appropriate
comparison after the fifth round. Recompose the prior cyclic thirteen
plans with the prior rectangular supports and coupled pair theorem. The
seed is

\[
(11,2,8,9,7)\mid(10,1,0,5)\mid(6,4,3,12),
\]

and all thirteen cyclic shifts preserve its within-block order. Our
independent checker constructs its 99 supports per plan, checks the twelve
off-diagonal entries in its circulant pair matrix, and obtains

\[
\beta_{13}^2=\frac{511416908935241}{1614795000000000}.
\]

Use the prior-ingredient group schedule \(13,10,7,6,4,4,\ldots\) with
successive tapers

\[
\frac{2051}{20000},\quad\frac{113}{4000},\quad
\frac{407}{20000},\quad\frac{217}{20000},\quad
\frac{14023}{1000000}(63/100)^{d-4}\quad(d\ge4).
\]

The cumulative leading capacities are
\(2051/20000,327/2500,3023/20000,81/500,1999/10000\).
Packing follows from

\[
338^{2051}<2^{20000},\quad 200^{327}<2^{2500},\quad
98^{3023}<2^{20000},\quad72^{81}<2^{500},\quad
5\cdot1999/10000<1.
\]

The same \(H=\lceil s/\lambda\rceil\), precision guard, tail bootstrap,
and space argument apply. Its five paid route coefficients are enclosed
respectively by intervals with upper endpoints
11.26420175559486, 10.89040267997346, 10.86572139736888,
11.09095203834686, and 11.26374992569384. Hence

\[
C_{\rm prior}=
\frac\pi{\ln2}\sqrt{\frac{511416908935241}{82798613625000}}
\in[11.26420175559485,11.26420175559486].
\]

The new time coefficient improves this concrete compatible bound by about
3.42 percent. This is the strongest compatible prior-ingredient
composition constructed in this review, not a proof of global optimality
over every possible prior menu or schedule. Its equal time/space bound is
a safe comparison, not a claim that previous ingredients admit no better
space tradeoff. The asymptotic order remains \(s/\sqrt{\log s}\).

## Reproduction and 3-SAT application

Run `python3 -O research_order/audit_round5_new15.py` and
`python3 -O research_order/audit_round5_baseline.py`. Their checks use
explicit exceptions, integer arithmetic, and rational interval arithmetic;
optimization mode does not disable them. The main checker reconstructs
the new fifteen-group time certificate. The baseline checker reconstructs
the cyclic thirteen-group coefficient and imports the cited ten-, seven-,
six-, and four-group finite certificates. Both check their packing and
recurrence inequalities. Machin's formula and a convergent rational
series enclose pi and ln 2. The joint space certificate is separately
reconstructed by
`research_affine_audit/check_partial_affine_joint.py`.

Their output files are `round5_new15_audit.json`,
`round5_baseline_audit.json` (the final comparison is its
`stronger_five_stage` field), and
`research_affine_audit/partial_affine_joint_result.json`.

The occurrence-preserving 3-SAT composition is proved separately in
`research_order/3sat_bridge.tex`. With \(L\) literal occurrences, it fixes
variables occurring more than \(\lceil\log_2(L+1)\rceil\) times and
uses the original incidence network. This costs
\(2^{O(L/\log L)}\) branches, at most \(L\) wires per branch, and
maximum degree \(O(\log L)\). Consequently the same \(C_T,C_S\) apply
to exact 3-SAT counting and decision on the scale
\(L/\sqrt{\log_2L}\), with a polynomial input factor. Coefficients
cannot be relabeled as coefficients per variable without tracking density.
The unrestricted variable-only order claimed in the corpus is not
improved by this construction.
