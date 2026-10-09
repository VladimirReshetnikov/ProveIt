# ProveIt research package — 8 October 2026

Three substantial articles, prepared for Vladimir Reshetnikov with OpenAI ChatGPT. The package contains **59 pages of mathematical manuscripts**, complete LaTeX sources, exact verification programs, numerical diagnostics where relevant, source audits, and proposed research agendas.

## Articles

| Directory | Article | Pages | Main contribution |
|---|---|---:|---|
| 01_universal_avoidance | A common avoiding set for stable recurrences and balanced P-recursive sequences | 23 | One near-full-measure set simultaneously avoids every nontrivial affine copy of every sequence in the stated recurrence class, with infinitely many omissions. |
| 02_parabolic_amplitudes | A Common Density for Parabolic Iteration | 16 | Exact Bell–Euler amplitude identification, positive-axis analyticity, justified geometric depth summation, and weighted partition-chain constants. |
| 03_tree_broadcast | A sharp analytic renormalization threshold for binary broadcasts on trees | 20 | The exact threshold theta>b^(-3/4), analytic critical-window residues, arbitrary-order local expansions, and majority-decoding corrections. |

Each directory contains article.tex and article.pdf, a README, verification code and results, and pinned provenance. The first article uses four additional numbered TeX files and one generated figure. The other articles are standalone TeX sources.

## Principal results

### 1. Universal recurrence avoidance

For every epsilon in (0,1), one closed symmetric 1-periodic set F has measure greater than 1-epsilon in every unit interval and omits infinitely many terms from every nonzero affine copy of every real sequence satisfying:

- It is not eventually zero.
- It decays exponentially.
- Eventually it satisfies a polynomial recurrence whose first and last coefficient polynomials have the common maximal degree.

The same F works for all such sequences and all orders and real parameters. In particular, it covers every stable constant-coefficient recurrence, including complex characteristic roots, repeated roots, exact cancellations, and infinitely many zero terms. Convergent C-finite sequences are covered after subtracting their limit, provided they are not eventually constant.

The proof selects nonzero coordinates of successive small recurrence states, then uses polynomial sign conditions to make finite routing uniform over the continuum of parameters. Countable compact exhaustion handles all balanced recurrences. The effective version gives an effectively closed set with computable measure; a practical blocker-construction program is not claimed.

### 2. A common parabolic density

For f(z)=exp(z)-1 and H(n,m)=n![z^n]f^m(z), let h be the positive Laplace density of the normalized entire Fatou orbit and I the existing compact-ratio Bell amplitude. The paper proves

    I(t) = t 2^(t/3) h(t),  t>0,

and consequently continues h holomorphically to Re t>0. It constructs finite positive coefficient measures whose Laplace limit identifies h and whose local coefficient limit identifies I. This fixes the normalization without comparing global contours.

The global-depth estimate is

    sum_m exp(-Lm) H(n,m)
      ~ (n!)^2 (2L)^(-n) n^(-1-L/3) L^(L/3-1) I(L).

It is uniform on positive compact L-intervals. For strict chains marked by q, L(q)=log(1+1/q), the identified amplitude is

    C(q) = (2L(q))^(L(q)/3) h(L(q))/(q+1).

This C extends holomorphically to Re q>0. At q=1 the formula identifies the existing Lengyel constant. Classical leading chain asymptotics are credited; their mere existence is not claimed as new.

The main implication explicitly imports four analytic statements from the pinned, unrefereed ProveIt Euler/Bell reports. Endpoint and chain-length corollaries state their additional source dependencies.

### 3. Tree-broadcast analytic threshold

For a rooted b-ary binary broadcast with fixed positive root, independent edge signs of mean theta, and level sum S_n, put X_n=(b theta)^(-n)S_n. The transforms

    exp(-Var(X_n) t^2/2) E exp(t X_n)

converge locally holomorphically near zero if and only if theta>b^(-3/4), for 0<theta<=1. The residue is jointly analytic in theta and t and convergence is exponential on compact parameter intervals.

The parity decomposition of the logarithm is decisive. Its odd part has contraction multiplier (b theta)^(-2); the remaining even part starts at degree four and has multiplier b/(b theta)^4. Explicit third- and fourth-cumulant divergences prove the converse, including the boundary.

The paper then proves all-order expansions in the depth window theta_n=b^(-1/2)exp(gamma/(2n)), full lattice local asymptotics, and an independent Fourier formula for majority success. At exact criticality on the binary tree,

    p_n = 1/2 + 1/sqrt(pi n) - 5/(4 sqrt(pi) n^(5/2)) + O(n^(-7/2)).

The n^(-3/2) term vanishes. Removing sufficiently many even cumulants also gives analytic renormalization for every theta>1/b.

## Proof and novelty status

These are research manuscripts with complete arguments for the new claims, not declarations of external peer review or worldwide priority. THEOREM_LEDGER.json records the statements and dependencies. REVIEW_NOTES.md records the internal mathematical checks and concrete limitations.

The avoidance routing method is inherited and reproved. The tree paper is self-contained and does not assume the factor-of-IID theorem that motivated its selection. The parabolic paper is an explicit implication from four named analytic interfaces in earlier unrefereed reports. None of the manuscripts is proof-assistant verified.

The papers identify genuine extensions or unresolved questions in the inspected snapshots. Their eventual assessment as breakthroughs, and priority relative to the entire literature, requires specialist review. Numerical agreement is never used as a proof of an analytic theorem.

## Reproduce

Required:

- Python 3.10 or later.
- SymPy for the parabolic exact coordinate check.
- TeX Live with latexmk and the standard packages loaded by the sources.

Optional:

- mpmath for the parabolic numerical diagnostics.
- Matplotlib for regenerating the signed-sampling illustration.

The requirements.txt file lists the Python packages. All verification programs are offline. From this top-level directory:

```sh
python3 reproduce.py --checks
python3 reproduce.py --pdfs
```

Running both options performs both actions. The commands overwrite only the recorded verification outputs and TeX build products. Optional numerical and figure commands appear in the individual READMEs. Their stored results and the figure are already included.

The exact suites were executed during preparation and all passed. A total scalar-check count across papers would obscure the different experiments; the reports retain their separate scopes:

| Article | Selected exact checks |
|---|---|
| Avoidance | 168 independent recurrence terms; 896 matrix-product terms; 2,184 sign comparisons; 51 boundary triples; 24 window cases; 65,536 routing event cases |
| Parabolic | 960 coefficient majorants; 144 Newton-basis evaluations; 96 rational geometric mixtures; Fatou defect through degree five |
| Tree broadcast | 392 exact scalar checks plus fixed-series checks through degree ten, with independent finite generating functions |

The parabolic inverse-Laplace runs are exploratory, not interval-certified. They agree to at least twelve decimal places at the four displayed arguments. The exact and numerical roles are distinguished in the article and receipts.

All three final PDFs were compiled and rendered for visual inspection. The final compilation logs had no warnings, undefined references, overfull boxes, or underfull boxes.

## Suggested integration

INTEGRATION_MAP.json gives suggested destinations. These are proposed locations for review, not a record of a committed repository change.

- Place the avoidance directory alongside the earlier uniform-geometric-avoidance report.
- Place the parabolic directory alongside the Euler, Bell, and strict-chain reports, and link the resolved question labels from those reports.
- Place the tree paper in a probability/tree-broadcast research directory; the suggested new path can be adapted to the repository's preferred taxonomy.

Retain entire article directories so that all relative TeX, code, data, and figure paths work. An editor can add cross-references to existing reports without altering the proved statements. Source pins preserve the baseline for each comparison.

The repository snapshots used were:

- openai/math: adc7f1241b42e322a6451854ab7e4b4c146bf78a
- VladimirReshetnikov/ProveIt: 58175ca45563d9ee29875374dd77942f069268a9

## Further research

The three articles contain 26 proposed research directions, each with motivation and a stated boundary. RESEARCH_QUESTIONS.json provides a selected machine-readable list for issue creation. Especially concrete next steps are:

1. Extend signed sampling to polynomially growing inverse-state norms.
2. Obtain usable size bounds or verified finite certificates for recurrence blockers.
3. Determine what parameter-complexity growth can replace the present subexponential condition.
4. Prove a Bell coefficient theorem uniform as n/m tends to zero and justify all-order depth summation.
5. Investigate complex zero-freeness and global marked-chain asymptotics.
6. Certify the common density and its derivatives numerically.
7. Determine the maximal complex domain and sharp convergence rates of the tree residue.
8. Classify higher even-cumulant thresholds and possible cancellations.
9. Compare majority with the full posterior in the finite-depth critical window.

These are proposed targets; the package does not certify that every formulation is absent from the wider literature.

## Attribution and integrity

THIRD_PARTY_NOTICES.txt and third_party/ retain attribution and license information for the inherited OpenAI routing construction. Original repository articles are linked by immutable source references rather than duplicated in full. Each article credits the primary literature it uses.

SHA256SUMS records the bytes in this package before compression. The PDFs are readable deliverables; the TeX and scripts are the editable and reproducible sources.
