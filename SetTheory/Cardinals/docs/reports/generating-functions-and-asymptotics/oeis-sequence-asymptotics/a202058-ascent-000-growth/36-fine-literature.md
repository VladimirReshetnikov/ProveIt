# A202058 fine asymptotics: literature and overlap audit

Checked 2 October 2026 (UTC). Read-only external research. This is a scoped search, not an exhaustive novelty certificate.

## Finding

No retrieved primary source supplies a proved full asymptotic equivalent, ratio limit, power prefactor, logarithmic prefactor, or stretched-exponential correction for A202058. The main primary source leaves the subexponential factor unresolved. The private root-limit proof supplied for this project goes beyond the published root-constant conjecture; that private proof is not external literature and does not by itself determine the finer factor.

## Exact object and indexing

Let `asc(x_1...x_j)` count indices `i<j` with `x_i<x_(i+1)`. An ascent sequence has `x_1=0` and `0<=x_i<=1+asc(x_1...x_(i-1))` for `i>=2`. Classical pattern `000` occurs precisely when one value occurs in three positions, not necessarily consecutive. Thus A202058 counts precisely the ascent sequences in which every value occurs at most twice. The empty sequence contributes `a_0=1`.

The OEIS entry gives offset 0 and initial values `1,1,2,4,10,27,83,277,1015,4007,17047`; it identifies this sequence as column `k=2` of A294220. Its retrieved text contains no asymptotic formula and says no formula or generating function is known. It links Conway's table through 176 and the 2021 preprint. The search renderer reports an old cache date even though the displayed site footer says September 2026; the footer is not an entry-revision timestamp. Direct opening failed, but the OEIS-domain search returned the entry text.

Sources: [A202058](https://oeis.org/A202058), [A294220](https://oeis.org/A294220). The conventional ascent-sequence and pattern definitions are also stated on pp. 1–2 of [Liu–Kitaev–Zhang, arXiv:2604.06735v2](https://arxiv.org/pdf/2604.06735v2).

## Main asymptotic source

Andrew R. Conway, Miles Conway, Andrew Elvey Price, Anthony J. Guttmann, *Pattern-Avoiding Ascent Sequences of Length 3*, Electronic Journal of Combinatorics **29**(4) (2022), P4.25, DOI [10.37236/11266](https://doi.org/10.37236/11266); [published PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/), [arXiv:2111.01279](https://arxiv.org/abs/2111.01279).

- Sections 2.2 and 2.6 give the enumeration recurrence and its compression.
- Section 5, pp. 18–19, reports numerical analysis using coefficients through `O(x^395)`. It conjectures `a_n ~ C n! mu^n mu_1^(n^sigma) n^g`, with `mu=8/(3*pi^2)` and an estimated `0.06<=sigma<=0.1`. Neither `mu_1` nor `g` is estimated.
- The introductory expression `C n! mu^n` on p. 3 must not be presented as an established full equivalent: Section 5 explicitly retains the unresolved factors.
- The rigorous elementary bound there is `a_(2n)>=n!`, proving zero ordinary radius but not the exponential-generating-function radius.

Consequently, this paper supplies a numerical hypothesis for the fine scale, not a theorem fixing it. In particular, its interval for `sigma` is not a rigorous exclusion of logarithmic corrections or pure powers.

## Later or adjacent primary sources checked

1. David Callan and Toufik Mansour, *Ascent Sequences Avoiding a Triple of Length-3 Patterns*, EJC **32**(1) (2025), P1.40, DOI [10.37236/12720](https://doi.org/10.37236/12720), [PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i1p40/pdf/). Its classes containing `000` also impose other forbidden patterns. These are proper subclasses; their rational/Catalan-type enumerations do not solve the single-`000` problem.
2. Qi Liu, Sergey Kitaev, Philip B. Zhang, *Simultaneous avoidance of length-4 patterns in ascent sequences*, [arXiv:2604.06735v2](https://arxiv.org/abs/2604.06735v2), revised 25 September 2026. It treats subsets of `0101,0102,0112,0120,0121`, not the sole `000` restriction. Its discussion also warns that transport of patterns through modified ascent sequences does not automatically produce ordinary-ascent-sequence avoidance classes.
3. *Generating trees growing on the left for pattern-avoiding inversion sequences*, [DMTCS PDF](https://dmtcs.episciences.org/16563/pdf). Its `000`-avoidance results concern inversion sequences, a different class. The ascent restriction depends on preceding ascents, not just the position.
4. Hsien-Kuei Hwang and Emma Yu Jin, *Asymptotics and statistics on Fishburn matrices and their generalizations*, JCTA **180** (2021), 105413, DOI [10.1016/j.jcta.2021.105413](https://doi.org/10.1016/j.jcta.2021.105413), [arXiv:1911.06690](https://arxiv.org/abs/1911.06690). This supplies powerful saddle-point asymptotics for particular sum-of-finite-products generating functions, but no identified multiplicity-preserving correspondence or applicable generating function for A202058. Its general Fishburn results cannot simply be imported here.

## ProveIt default-branch check

The authorized GitHub connector returned default branch `main` for [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt). Fresh default-branch code searches on 2 October 2026 returned:

- No results: `A202058`, `A294220`, `000-avoiding`, `Fishburn`, `0.2701898`
- `ascent`, `ascent sequence`, and `ascent sequences`: only unrelated permutation-ascents or algebraic-order material
- `bounded multiplicity`: unrelated analytic zero-multiplicity, polynomial, partition, and adjacency-bounded-permutation material
- `3pi`: one unrelated trigonometric branch check in an A290268 calculation

The returned indexed links used commit `13ef7d939f5eb007c2f409d622ac05f1efb7cda9`, newer than the index observed in the previous audit. Representative unrelated hit: [adjacency-bounded 132-avoiders README at that commit](https://github.com/VladimirReshetnikov/ProveIt/blob/13ef7d939f5eb007c2f409d622ac05f1efb7cda9/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/README.md).

These searches found no direct duplication or usable fine-asymptotic result. This is indexed keyword-search evidence, not a complete semantic audit of the repository or a verified assertion that the indexed SHA equals the live branch tip.

## Search scope and limits

Searches included the sequence IDs; exact `000-avoiding ascent sequences`; ascent sequences with bounded multiplicity, multiplicities, or at most twice; the decimal/root constant; and 2023–2026 restrictions. Primary papers, publisher records, arXiv, OEIS, and the authorized GitHub code search were used for substantive claims. Results for weak, modified, difference, or inversion sequences were not conflated with ordinary ascent sequences. No external files, branches, issues, comments, or publications were created or modified.
