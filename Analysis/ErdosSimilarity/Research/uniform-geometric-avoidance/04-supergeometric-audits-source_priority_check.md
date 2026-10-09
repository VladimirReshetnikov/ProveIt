# Focused priority check: unbounded logarithmic gaps

Checked 2026-10-08 using primary arXiv sources, the OpenAI repository
snapshot, and targeted recent searches (30-day and 365-day windows).

## Scope

I found no primary source proving nonuniversality of each fixed
a_n=exp[-n(loglog n)^alpha], 0<alpha<1, or the general criterion
liminf G_N/loglog N=0 with a_{n+1}/a_n<=mu<1.
This is a limited search and cannot establish universal priority.

The extension is not merely the bounded-ratio result: these examples
have a_{n+1}/a_n->0 and no infinite bounded-ratio subsequence.
Do not describe all supergeometric sequences as solved.

## Direct antecedent and repo comparison

OpenAI: "The geometric case of the Erdos similarity conjecture,"
Oct5 2026. Commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/sections/01-introduction.tex

The statement is one fixed ratio q at a time and excludes no
supergeometric sequence. Its local random-routing mechanism is the
direct antecedent and should receive prominent attribution.
Its Lean scope page only specifies the dyadic case.

The ProveIt source inspection included
Analysis/ErdosSimilarity/Research/uniform-geometric-avoidance/sections/06_algebraic_families.tex,
where the singleton polynomial family already handles arbitrary fixed
bounded-ratio sequences. Do not claim bounded-ratio novelty.

## Recent primary papers checked

1. A. Iosevich, N. Kulkarni, N. Mora Cuellar, I. Rojas Aravena, A. Yavicoli:
"The Erdos similarity conjecture and Rajchman measures,"
arXiv:2609.04456v1 (submitted Sep3 2026).
https://arxiv.org/html/2609.04456v1

Latest original source inspected, not merely search snippet.
Its Theorem1.5 requires a Rajchman probability supported on A.
Proposition4.1 proves such supports are atomless, uncountable, and
perfect (HTML lines440-470), so it does not apply to our countable A.
A separate geometric criterion in Proposition3.2 treats sets whose
large dilates become uniformly dense modulo one. Remark3.3 gives a
countable example with finite arithmetic grids, not superlacunary A.
No logarithmic-gap criterion of our form occurs.

2. N. Mora Cuellar, A. Iosevich, N. Kulkarni, I. Rojas Aravena, A. Yavicoli:
"The Erdos Similarity Conjecture for Two-Fold Sumsets with a Geometric
Summand," arXiv:2607.03584v2 (revised Aug1 2026).
https://arxiv.org/abs/2607.03584
Source page confirms exact current title/version; one search index
returned its previous broader title, so use the direct page.

Theorem: geometric/lacunary exponential-order summand plus arbitrary
infinite set is nonuniversal. Counting-function tradeoff also covers
certain sums/differences of two stretched exponential sequences.
This is a sumset result. It does not assert nonuniversality of one
constituent sequence, and explicitly says its result applies even
though the single geometric case was open before the Oct release.

3. A. Iosevich, A. Yavicoli:
"Falconer lattice sets and the Erdos similarity problem,"
arXiv:2604.01493v1 (Apr2 submission; HTML manuscript date Aug24 2026).
https://arxiv.org/html/2604.01493

Uses nested lattice structure to force a triple sumset inside an
uncountable thin Cantor set; Bourgain then gives nonuniversality.
Lemma2.4 exhibits a fast sequence a_i=1/q_i, ratio->0, INSIDE the
uncountable set. This does not make the sequence itself nonuniversal.
No result matches our fixed single-sequence criterion.

4. P. Shmerkin, A. Yavicoli:
"Full measure universality for Cantor Sets,"
arXiv:2503.21079v2 (revised Dec19 2025).
https://arxiv.org/abs/2503.21079

Results concern Cantor sets under logarithmic dimension assumptions,
and a weaker almost-everywhere statement for all Cantor sets.
Our countable null sequence falls outside those Cantor/dimension
hypotheses. The logarithmic dimensions here are dimensions of the
pattern, not the maximum adjacent logarithmic gaps G_N.

5. W. Li, Z. Wang, J. Xu:
"On the Eigen-Falconer theorem in R^d,"
arXiv:2512.02146 (Dec1 2025).
https://arxiv.org/abs/2512.02146

Vector norm ratios tend to1. It is a higher-dimensional slow-decay
theorem, not applicable to our ratios tending to0.

## Older primary/method references

6. Y. Jung, C.-K. Lai, Y. Mooroogen:
"Fifty years of the Erdos similarity conjecture,"
arXiv:2412.11062v2, Jan1 2025.
https://arxiv.org/html/2412.11062v2

Sections1.1 and2 discuss slow and fast decreasing sequences.
Lines61-87 give Eigen-Falconer and Kolountzakis finite-gap criterion.
Use as historical background, not as current Oct2026 status alone.

7. M. N. Kolountzakis, "Infinite patterns that can be avoided by measure,"
Bull. London Math. Soc.29 (1997), 415-424.
https://doi.org/10.1112/S0024609397003056

8. M. Chlebik, "On the Erdos similarity problem,"
arXiv:1512.05607v1, Dec17 2015.
https://arxiv.org/abs/1512.05607

The translated normalized-minimum-gap criterion requires
-log(min gap/diameter)=o(m). For any uniformly lacunary sequence,
every m-point subset has min gap/diameter <=mu^(m-2)/(1-mu);
therefore our examples cannot satisfy this route.

## Misleading search hit checked and excluded

Cruz--Lai--Pramanik, "A proof of the Erdos similarity conjecture,"
arXiv:2001.02395.
https://arxiv.org/abs/2001.02395

The current source explicitly states a gap in Proposition3.3 and
withdraws the paper (Jan11 2020). Do not cite it as a proof or as
contradicting the novelty/status description.

## Suggested article language

"We extend the finite routing construction beyond bounded logarithmic
gaps. Under ... [precise theorem] ... . Neither the checked OpenAI
geometric manuscript nor the earlier ProveIt bounded-ratio and
finite-family extension contains this criterion. A focused search of
the primary literature listed here found no theorem covering these
individual supergeometric examples. The general similarity conjecture
and faster-decay examples remain outside the result."

Avoid "first ever" or "the literature proves this was open on Oct7"
unless independently verified by a specialist.

## Search phrases and filters

- "Erdos similarity" supergeometric (365 days)
- "Erdos similarity" sequence logarithmic (365 days)
- "Erdos similarity" ratios (30 days)
- "Erdos similarity" "super" logarithmic gaps (365 days)
- "Erdos similarity" "loglog" sequence (365 days)
- "similarity conjecture" "log log n" (365 days)
- "similarity problem" "supergeometric" (365 days)
- "Erdos" "bounded logarithmic gaps" (365 days)

Many exact-phrase searches returned no relevant primary hit. Recent
relevant results were checked at their original arXiv pages above.

