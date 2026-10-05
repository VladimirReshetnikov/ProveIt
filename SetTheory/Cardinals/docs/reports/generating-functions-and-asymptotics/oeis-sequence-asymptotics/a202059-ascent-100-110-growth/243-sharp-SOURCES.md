# Sources and mathematical scope for Report243

Prepared 5 October 2026. This is a bounded source comparison, not an exhaustive bibliography or priority certificate. No third-party paper, private review, or account identifier is redistributed in this package.

## Ordinary ascent sequences

The model is x_1=0 and 0<=x_i<=1+asc(x_1,...,x_(i-1)), with strict adjacent ascents. The entering edge is excluded when checking the current entry. Patterns are arbitrary subsequences, with literal equality and order. The package does not concern weak ascents, contiguous factors, general inversion sequences, or restricted-growth words.

- A202059: https://oeis.org/A202059, ordinary 100 avoidance, offset 0
- A202060: https://oeis.org/A202060, ordinary 110 avoidance, offset 0
- No OEIS ID is assigned here to simultaneous 000/100 avoidance

Andrew R. Conway, Miles Conway, Andrew Elvey Price, and Anthony J. Guttmann, Pattern-Avoiding Ascent Sequences of Length 3, Electronic Journal of Combinatorics 29(4) (2022), P4.25.

- DOI: https://doi.org/10.37236/11266
- Final PDF: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/
- Sections 2.3 and 2.4 give the actual 100 and 110 recurrences, used in exact_counts.py
- The final abstract reverses their algorithm-efficiency labels; the package follows the actual sections
- Section 7 uses a doubled increasing seed. That idea is credited, not claimed as new
- The former fractional-factorial conjecture was already addressed in Report241; it is not presented as a second new correction in Report243

David Callan and Toufik Mansour, Ascent sequences avoiding a triple of length-3 patterns, Electronic Journal of Combinatorics 32(1) (2025), P1.40.

- DOI: https://doi.org/10.37236/12720
- PDF: https://emis.de/ft/35384
- Table 2, Class 36, lists {000,100,110} and its finite prefix
- The public source_prefixes.json preserves these source counts with URLs
- This classification is not used as an asymptotic theorem

Andrew M. Baxter and Lara K. Pudwell, Ascent sequences avoiding pairs of patterns, Electronic Journal of Combinatorics 22(1) (2015), P1.58.

- Preprint: https://arxiv.org/abs/1406.4100
- Its inspected Table 2 lists 16 solved representative pairs and does not give the present {000,100} result
- This is a specific checked comparison, not a claim that every pair-pattern source was searched

## Historical triangular enumeration and its exact model

For positive-diagonal upper-triangular nonnegative matrices of total weight n and dimension r, subtract one from each diagonal cell. The remaining n-r units occupy r(r+1)/2 cells, giving

T(n,r)=binom(r(r+1)/2+n-r-1,n-r).

The total b_n=sum_r T(n,r) counts the self-modified ordinary ascent model. With the current OEIS offset, b_n=A098569(n-1) for n>=1, not A098569(n).

Mireille Bousquet-Melou, Anders Claesson, Mark Dukes, and Sergey Kitaev, (2+2)-free posets, ascent sequences and pattern avoiding permutations, Journal of Combinatorial Theory, Series A 117 (2010), 884-909.

- DOI: https://doi.org/10.1016/j.jcta.2009.12.007
- PDF: https://arxiv.org/pdf/0806.0666
- Section 4.1 gives the standard modification algorithm
- Section 4.4, Propositions 10-11, gives the self-modified model and exact enumeration
- Its unrestricted Fishburn asymptotics are not transferred to this subclass

Mark Dukes and Peter R. W. McNamara, Refining the bijections among ascent sequences, (2+2)-free posets, integer matrices and pattern-avoiding permutations, Journal of Combinatorial Theory, Series A 167 (2019), 403-430.

- PDF: https://arxiv.org/pdf/1807.11505
- Definitions 3.1 and 3.3, Lemmas 3.2 and 3.4, and Proposition 3.6 supply the maximal-ascent and positive-diagonal correspondence
- These exact bridges are prior results, distinct from this report's many-to-one comparisons

B. I. Bayoumi, M. H. El-Zahar, and S. M. Khamis, Asymptotic enumeration of N-free partial orders, Order 6 (1989), 219-225.

- DOI: https://doi.org/10.1007/BF00563522
- Lemmas 2-4 and the displayed multiplicity substitution supply exact interval-subclass antecedents
- The stated asymptotic theorems concern the larger covering-graph N-free class, not a relative equivalent for this selected triangular model
- The correct page range is 219-225; a later reference gives a different range

S. M. Khamis, Height counting of unlabeled interval and N-free posets, Discrete Mathematics 275 (2004), 165-175.

- DOI: https://doi.org/10.1016/S0012-365X(03)00106-7
- Institutional record: https://research.asu.edu.eg/handle/123456789/1124
- Lemma 4.1 and Theorem 4.2 enumerate the rigid model and the multiplicity substitution
- N-freeness is defined through the directed covering graph, not induced-subposet N avoidance
- Removing the forced zero first column and last row converts the block matrix's positive superdiagonal to a triangular table's positive diagonal; the block matrix has one extra row

OEIS model record: https://oeis.org/A098569. The source review used the official record with the 29 October 2023 offset change. Exact enumeration and older coarse logarithmic work are not presented as new.

## What is proved here and what is inherited

Report241, Factorial Logarithmic Growth of Pattern Avoiding Ascent Sequences, 5 October 2026, is the earlier companion report. Its occurrence-marking, monotone marked labels, run subsets, and Vandermonde method are acknowledged. Report243 retains the exact run index, bounds skeletons subexponentially on the relevant range, and excludes the large-repeat tail separately.

The new lower comparison in this report is explicitly proved: positive triangular rows are decoded by an actual stars-and-bars rank bijection; empty rows are repaired after an expectation/Markov estimate; repair, boundary-decoration, and padding fibers are bounded separately. A translated doubled seed gives a common-class lower bound. Every asymptotic conclusion rests on finite inequalities and the article's own elementary triangular localization proof.

Sharp conclusions: log u_n=n(log n-2 log log n+log 2-1)+O(n(log log n)^2/log n) for u=a or e, and normalized-root limit 2. For 110 and the common class, only lower/upper constant brackets -log 2-1 and log 2-1 are proved; existence or equality is not claimed. The first-crossing inverses have diverging absolute remainders. No exact rounding rule or relative counting equivalent is claimed.

Standard modification is not a substitute for the proved comparisons: 0101 avoids both 100 and 110 but modifies to 0201, which is not an ordinary ascent sequence. Self-modified 0110 contains 110, and self-modified 0100 contains 100.

The code checks finite instances, not asymptotic truth by numerical fitting. The package does not claim external peer review, proof-assistant verification, exhaustive novelty clearance, or publication.
