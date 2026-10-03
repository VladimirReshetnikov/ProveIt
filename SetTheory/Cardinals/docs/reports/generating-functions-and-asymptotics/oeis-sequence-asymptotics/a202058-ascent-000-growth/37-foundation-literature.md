# Literature and duplication status

Checked 1 October 2026. This is a scoped search, not an exhaustive novelty certificate. No external state was changed.

## Primary source

Conway, Conway, Elvey Price, Guttmann, Pattern-Avoiding Ascent Sequences of Length 3, Electronic Journal of Combinatorics 29(4) (2022), P4.25, DOI 10.37236/11266. https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/ ; arXiv https://arxiv.org/abs/2111.01279 . Sections 2.2 and 2.6 establish the exact compacted recurrence. Section 5 explicitly conjectures the factorial exponential constant 8/(3*pi^2), with an unresolved possible stretched factor and estimated exponent between .06 and .1. Its rigorous lower bound is only a_(2n)>=n!.

## OEIS

Direct main/internal/API downloads initially failed. A domain-specific web search then returned the OEIS entry itself, with the full entry text: https://oeis.org/A202058 . It says no formula or generating function is known, links the Conway table through 176 and arXiv2111.01279, and identifies the sequence as column k=2 of A294220. The search renderer labels its cached crawl as old while the displayed site footer is September 2026; do not treat that footer as proof of the entry revision date. No later asymptotic theorem appears in the retrieved entry. Initial values through 20 agree with the independently implemented exact recurrence, and direct enumeration checks through 10.

## Later material inspected / excluded

The 2025 EJC paper on ascent sequences avoiding triples of length 3 patterns (EJC 32(1),P1.40; https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i1p40/pdf/) contains 000 together with additional restrictions, not a solution of the unrestricted single-000 problem. Searches for exact sequence ID, 000-avoiding ascent sequences, bounded multiplicities, the quoted growth constant, and later 2024–2026 work did not find a subsequent proof.

The 2026 work on generating trees growing on the left for inversion sequences (https://dmtcs.episciences.org/16563/pdf) concerns a different class: 000-avoiding inversion sequences are enumerated by Euler up/down numbers. Its known EGF does not apply to ascent sequences. Likewise, Fishburn matrices with row sums<=2 are a different class: their counts 29,97 at sizes 5,6 disagree with 27,83 here. No multiplicity-preserving Fishburn bijection has been assumed.

## ProveIt default branch

Authorized GitHub connector confirmed VladimirReshetnikov/ProveIt has default branch main. Default-branch code searches for A202058, 000-avoiding, and bounded multiplicity ascent each returned no results. Previous broader source checks are documented in the same-session screening material. These are scoped negative search results, not a complete semantic nonduplication proof. Repository https://github.com/VladimirReshetnikov/ProveIt .

Additional default-branch searches for Fishburn and 3pi^2/8 returned no matches. The broad query ascent sequences returned only unrelated excerpts about permutation ascents and general sign sequences. These indexed results linked commit 0870c19bb79385e0ca68a695c81e860780e4b968. This remains scoped search evidence rather than a repository-wide semantic proof.
