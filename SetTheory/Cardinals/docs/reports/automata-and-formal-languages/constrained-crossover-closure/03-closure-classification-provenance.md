# Provenance and bounded novelty audit

Prepared 30 September 2026 for the user's request to extend topics in ProveIt with substantial proved results and a research article.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected revision: `b8b0fa2184a044d46ce9ed0f25f88d7bb60fa042`.

The GitHub connector was used to inspect the recursive tree, the research-report collection README, and the source and README of:

`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/constrained-crossover-closure/`

Predecessor title: *Aligned Fragments and Constrained Crossover: Undecidability, exact generation depth, and rational growth of context-free recombination closures*, 29 September 2026.

The preceding report states coordinate-hull and aligned-rank theorems, one-step CFG undecidability, eventual stabilization undecidability, regular-input procedures, rational commutative counting, and a linear seed with non-context-free closure and unbounded depth. Those statements are not claimed as new here. The coordinate-hull fact is reproved, and the sparse generation theorem has a direct independent proof.

The repository's source/README describes its own work as unrefereed and unformalized. Its placement in ProveIt confers no proof-assistant status on this manuscript. No repository files were changed.

## Research contribution relative to that source

The proposed extensions are global full-closure regularity and comparison via Presburger row types; Boolean-combination length theory; the complete sparse one-marker classification; exact clique depth; regular endpoint-ray realization of arbitrary graphs; and the explicit depth-one slender non-context-free fixed point.

The full-closure regularity question is a natural continuation, not asserted to be a specifically numbered open question in the preceding report. Hughes's explicit one-step question is credited as the preceding report's target, not claimed as first solved again.

## Primary literature inspected or bibliographically verified

- Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*, arXiv:2608.27755v1, 27 August 2026. https://arxiv.org/abs/2608.27755 . The PDF definition and the open-question page were visually inspected. The operation is aligned equal-length suffix exchange with endpoint cuts permitted.
- Rohit J. Parikh, *On Context-Free Languages*, JACM 13(4), 570–581 (1966). https://doi.org/10.1145/321356.321364 . Effective semilinear support is a classical ingredient, not a new result.
- Javier Esparza, Pierre Ganty, Stefan Kiefer, Michael Luttenberger, *Parikh's theorem: A simple and direct automaton construction*, IPL 111(12), 614–619 (2011). https://doi.org/10.1016/j.ipl.2011.03.019 . Constructive Parikh reference.
- Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger formulas, and languages*, Pacific J. Math. 16(2), 285–296 (1966). https://doi.org/10.2140/pjm.1966.16.285 . Semilinear/Presburger background.
- Pablo Barceló, Chih-Duo Hong, Xuan-Bach Le, Anthony W. Lin, Reino Niskanen, *Monadic Decomposability of Regular Relations*, ICALP 2019. https://doi.org/10.4230/LIPIcs.ICALP.2019.103 . The global row-type mechanism is a monadic-decomposition application.
- Matthew Hague, Anthony W. Lin, Philipp Rümmer, Zhilin Wu, *Monadic Decomposition in Integer Linear Arithmetic*, IJCAR 2020, 122–140. https://doi.org/10.1007/978-3-030-51074-9_8 ; extended report https://arxiv.org/abs/2004.12371 . Its complexity statements are not transferred without accounting for representation conversion.
- Moses Ganardi and Marin Ricros, *Constructing Small Monadic Decompositions in Presburger Arithmetic*, LICS 2026, LIPIcs 380, 47:1–47:22. https://doi.org/10.4230/LIPIcs.LICS.2026.47 . Primary Dagstuhl page verified the 9 July 2026 publication and general decomposition-size lower bound. Cited to avoid implying small synthesized representations.
- Danny Raz, *Length considerations in context-free languages*, TCS 183(1), 21–32 (1997). https://doi.org/10.1016/S0304-3975(96)00308-8 . Primary author-institution record documents the paired-loop/slender-language background. Our finite-gap-ray lemma is presented as a specialized elementary argument, not a new general characterization of slender CFLs.
- Richard M. Karp, *Reducibility among Combinatorial Problems*, 85–103 (1972). https://doi.org/10.1007/978-1-4684-2001-2_9 . Classical CLIQUE hardness, imported rather than reproved.
- J. Barkley Rosser and Lowell Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6(1), 64–94 (1962). https://doi.org/10.1215/ijm/1255631807 . Used only to justify polynomial-bit and polynomial-time prime selection in the graph encoding.

## Limits

This is a bounded, topic-focused literature audit, not an exhaustive priority search. Monadic decomposition and paired-loop descriptions are established background. Equivalent sparse-recombination formulations may exist in other language, splicing, or recombination literature. The article's proposed originality is the exact combination and specialization of the crossover criteria and constructions, supported by complete written proofs. No claim of solving the general context-freeness problem for arbitrary Presburger hulls or the optimal explicit-DFA stabilization complexity is made.

The final article and code were generated in the working container. The exact finite verifier was run, and the PDF was compiled, rendered, and visually checked. No Lean or Rocq build was attempted.
