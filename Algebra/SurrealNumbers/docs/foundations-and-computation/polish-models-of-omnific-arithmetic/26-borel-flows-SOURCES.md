# Sources and inspection record

Reviewed on 4 October 2026. Only primary research and the user's own
repository/research artifacts support the literature discussion. Search
results unrelated to the mathematical question were not used.

## Published/preprint research

1. Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699v1 (2023).
   https://arxiv.org/abs/2311.13699
   https://arxiv.org/pdf/2311.13699
   Inspected abstract and paper text, including its theorem hypotheses and
   the discussion of remaining foundational questions. Used to identify the
   mathematical research intersection, not as an assumed theorem about
   series-field flows.

2. Vincent Bagayoko, Lothar Sebastian Krapp, Salma Kuhlmann, Daniel Panazzolo,
   Michele Serra, *Automorphisms and derivations on algebras endowed with
   formal infinite sums*, arXiv:2403.05827v2 (revision 22 September 2025).
   https://arxiv.org/abs/2403.05827
   https://arxiv.org/pdf/2403.05827
   Inspected abstract, introduction, and formal-summability/contracting-map
   context. The existing exponential and BCH mechanisms are credited to this
   theory; this manuscript's counterexample concerns the smaller left-finite
   support class and does not refute the cited results.

3. Vincent Bagayoko, *A formal Lie correspondence*, arXiv:2604.04224v1
   (5 April 2026).
   https://arxiv.org/abs/2604.04224
   https://arxiv.org/pdf/2604.04224
   Inspected abstract, introduction, and scope of formal nilpotence. Its
   existence is recorded to avoid presenting general formal Lie
   correspondence as new.

## ProveIt and the prior research question

Repository:
https://github.com/VladimirReshetnikov/ProveIt

The root README and the research catalogue were inspected on the moving
branch before a later exact commit was pinned. The relevant catalogue is:
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic

The prior standalone report is:
*Borel Regularity Forces Summability: Automatic continuity and measurable
derivations on left-finite series fields*, AI-assisted manuscript dated
4 October 2026, 24 pages, `borel_summability.pdf`.
It was retrieved from the user's Library and inspected for its abstract,
Section 10 positive-gain flow discussion, and the complete further-research
section on PDF pages 21-23. Its Question 13.5 asks about flows without
uniform positive gain and the need for analytic time regularity. The new
paper settles this question for countable divisible real exponent groups.
The catalogue places the prior report as source 23 / Part XVII.
The entire large merged report was not audited.

## Exact repository source pin

Commit:
c39974f12a45c8795575ab222f3b84b2901c394f

Commit tree:
dbbe29a67da59205e50a264c58a9bc3731d761ec

Inspected source:
Algebra/BakerCampbellHausdorff/Lean/BCH/Formal/Trunc.lean

Source blob:
5f238ed2f05b54e940e51f974465768c0dc23ba7

https://github.com/VladimirReshetnikov/ProveIt/blob/c39974f12a45c8795575ab222f3b84b2901c394f/Algebra/BakerCampbellHausdorff/Lean/BCH/Formal/Trunc.lean

Lines 1-130 were read, including the truncated free-algebra representation
and its coefficient-recovery declarations. No Lean build or audit of the
entire BCH development was performed. This source supplies a prospective
formalization interface, not a formal proof of the new theorems.

## Profile access and novelty limits

The supplied LinkedIn profile could not be fully read. No current role,
affiliation, or personal research preference is inferred from unavailable
profile content. The intersection is supported by Glazer's own paper.

Searches also combined 'Borel representations countable-dimensional',
'Levi-Civita one-parameter automorphisms', and 'Levi-Civita derivations
locally exponential'. No priority conclusion follows from failure to find
an exact match. The new theorem package is proposed for specialist review;
no independent novelty certification is claimed.
