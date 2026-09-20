# Source and novelty audit

Checked on 20 September 2026. This records the scope of the source review;
it is not an exhaustive literature or priority determination.

## Primary target

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite
Automata with Output*, arXiv:1705.07150v2, 17 October 2017.

- Abstract/metadata: https://arxiv.org/abs/1705.07150
- Version-specific HTML: https://arxiv.org/html/1705.07150v2
- Version-specific PDF: https://arxiv.org/pdf/1705.07150v2

Locations actually checked:

1. Section 5, Problem 1, printed PDF page 17: asks whether the k^n upper
   bound is reachable over a binary input alphabet for k≥3, conjecturing no.
2. Proposition 4: orbit characterization of reversal complexity for an
   accessible/trim source machine.
3. Corollary 2: ternary attainability.
4. Theorem 3 and Corollary 3: the coprime-block lower construction for k<n.
5. Section 5, Problem 2: conjectural optimality of that lower construction
   for n≥7. It is distinct from Problem 1.
6. Printed PDF page 13, Table 2: the n=8,k=5 number is visibly 368020.
   The formula in the same paper yields 369020, and two implementations
   independently verify a 369020-state coloring orbit. The PDF page was
   inspected as an image, so the discrepancy is not attributed to HTML parsing.
7. Printed PDF page 17, Table 3: bold entries are the source's exhaustive
   maxima; nonbold entries are described there as random-search results.

## Earlier transformation-monoid work

Markus Holzer and Barbara König, *On deterministic finite automata and
syntactic monoid size*, Theoretical Computer Science 327(3), 319–347 (2004).
DOI: https://doi.org/10.1016/j.tcs.2004.04.010

An author-uploaded full-text rendering was inspected at:
https://www.researchgate.net/publication/226652130_On_Deterministic_Finite_Automata_and_Syntactic_Monoid_Size

Important attribution points:

- Theorem 13 includes the classical two-generator transformation-monoid
  upper bound n^n−n!+g(n). The present main bound specializes to it when k=n.
  That special case is not claimed as new.
- Sections 4–5 use graph colorings and chromatic polynomials in the
  transformation-monoid setting. Graph coloring as a method is not claimed
  as an invention of this note.
- The proposed contribution is the output-relabeling/cyclic-orbit obstruction
  for k<n, its constructive version, and the accompanying derived extensions
  and structural bounds. These still require independent expert assessment.

## Search scope and limitations

Searches included the exact target title and arXiv identifier; combinations
of “DFAO”, “binary”, “reversal”, “output”, and “conjecture”; and later-year
searches. The results inspected did not identify a later resolution of the
selected first problem. Some broad matches were unrelated and were not used
as evidence. The 2018 conference publication was surfaced in bibliographic
results, but the mathematical source used here is the identified arXiv v2.

Absence of a located later resolution is not proof of novelty. No claim is
made that the literature search rules out an unpublished solution, a result
under different terminology, or an inaccessible later treatment.

## Dependency boundary

The main k^n−k!+g(k) theorem, constructive algorithm, abelian-group extension,
and structural upper bound are proved in the article without external
classification theorems. The reversal construction and ternary attainability
are also reproved.

The finite exact-optimality comparison uses Davies's lower-bound existence
result together with the independently derived upper formula. Its 372
parameter pairs are checked by two separately implemented arithmetic
procedures. Some individual lower witnesses are also verified directly by
independent BFS implementations. No full proof-assistant formalization or
independent refereeing is claimed.

No third-party PDF, source manuscript, or font files are redistributed in
this archive. The bibliography links to the original sources.
