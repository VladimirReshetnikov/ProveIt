# Sources and novelty audit

Inspected for this manuscript on 28 September 2026.

## Pinned repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: `2cdcd74f3abcbbff7bd47c6c4265522395def609`

Target directory:
`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/`

Inspected through the GitHub connector:

- `README.md`: reported nonattainment bound, collision-graph bounds,
  computational agreement for 7 <= n <= 30 and 3 <= k < n, and limits of claims.
- `RESEARCH_STATUS.md`: explicit non-claim of arbitrary-n exact optimality.
- `code/reversal.py`: available portions through the complete structural-bound
  and Davies-lower-bound functions, including exact order sets and H(r,t).
  The returned file content was truncated later; this was not a full audit of
  every function or of the entire merged article.
- General Cardinals/reports README and the available manifest portion:
  consulted for topic selection, not a proof audit of the full collection.

The paper rederives every upper-bound ingredient it needs. It does not treat
repository membership as proof-assistant certification.

## Primary literature

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite Automata
with Output*, arXiv:1705.07150v2 (17 October 2017):
https://arxiv.org/abs/1705.07150
https://arxiv.org/pdf/1705.07150v2

Checked locations (printed pages, one greater than zero-based PDF indices):

- Proposition 4, page 6: reversal size as the coloring orbit.
- Page 7: definition of U_(a,b), two-generation attribution, and generators.
- Theorem 3, pages 9–12: proper-coloring count and cyclic correction.
- Corollary 3, page 12: attainable binary lower bound over coprime splits.
- Section 5, Question 2, page 17: optimality for n >= 7.

The PDF image of printed page 17 was inspected. We do not rely on a random
search table entry as an extremal proof.

Markus Holzer and Barbara König, *On deterministic finite automata and
syntactic monoid size*, Theoretical Computer Science 327(3), 319–347 (2004):
https://doi.org/10.1016/j.tcs.2004.04.010
https://www.sciencedirect.com/science/article/pii/S0304397504004840

Publisher metadata and abstract were checked. The relevant Theorem 8
attribution and its exact applicability are checked in Davies's primary
paper; the full Holzer–König proof is not independently reproduced or audited
here. The much stronger extremal-monoid assertions are not imported.

## Targeted search terms

- "DFAO" "reversal" "optimal"
- "DFAO" "reversal" "asymptotic"
- "DFAO" "reversal" "2025"
- "State Complexity of Reversals of Deterministic Finite Automata with Output"
- "State Complexity of Reversals" 2025 2026
- "On deterministic finite automata and syntactic monoid size" Holzer König 2004

No later resolution was located in these searches. Search-engine coverage
and wording are limited; non-discovery establishes no priority. The precise
claim is an extension beyond the stated scope of the inspected repository
report, with the new proofs and their limitations supplied in this package.
