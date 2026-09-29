# Sources, dependency boundaries, and research status

Date: 28 September 2026 (Pacific time).

## Repository evidence actually inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `fbba58593dc0622aa914972896150d4848f935b5`.

Directory:
`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/`.

The README at the pinned commit was explicitly retrieved. The article,
status record, and relevant implementation were also read through the
GitHub connector. The following distinctions were checked:

* The repository's headline k^n-k!+g(k) theorem is a nonattainment result,
  not an exact all-n optimization formula.
* Its graph bound distinguishes proper and improper initial colorings.
* Its structural formula accounts for same-cycle and cross-cycle collision
  graphs, isolated residual states, and residual permutation orders.
* Its proper-period improvement for k=3 applies to a connected biclique.
* Its equality with Davies's lower bound is reported for 7 <= n <= 30 and
  3 <= k < n, 372 finite parameter pairs. It explicitly distinguishes that
  statement from an all-n theorem.
* The function `u_witness` in `code/reversal.py` gives the zero-based
  parity-version arrays used for the independent orbit experiments here.

The broad repository tree was inspected for topic selection. No claim is
made to have audited every document or every Lean proof in the repository.
The main upper-bound proof in this article is self-contained and does not
rely on assuming the repository's candidate theorems are correct.

## Primary published source

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite
Automata with Output*, arXiv:1705.07150v2 (17 October 2017):

- https://arxiv.org/abs/1705.07150
- https://arxiv.org/html/1705.07150v2
- https://arxiv.org/pdf/1705.07150

Inspected points: the coloring-orbit formulation (Proposition 4), the
coprime two-cycle construction and parity generators, Theorem 3 and
Corollary 3, the three-output period contribution, Table 3, and Section 5's
optimality question. The PDF pages containing Corollary 3 (printed page 12)
and the open question and small-case table (printed page 17) were inspected
as page images in addition to parsed text.

The exact lower-bound existence theorem is a published dependency. The
article proves the new universal upper bound and equality restrictions,
then uses the lower theorem for attainability. It does not claim a new proof
of the two-generator monoid-generation theorem. Finite BFS tests do not
replace that dependency.

Background reference: Markus Holzer and Barbara König, *On deterministic
finite automata and syntactic monoid size*, Theoretical Computer Science
327(3), 319-347 (2004), DOI 10.1016/j.tcs.2004.04.010. Publisher metadata was
checked. The article cites this as background; its operative lower-bound
theorem is cited through Davies, rather than attributed to an uninspected
proof in the journal paper.

## Literature-search scope

Searches included the exact Davies title; combinations of DFAO, reversal,
three outputs, optimality, and 2026; and the exact Holzer-König title.
The broad acronym queries produced substantial unrelated material, which
was not used as mathematical evidence. The primary Davies text and the
repository's explicit status statement were the substantive sources.

No later complete solution was located by these searches. This is not an
exhaustive citation-index review, a survey of theses or unpublished work,
or correspondence with the author. It is not evidence sufficient to establish
priority or to assert that no earlier solution exists. Novelty claims are
limited to the inspected sources, in particular the concrete extension of
the repository's finite result to all n for three outputs.

## Claims and nonclaims

The principal new contribution is the all-n comparison proving the exact
three-output formula and forcing the optimal two-cycle graph. The rank
rigidity, 6AB collision penalty, and missing-orbit inventory are developed
as further results. The first theorem settles the complete k=3 slice of
Davies's Problem 2, not the full problem for variable k.

The lower witness, reversal-orbit reduction, graph classification method,
standard primitive-word counting, and small known values are not claimed
as inventions. The missing-orbit inventory applies primitive-word counting
to the extremal forbidden family. The example showing that necessary
conditions are not sufficient is included to prevent an overstatement of
the rigidity theorem.

The article is not externally refereed and has no proof-assistant
certification. The all-n proof is a conventional proof with a fully
displayed finite base table. The exact finite experiments are implementation
checks and regression tests. They are not an independently certified proof
of the infinite theorem.

## What remains open in this package

Four and more outputs; a necessary-and-sufficient classification of the
singular letter for saturation; efficient saturation recognition; second-best
values and stability; the near-maximum attainable spectrum; output counts
growing with n; proof-assistant formalization; sharp general-group analogues.
The article formulates eight corresponding research questions with specific
obstacles and next steps.
