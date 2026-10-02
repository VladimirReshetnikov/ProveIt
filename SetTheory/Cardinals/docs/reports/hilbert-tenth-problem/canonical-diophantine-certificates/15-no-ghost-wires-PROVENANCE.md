# Sources and provenance

Research and verification date: October 2, 2026.

## Repository inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt

Observed recursive-tree revision:
`928ea97017a25ebe56d240c84f27d2275d818c75`.

The GitHub connector supplied the repository tree and directory information,
the Hilbert's-tenth-problem README, the wiring-obstruction note, and the MRDP
interface. This was a targeted inspection, not a complete repository audit.
The main README is large; only claims directly supported by the retrieved
relevant text are used.

Direct starting point:
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interaction_combinator_wiring_obstruction.md`

Returned blob: `764c982297342093307a0e831bc0d9ed5084c87f`.

This note supplies the two four-delta example nets, their terminal behavior,
the summary obstruction, and the explicitly stated need for a topology-aware
arithmetic compiler. Those examples and the obstruction are inherited, not
claimed as discoveries of this article.

MRDP interface, read at the recorded tree revision:
`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`

Returned blob: `74aea8c5e75923c7f8b0c041388b91e10e729d65`.

The interface states the fixed-polynomial, fixed-witness-dimension MRDP theorem.
No Lean or Rocq build was run. The standalone compiler does not import this
interface or use MRDP as an implementation step. Neither the user's repository
nor any persistent Library file was modified.

## Primary mathematical sources

Yves Lafont, *Interaction Combinators*, Information and Computation 137 (1997),
69–101. The original paper was inspected through this PDF copy:
https://chorasimilarity.wordpress.com/wp-content/uploads/2024/01/ic-lafont-1.pdf

Publisher record:
https://www.sciencedirect.com/science/article/pii/S0890540197926432

The definition on journal page 71 (PDF page 3) and rule diagrams on journal
pages 81–82 (PDF pages 13–14) were visually inspected. These fix the ordered
ports, admission of cyclic wires, the six rules, the difference between gamma
and delta annihilation, and the repeating example. The four-step repetition
is Lafont's example, newly encoded here, not a newly discovered divergent net.
No copy of the original copyrighted paper or its figures is included. The
small pair-suppression illustration in the article was drawn for this report.

Lafont, *Interaction nets* (POPL 1990):
https://doi.org/10.1145/96709.96718

G. I. Lehrer and R. B. Zhang, *The Brauer category and invariant theory*:
https://arxiv.org/abs/1207.5889

This is background for established matching-diagram composition and closed
components, not a source for a claim of novelty about that composition.

Yu. V. Matiyasevich, *Enumerable sets are Diophantine* (1970), reprint:
https://doi.org/10.1142/9789812564894_0013

Yu. V. Matiyasevich, *Towards finite-fold Diophantine representations* (2010):
https://doi.org/10.1007/s10958-010-0179-4

These support the distinction between ordinary MRDP and multiplicity-sensitive
representations. The present finite-horizon certificate does not resolve the
unbounded finite-fold problem.

## Construction and verification

The article's polynomial formulation, proofs, and Python implementation were
developed for this response. Historical priority for the specific canonical
certificate was not established by the limited source search. No claim of
external independent review or peer-reviewed novelty is made.

`verify.py` exhaustively compares three independently implemented finite gluing
algorithms and checks the compiled residuals on the reported finite families.
`check_export.py` separately evaluates the JSON residual representation without
importing the compiler. All arithmetic is exact integer arithmetic. The
unbounded theorems rest on the written proofs, not on the finite test counts.

The PDF was generated from the supplied LaTeX source and rendered for visual
inspection. The final LaTeX run had no overfull-box or unresolved-reference
warnings. No font files are distributed in the archive.
