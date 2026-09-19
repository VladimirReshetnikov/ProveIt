# Source map and contribution boundaries

## Supplied material actually inspected

The user supplied `Cardinals4.zip`. The textual research sources in that archive are:

- `docs/Large_Cardinals_Synthesis.tex`
- `docs/Large_Cardinals_Unified_Report.tex`

The archive also includes the `Cardinals/` Lean development, including
`Cardinals/Combinatorics/FiniteCycles.lean`,
`Cardinals/Combinatorics/SecondRound.lean`,
`Cardinals/Combinatorics/ThirdRound.lean`,
`Cardinals/FiniteLabel.lean`,
`Cardinals/Ultraexacting.lean`, and `Cardinals/README.md`.

The twenty-seven separate continuation reports described by the synthesis are not present as separate reports in the supplied archive. No claim is made to have read those missing documents. Comparisons are with the actual supplied synthesis.

## Exact correspondence with the synthesis

| Supplied location / LaTeX label | Its role here | Continuation |
| --- | --- | --- |
| Section 9, `lem:algebra` | Existing finite cycle-amplification argument; re-proved, not claimed as new. | Lemma 5.1. |
| Section 9, `thm:fsel` | Existing ultraexacting finite-family selector exclusion. | New Prikry-extension counterpart: Theorem 5.2. |
| Section 12.5, `lem:cyclic`, `thm:classification` | Existing cyclic-stabilizer sufficiency and ultraexacting necessity for finite labels. | Sufficiency re-proved in Lemma 6.3 / Theorem 6.4; new Prikry necessity in Theorem 6.2. |
| Section 13, `thm:strength` | Existing measurable calibration of rigidity and the normal-trace principle; includes relative cone homogeneity. | Classical/previous mechanism expanded in Section 9; finite-symmetry clauses added without raising strength in Section 10. |
| Section 13, `thm:charges` | Existing tail synchronization, invariant charges, and stated finite-family ultrafilter exclusion at designated ultraexacting classes. | New universal countable ultrafilter orbit in Theorem 8.2; sharp local width in Corollary 8.3. Prikry finite-family exclusion is proved independently in Theorem 7.1. |
| Section 15, final question (ii) | Asks whether finite-label necessity and finite selector-family exclusion hold in a Prikry extension of a measurable, followed by the stronger phrase “rigidity alone.” | Prikry-extension assertion answered positively. The rigidity-alone implication is not claimed. |
| Section 15, final question (vi) | Asks about countably infinite definable families of global ultrafilter-valued kernels. | Not answered: the new construction has countable fibers, not a countable collection of global choice functions. |

The original low-rank rank-agreement statement is recovered with an explicit ground-model bijection `b : kappa -> V_kappa`. This parameter is allowed because the new negative theorems admit arbitrary ground-model set parameters. No rank-into-rank embedding is introduced.

## Primary public sources checked

1. Tom Benhamou, *Prikry Forcing and Tree Prikry Forcing of Various Filters*, arXiv:1801.04424v2 (2018), especially Section 3. Classical Prikry background. The particular pure-decision and cone-deletion tools used in the continuation are also proved in the paper.
2. Juan P. Aguilera, Joan Bagaria, Philipp Luecke, *Large cardinals, structural reflection, and the HOD Conjecture*, arXiv:2411.11568v4 (2025). Context only for exacting / ultraexacting cardinals.
3. Juan P. Aguilera, Joan Bagaria, Gabriel Goldberg, Philipp Luecke, *Large cardinals beyond HOD*, arXiv:2509.10254 (2025). Context for the ultraexacting / I0 consistency comparison, not an input to the new measurable upper bound.

The report's bibliography gives clickable arXiv references. Literature searches do not establish priority. The proof is offered as a new continuation relative to the supplied synthesis, not as a certified first discovery in the literature.

## Validation limits

- The complete report was compiled with pdfLaTeX; the final log has no undefined-reference, missing-character, or overfull/underfull-box warnings.
- All 21 pages were rendered and inspected for layout, with full-size inspection of representative proof pages.
- The standard-library Python checks were actually executed successfully; their bounds and output are included.
- No Lean verification, independent referee review, or mechanized verification of the set-theoretic arguments is claimed.
