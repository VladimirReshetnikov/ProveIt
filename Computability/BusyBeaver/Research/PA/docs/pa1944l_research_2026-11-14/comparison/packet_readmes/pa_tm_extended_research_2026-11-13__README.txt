# PA-consistency machines: comparison and refined reduction search

**The requested sub-196-state construction was not obtained.** The smallest
accepted working-state count in this package is 196. No 195-state table is
presented as correct, and the unsuccessful searches do not establish a lower
bound. This package records the comparison, new verification infrastructure,
four alternative 196-state tables, and reproducible negative search results.

Start with `report/pa_tm_extended_research.pdf`; its complete LaTeX source is
beside it. `RESULT.json` records the outcome in machine-readable form.

## Scope and frozen sources

The model has one binary tape, initially blank and unbounded in both directions.
Each working state has two defined transitions; the separate halt label is not
counted. The requested property is a PA-provable equivalence between nonhalting
and consistency of ordinary first-order PA with full induction.

| Source | Commit |
|---|---|
| ProveIt incoming / ConciseIPRA | `f1f076e31995f10460838d1846456f4bb9c8ae80` |
| BusyBeaver PA196 | `407cdc356f6b586635e71ac92be394255f4bfea4` |
| Requested BusyBeaver PA209 | `69d98241a721ead20b4f0b17df9062950b40fbfe` |

The current ProveIt incoming directory includes an earlier research archive
about this same problem. Its comparison data and checker are retained with
attribution, and the new current-input audit checks the current archive census.
The new work extends its search and verification interfaces; the earlier
comparison is not misrepresented as a new discovery.

## Main findings

* Nine designated 208-state presentations form two rooted, action-preserving
  transition-graph isomorphism classes, with five and four presentations. Both
  resolve to the same 3,909-site source program.
* The requested 209-state predecessor differs from the U209 parents within the
  U208 archives. PA196 removes 75 of its native states and introduces 62. Its
  134 common native states have only three changed transitions. The native
  roles used by the final U208 saving are already absent from PA196.
* The explicit upstream formal arithmetic endpoint is
  `PA196.Arithmetic.pa_proves_nonhalting_consistency`: PA proves nonhalting
  implies Con(PA). The report explains a syntactic proof-producing route to the
  converse and its remaining formalization boundary. No new end-to-end Lean
  biconditional and no fresh full upstream Lean build are claimed.
* Independent checks establish zero/nonzero, difference-bound, and reduced
  joint invariants. They reduce 4,959 generic instruction cases to 4,954
  reachable cases. The generalized executor permits repeated register-file
  excursions and preserves the nine logical registers while allowing more
  spare registers and a larger gap.
* Four one-row variants each retain 196 working states, pass 4,959 constrained
  symbolic instruction contracts, and have the exact same 58,154-step blank
  startup endpoint. They are distinct from each other and the published table.
* The report gives an all-instance countervaluation for replacing the first
  quantifier head by the shorter `forall-elimination` head, and identifies the
  missing atomic-vacuity argument in the automatic-freshness proposal.

## Contents

| Directory | Contents |
|---|---|
| `report/` | Main `.tex` and compiled `.pdf` |
| `comparison/` | All nine designated U208 tables, PA209, PA196, source inventories, comparison checker, manifests and attribution |
| `inputs/pa196/` | Pinned literal table and Lean source extracts used by the new checkers; not a complete Lean checkout |
| `verification/` | Exact startup runner, symbolic executors, three invariant certificates and independent checkers, countervaluation supplement, detailed physical-contract argument |
| `auxiliary196/` | Four alternative dense/native 196-state tables, regeneration/checker, invariant and source proof extracts, receipts |
| `experiments/` | Restricted search programs and frozen outcomes; see its README files |
| `provenance/` | Published result statements, source references, and the earlier written reverse-translation argument |

Dense `.tm` rows have the format `state read write direction next_state`.
The published table and four closing variants use working labels `0..195`,
start `0`, and halt `196`. Native-label copies use start `74` and halt `254`.
The two labeling systems must not be mixed.

## Reproduce the bundled evidence

Use ordinary Python 3.10 or newer, without `-O`. No third-party Python package
or network access is needed for the following command, which may be run from
any working directory:

```sh
python3 /absolute/path/to/pa_tm_extended_research_2026-11-13/verification/reproduce.py
```

It verifies the pinned input hashes and state count, simulates the exact entire
blank-tape startup, repeats the comparison, checks all three invariant
certificates independently of their discovery algorithms, checks the 4,959
original and 4,954 refined symbolic contracts, checks the countervaluation's
finite supplement, and rechecks the four closing variants. The resulting
receipt is `verification/verification_results.json`; detailed subprocess logs
are in `verification/logs/`.

The Python symbolic checks instantiate the unchanged register-engine macro
lemmas. They are executable mathematical evidence, not Lean kernel proof
objects. The all-instance countervaluation is proved in the report; its finite
test script is supplementary. The matrix experiment concerning a fixed-falsity
implicational basis applies only to that isolated basis, not the complete
native PA196 calculus.

Exploratory searches are not run by this command. Their C++20/Python commands,
candidate counts, limits, and frozen outcomes are documented in `experiments/`.
Repeated runs of the same candidate family under stronger preconditions are
not disjoint searches and their counts should not be summed.

To rebuild the report with a conventional TeX installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa_tm_extended_research.tex
pdflatex -interaction=nonstopmode -halt-on-error pa_tm_extended_research.tex
```

It uses standard LaTeX packages including Latin Modern, AMS mathematics,
geometry, booktabs, microtype, xurl, enumitem, fancyhdr, and hyperref.
`verification/generalized_physical_contracts.tex` is an additional section
source, not a separate standalone document. The retained prior translation
source in `provenance/prior_report/` is attributed to the earlier archive.

`SHA256SUMS` covers the delivered files before any reproduction command changes
generated receipts. A re-run can change timing fields and logs without changing
the underlying checks.

## Evidence limits and the missing result

No result here proves that 196 is minimal. The searches cover particular
quotients, selector constructions, layouts, grammar heuristics, and logical
variants. A rejection can reflect the restricted simulation relation or the
conservative symbolic evaluator, rather than failure of the candidate's true
blank-tape behavior. A finite startup check alone does not prove nonhalting.

Completing the original task still requires an explicit table with at most 195
working states, a verified blank startup, sufficient universal simulation
contracts (or another proof), and a complete PA-formalizable calibration to
the proof search. The four 196-state variants and stronger certificates do
not replace that missing construction.

## Sources and licenses

Primary pinned sources are [PA196](https://github.com/jamesyc/BusyBeaver/tree/407cdc356f6b586635e71ac92be394255f4bfea4),
[PA209](https://github.com/jamesyc/BusyBeaver/tree/69d98241a721ead20b4f0b17df9062950b40fbfe),
[ProveIt incoming](https://github.com/VladimirReshetnikov/ProveIt/tree/f1f076e31995f10460838d1846456f4bb9c8ae80/docs/incoming),
and [ConciseIPRA](https://github.com/VladimirReshetnikov/ProveIt/tree/f1f076e31995f10460838d1846456f4bb9c8ae80/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA).
Retained files carry their original licenses and notices in their respective
directories. `LICENSE.research` applies only to new research contributions.
