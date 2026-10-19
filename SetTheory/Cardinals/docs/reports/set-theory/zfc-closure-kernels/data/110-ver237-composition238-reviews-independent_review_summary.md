# Independent review summary

Three separately delegated mathematical reviews were performed during this
investigation. This note summarizes those actual review results; it is not
a proof-assistant certificate or an external peer-review claim.

## Local construction and runtime rules

The local verifier was developed separately from the discovery script. It
checks the exact domains and edit set, every incoming-edge implication of
the structural invariant, all six special whole-tape blocks, and the
ordinary rows under the state identification. Its certificate is
`evidence/local238_certificate.json`.

The direct-runtime engine was separately read for literal-rule soundness,
unary self-loop induction including zero length, the four finite-list
schemas and their reverse direction, exclusion of hidden halts, positive
affine durations, and absolute head movement. No mathematical defect was
found in the accepted interfaces. The detailed review is
`reviews/runtime_review.md`. It specifically notes that the complete source
control certificate must accompany the runtime adapter's leaf hash.

## Main mathematical report

The exact table, state census, edit counts, six local cases, complete guard
receipt, source semantics and inherited calibration files were compared
against the report. No theorem-level or state-count discrepancy remained.

Two explanatory corrections identified during review were incorporated:

- In the longer state-91 block, state 151 reads the bit at relative position
  -2 to distinguish the original state-91 route. The zero at position -3
  subsequently permits the return excursion; it is not the branch bit.
- The external nonhalting conclusion under consistency uses the ordinary
  mathematical halting/refutation equivalence, not a general inference from
  ZFC-provability to external truth under consistency alone.

The source-interface text was also made explicit about the original
203-node program, its 204-step decoder fuel and maximum path depth 51, and
the requirement that source halting reach a literal halt leaf.

## Supplementary formalism result

The assembled formalism section and packaged checker were reviewed together.
The review found no substantive defect in the six-valued obstruction, the
fixed-finite-fragment reflection proposition, or the stated arithmetic
calibration example. The retained logical rules, actual atomic equality,
atomic vacuity and irreflexivity are distinguished from the excluded CP/GIC
axioms throughout. The reviewer independently reran the finite checker
under Python optimization and obtained all 11,690 declared obligations,
including both newly explicit formula-definable witnesses.

The review preserves the report's evidence limits: no new exact-table
kernel endpoint and no unmeasured state-count claim for an alternative
formalism.
