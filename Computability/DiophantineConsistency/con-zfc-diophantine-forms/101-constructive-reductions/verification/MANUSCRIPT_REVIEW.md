# Main manuscript review

## Scope and result

This is an internal AI review of the main manuscript's overview, logical-dependency discussion, evidence claims, and integration instructions. The component mathematical arguments had separate reviews; this pass did not repeat their full proofs, rerun a proof assistant, or independently re-establish the transitive inherited calibration. It is not external peer review.

**Result: no unresolved substantive issue found in the reviewed scope.** One displayed characterization originally omitted its existential witness quantifiers. The author corrected it to

`(exists u,v,w in Z: x = u^2 + v^2 + w^2 + w) iff x >= 0`, for integer `x`.

The corrected text was inspected before this review was recorded.

## Checks and findings

- The seven-row overview agrees with the component literal metadata and audit receipts: the three nine-positive forms have degrees/operations 1,472,168/420, 997,810/1,057, and 1,626,248/428; the two fourteen-integer forms have 540/160 and 568/147; the quartics have 495 nonnegative and 977 unrestricted integer unknowns, with 15,377 and 24,632 monomials respectively. The integer quartic's coefficient height is 83,869,250.
- The synchronized predecessor's retained incoming README gives 2,088 integer unknowns and height 83,901,150. Thus the stated saving of 1,111 variables (approximately 53.2 percent), unchanged quartic degree, and slightly smaller coefficient height are consistent. The comparison distinguishes domains correctly.
- The manuscript explicitly limits simplicity claims to selected measures and inspected predecessors. It does not claim a global minimum, a new variable-count record for the fourteen-integer construction, historical priority, consistency of ZFC, or actual absence of zeros.
- The ordinary proof / finite verification / existing Lean dependency / new kernel theorem distinction is explicit in the abstract, main theorem discussion, and evidence section. Successful Python runs are not represented as proofs of the unbounded calibration. The main theorem is an ordinary compositional proof claim formalizable in ZFC; the lack of a new end-to-end kernel theorem is disclosed.
- The two immediate direct calibration declarations were inspected. `c222_iff_zf_refutation` precedes the machine-parameter section and has the stated machine-free theorem statement. `zf_refutation_iff_zfc_refutation` has the stated theory-inclusion and constructible-model directions. Both complete immediate files and their pins are present. The older calibration revision is expressly distinguished from the comparison snapshot. A complete transitive Lean rebuild is neither supplied nor claimed.
- Coefficient cost is not hidden by the operation counts: the discussion distinguishes fixed coefficient size from circuit length, keeps the two native nine-variable tuples separate, and identifies the original31/compact54 storage tradeoff. The root README reports actual raw byte counts and specifies its operation-count convention.
- The direct branch's independence from a machine run is stated at the semantic-source level, with an explicit qualification concerning machine-related modules elsewhere in the inherited import graph. The compact branches retain their named compiler and machine/refutation dependencies.
- Both recorded root verification receipts report PASS, 14 component checks, 45 byte-exact reconstructions, and seven calibration pin checks, with normal and optimized Python modes distinguished. This review inspected those receipts and the driver; it did not add another redundant execution. The driver verifies delivered data before rebuilding in a temporary directory and does not overwrite the delivered equations.
- The seven literal equation paths, both quartic expansions, root README, schema note, comparison ledger, and root verification receipts exist. The root driver imports only the standard library; component dependencies are supplied locally. All article reference labels resolve across the main file and three included sections, with no duplicate labels found.
- Citation boundaries are appropriately stated: repository comparisons and inherited calibration are identified by pinned sources; the classical three-square conversion is attributed separately; the universal-bounds reference supplies context rather than evidence for a claimed optimum. The packet manifest is described as integrity evidence, not mathematical proof.

## Reviewed manuscript identity

SHA-256 of `report/ConZFC_Constructive_Reductions.tex` at the end of this review:

`c450135cc5f557a22c2c01483ed75a849c2cc11989f744351cb7cc0e63eb2bb8`

Later typographic or packaging edits, if any, should not be inferred to have been reviewed from this digest.
