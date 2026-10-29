# Independent replay: witness selection for open matrices

For any open Foundation semisentence φ, explicit primitive-recursive candidate
codes and a proof in the proposed universal theory of their universally
closed finite disjunction, `PRA_exists_witness_of_openDisjunction` constructs
one fixed primitive-recursive witness code and a candidate-PRA proof of φ
at that witness. The proof uses the actual substitution and characteristic
compiler, the reviewed universal-theory equivalence, and finite selection.
It does not extract the candidate disjunction from a ∀∃ proof; Herbrand
extraction and Π₂ conservation remain open.

Two separate builds against the independent finite-witness provider
`/tmp/pra-finite-witness-independent-00hf0nxl/lib` passed both modules with
matching source, object and complete-log hashes. The driver verifies its
parent source and object hashes and frozen selection sources. [Independent
driver, state and logs](pra-herbrand-selection-root-replay/) and the
[author packet](pra-herbrand-selection-author-replay/) are retained. Historical
failed attempts are evidence only, not compiled proof inputs. Foundation,
Mathlib and unchanged local objects remain inherited cache boundaries.

A subsequent upstream merge changed `PRAFormulaParameters.lean` and
`PRAUniversalSyntax.lean`. This receipt authenticates the earlier snapshot;
the affected downstream [source-current replay](pra-parameter-current-root.md)
has since passed.
