# Review scope

## Supplied material

All three ZIPs were extracted and their complete LaTeX manuscripts compared.
The reconciled report uses A for the continuous left-finite development while
integrating the distinct Puiseux theory and complementary B/C results. The original manuscripts are not
redistributed with this report; the manifest records hashes of the uploaded
archives and of their contents, and the reconciliation ledger cites them by
their original line numbers.

## External checks

The report's bibliography gives full references and links. In particular:

- The ordinary-computable-number Wikipedia page was treated as orientation, not
  authority for the new representation-specific statements.
- Hamkins's six-page 2024 lecture notes were visually inspected at pages 4–6 for
  the structural definition, noncomputable-real example, and classification.
  His 2025 seminar announcement confirms attribution and the connection to Lurie.
- Lurie's publisher abstract and metadata were checked. The 1998 publication date
  is distinguished from the 2014 online posting. The full Lurie paper was not read.
- The full Harkleroad paper was not accessible in this preparation; its entry is
  explicitly a historical bibliographic reference rather than a newly audited proof.
- The introductory characteristic-zero Newton–Puiseux statements in Rond and
  Kedlaya were read in the PDFs, including the algebraically-closed coefficient
  hypothesis. No positive-characteristic result is used.
- Rzepka–Szewczyk Section 2.1, equation (1), was checked for the valuation degree
  formula and the residue-characteristic-zero defectless case.
- Restrepo Borrero–Shamseddine, version 2, Section 1.1, was checked for the classical
  rational left-finite definition and context; its integration theory is not used.
- The abstracts/metadata of the cited infinitary-computation, larger surreal-field,
  and Mahler-support papers provide context only, as stated in the bibliography.

Classical books and Neumann's support lemma are identified as background inputs,
not represented as newly proved or independently fully audited in this merge.

## Repository snapshot

Commit: `4896a2808ce30e01b1c86ae3ba2295a64762d246`.

The repository tree, root README, and selected source files were read through the
GitHub connector:

- `Surreal/Foundations/SignSequenceField.lean`, including its noncomputable field
  transport and explicit outstanding formalization obligations.
- `Surreal/HahnSeries/Evaluation.lean`, including positive-order evaluation,
  summability, the geometric identity, and its exact finite remainder.

The root README states that real closedness and the normal-form bridge to Hahn
series remain formalization tasks. That is not an assertion that the classical
mathematical theorems are open problems. That historical source review included
no local Lean build, CI audit, or repository write.

## Tests and presentation

The three original standard-library Python programs were preserved unchanged and
rerun, together with the new reconciliation suite. The September 22 rerun results are in `data/` relative to this report, with
the runtime and UTC timestamp in `data/summary.json`. The geometric-cover
regression was added for the revised candidate-range proof; the three original
verification programs remain unchanged.
These are finite exact-rational tests only. The revised PDF was rebuilt with
LaTeX, its log checked after references stabilized, and selected pages around
the changed proofs and reproduction instructions rendered for inspection. The
current details are in `data/document_check.json`; they supersede the original
merge's presentation record for this revision. These are presentation checks,
not a machine-checked mathematical proof.
