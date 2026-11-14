# Provenance and attribution

This research archive was prepared in response to Vladimir Reshetnikov's request to compare PA consistency machines and attempt a reduction below 194 working states.

The original project is [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt), pinned to commit `75a42a28ca818627f5a104fb0f0c7f7d02a52947`. The original James Y. Chang construction and the later contributors' packets retain their attribution. Their supplied license notices are included in `licenses/`; additional notices accompany the selector certificate. No authorship of inherited machine tables, compiler logic, theorem arguments, or the coefficient-three primitive certificate is claimed here.

The original file paths and byte digests for copied comparison inputs are recorded in `PROVENANCE.json` and `inputs/catalogue_index.json`. Minor adaptations of inherited code include portable paths and a corrected explanation of the catalogue fingerprint. The C++ grammar searches derive from the upstream PA194N6 search code; the new negation/scanner objectives, input instances and experiments are identified in their README. Supplementary research directories retain their local provenance notes.

New report text, comparison annotations, exact certificate enumeration/checking work, source-rotation checker and search adaptations may be reused under the MIT No Attribution license included as `licenses/LICENSE.ProveIt`, subject to preserving the original notices for inherited material.

The complete end-to-end arithmetic equivalence for a new sub-194 machine was **not** proved. Python verification of a finite certificate, an exact source identity, an optimizer receipt and a proof-assistant endpoint are different kinds of evidence. The report and checkers preserve those distinctions.
