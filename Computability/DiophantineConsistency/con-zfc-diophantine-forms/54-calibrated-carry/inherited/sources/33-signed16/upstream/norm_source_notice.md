# Attribution and scope

This is an AI-assisted research contribution prepared for Vladimir Reshetnikov's
ProveIt project on 22 October 2026 (America/Los_Angeles). It does not imply human
authorship by a researcher who has not reviewed it. New material is offered under
the repository's MIT-0 license in LICENSE.

The mathematical and executable sources were read at ProveIt commit
ae3007ca4467011e0e051c84acb4a1dd13971b0e. The repository catalogue at that commit,
including its limitations and attribution, is retained under references/.
Copied sources retain their original comments and notices. Some text copies
normalize a terminal newline; source identity of the machine and the actual
coefficient bytes is checked separately by SHA-256.

The new contributions are the quotient shift and compact root bound in norm12/,
the combination of odd-scale semantics with the low-degree integer lifts in
low_degree/, and the signed-coordinate construction documented in the article.
All rely on the explicitly identified earlier compiler and K215 calibration
theorems. Finite computations check formulas, counts, and coefficient bytes;
they do not prove those semantic theorems, produce a ZFC refutation, establish
Con(ZFC), or constitute a new Lean/Rocq formalization.

The literal K215 transition table and its upstream notices retain their
original attribution, including the Wade-derived machine lineage. No remote
repository files were changed by this delivery.
