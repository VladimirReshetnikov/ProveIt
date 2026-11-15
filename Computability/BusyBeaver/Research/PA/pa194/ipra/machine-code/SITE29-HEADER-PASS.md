# PA194 site-29 first header pass

`PA194Site29HeaderPass.site29HeaderPass` follows the pinned literal stepper from a state-24 site-29 header back to state 24, with an exact model-valued clock and exact right-tape expression. It requires a zero run of length `k+2` after the actual nine-bit source path `100010110`. All logical registers, the preceding spare, and the entire numeric suffix are arbitrary. The checked blank-to-site-29 theorem has sufficient padding for this segment.

The proof follows the distinct state-98 left turn, a 19-step dispatch to state 84, the model-uniform file/header scan, and the odd state-17 return. The five source modules expose the state-115, state-84 and state-17 intermediate layouts and retain the exact numeric suffix. This is only the first header pass; the site-29 increment of logical register 6 remains to be proved.

`check-site29-header-pass.sh` recompiles the five modules against the pinned site-27 coherent baseline, the retained site-28 carry stage and the retained site-28 finish-return stage, in a fresh output. It pins direct objects and source hashes, checks the requested axiom reports for `sorryAx`, rejects overlapping machine objects and machine-specific fallback roots, and verifies all input objects unchanged. Invoke with `REPO SITE27_BASELINE SITE28_STAGE FINISH_STAGE PROJECT_FOUNDATION PACKAGE_FOUNDATION SOURCE_DIR NEW_OUTPUT`. The prior stages and general foundations require independent provenance or trust.

This all-model segment is not a native iPRA proof, a complete source-instruction simulation, or either consistency implication.
