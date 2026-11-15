# PA194 site-29 third-pass dispatch

`PA194Site29To2.site29To2` follows the literal machine from a site-29 state-24 input through the first two controller passes and the next 19 transitions to state 2. It gives the exact combined clock and both output tape codes. Its input requires `k+2` zeros after source path `100010110`; logical registers, the preceding spare, and the complete encoded numeric suffix are arbitrary model values. The established blank-to-site-29 execution has sufficient padding.

`PA194Site29ThirdDispatch` proves the 11- and 19-transition segments and their application to an arbitrary model-valued zero-run length and file tail. The marked bit makes this dispatch end at state 2 rather than the first pass's state 84. The state-2 output is an intermediate configuration: selected-register traversal, the actual increment of logical register 6, and return to site 30 remain open.

`check-site29-to2.sh` recompiles the preceding sixteen modules and these two modules in a fresh output. Invoke with `REPO SITE27_BASELINE SITE28_STAGE FINISH_STAGE PROJECT_FOUNDATION PACKAGE_FOUNDATION SOURCE_DIR NEW_OUTPUT`. It pins source and selected direct-object hashes, checks all requested axiom reports for `sorryAx`, rejects overlapping machine objects and machine-specific fallback roots, and verifies input objects unchanged. The retained stages and general foundation require their preceding replays or independent provenance.

The theorem is an all-model finite physical-run segment, not a native iPRA sentence, arbitrary-length source simulation, or a consistency implication.
