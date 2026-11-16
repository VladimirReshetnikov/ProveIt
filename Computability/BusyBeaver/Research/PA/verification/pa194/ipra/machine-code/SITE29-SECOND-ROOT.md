# PA194 site-29 second controller pass

`PA194Site29SecondRoot.site29SecondRoot` follows the literal machine from the site-29 state-24 frame through the first header pass, the second pass's scans and rewinds, and its return to state 24. It states an exact combined clock and a named exact output tape expression. The input needs a zero run of length `k+2` after source path `100010110`. All model-valued logical registers, the preceding spare, and the complete encoded numeric suffix are arbitrary. The established blank-to-site-29 execution has sufficient padding.

The two new source modules give the fixed header's eight literal steps to state 19, the return to state 24, and the composition with the prior arbitrary-file rewind. The output is an intermediate controller frame: the actual increment of logical register 6 and the return to a site-30 source frame remain open.

`check-site29-second-root.sh` recompiles sixteen source modules in a fresh output against the pinned site-27 coherent baseline, retained site-28 carry stage, and retained site-28 finish-return stage. Invoke with `REPO SITE27_BASELINE SITE28_STAGE FINISH_STAGE PROJECT_FOUNDATION PACKAGE_FOUNDATION SOURCE_DIR NEW_OUTPUT`. It pins sources and selected direct objects, checks all specified axiom reports for `sorryAx`, rejects overlapping machine objects and machine-specific fallback roots, and verifies input objects unchanged. Retained stage and general foundation objects require preceding replays or independent provenance.

This is an all-model finite physical-run segment, not a native iPRA sentence, arbitrary-length source simulation, or a consistency implication.
