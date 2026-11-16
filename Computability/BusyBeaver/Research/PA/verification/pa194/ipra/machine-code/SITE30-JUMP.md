# PA194 physical jump from site 30 to site 27

`PA194Site30Jump.jumpPath30To27` proves that the literal machine runs for exactly 40 steps from the actual source-program path 30 to path 27. The entire model-valued source-file code is unchanged. Its initial zero-run length is `(k+1)+1`, and its final zero-run length is `(((k+1)+1)+1)+1`: the jump adds two padding cells. Both the padding parameter and the file code are arbitrary elements of any model of PRA; no blank-suffix assumption is made.

`prefixRun` proves the 40-step physical execution for an arbitrary model-valued remaining tape. Its individual row lemmas check each required literal transition in the kernel; the two path identities and zero-run laws establish the source-frame form. The external natural-number induction in `standardRunCorrect` is used only to identify this fixed 40-step run.

`check-site30-jump.sh` recompiles the module in a fresh output. It has the same ordered arguments as `check-site29-complete.sh`: `REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE SELECTED29_STAGE FINISH_STAGE INCREMENT29_STAGE COMPLETE28_STAGE RETURN29_STAGE PATHS29_STAGE PROJECT_FOUNDATION PACKAGE_FOUNDATION SOURCE_DIR NEW_OUTPUT`. It pins the source and selected direct-object hashes, checks both axiom reports for `sorryAx`, rejects overlapping machine objects and machine-specific fallback roots, and records all input object hashes before the build and verifies them afterward. The retained stages and general foundations require their preceding replays or independent provenance.

This is a finite all-model physical run, not by itself a native iPRA sentence, an arbitrary-length source simulation, or a consistency implication.
