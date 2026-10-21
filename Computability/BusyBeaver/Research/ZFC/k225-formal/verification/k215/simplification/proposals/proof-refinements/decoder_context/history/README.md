# Development history

The logs in this directory are intermediate observations only. They do not bind the frozen final source; use `verification/fresh-build.json` and the accompanying six final logs for that purpose.

The generic proof's initial draft required local elaboration repairs: exposing a mapped-list expression to a rewrite, giving the zero-step goal an explicit constructor, and replacing an unavailable Boolean theorem projection. The path proof required an anonymous constructor witness and an in-bounds root array access. The source-path extension required recursion on the bit list rather than an unrestricted simplifier unfolding, and explicit types for existential role/time witnesses. These were proof-script elaboration issues; no theorem premise was weakened to fix them. The final fresh build rechecked every source from scratch.
