# Independent terminal audit of split diagnostic

Author outer session 13406 exited 1. The independently written checker
completed as session 30112 with observed exit 0 and saved `result.json`. It
verifies the frozen state and both attempted source/log hashes, the first
object, direct-import producer bindings, 200 direct guard slots, 1,382 overlay
links and the upstream sign25 bridge audit.

The import-only stage compiled successfully. The following alias-and-attribute
stage's dependency scan succeeded but Lean compilation exited `-6` after an
interpreter memory exception under `-M2800`; neither that object nor the
following bridge/axiom objects exists. The failed run has no final postflight.
Because this split changes import boundaries, the observation does not by itself
identify the exact cause of the earlier failure. It is not a sign25 endpoint.
Guard and overlay observations do not establish a complete dynamic or
transitive dependency trace.
