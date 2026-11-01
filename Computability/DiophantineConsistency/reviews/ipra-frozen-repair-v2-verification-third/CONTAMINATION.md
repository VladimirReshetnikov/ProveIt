# Concurrent recorder contamination

The intended comparator subprocess reported exit 0 through its wrapper, but an accidental second invocation targeted the same `run.log` while it was live and could have truncated or interleaved that file. The accidental invocation was interrupted. Preserve this packet as evidence, but do not use its log or terminal marker to establish an independent comparator exit; a fresh recorder in a separate directory is required.
