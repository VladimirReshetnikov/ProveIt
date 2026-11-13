# Independent K canonical digits failure review

Confirmed failure. Author-observed outer session 51716 exited 1. Rewriting the last-digit list failed because its `getLast` nonempty proof depends on the original list; the final canonical-digits report includes `sorryAx`. No object or successful postflight exists. Frozen/live state, source, logs, monitor records and overlays match; the numeric outer receipt has no state hash. No Lean replay was performed.
