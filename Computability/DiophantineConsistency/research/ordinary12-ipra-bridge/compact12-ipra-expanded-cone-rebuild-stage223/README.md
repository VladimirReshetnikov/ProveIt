# Stage 223: rejected batch setup

The proposed 15-stage batch stopped before checking guards or invoking Lean.
The runner still limited its argument to five stages and rejected the requested
count with `ValueError`. No stage receipt or object was produced. The original
runner, observer, standard output, error, and sparse resource sample are
preserved here. A separately captured retry raises only the count limit to 15;
the per-stage checks and receipts remain in place. This is an orchestration
failure, not a mathematical or Lean compilation failure.
