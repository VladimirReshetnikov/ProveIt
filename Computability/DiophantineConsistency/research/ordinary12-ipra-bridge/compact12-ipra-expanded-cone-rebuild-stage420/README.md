# Expanded compact/iPRA rebuild: stages 420–425

All six remaining modules, from `ZFCinPA.ValidatorConsistencyLower222` through
`DiophantineConsistency.IPRAExpressionNative`, compiled with exit code 0 and
no warnings. The wrapper rechecked all prior receipts, all 425 current source
pins, the three corrected source cones and baselines, selected overlay and
exact-warning exceptions before and after the batch. It exited 0 and reported
`{"completed": 425, "overlay_unchanged": true, "total": 425}`. Each stage
retains its source snapshot, dependency guards, log, timing and object hash.

The terminal stage 425 compiled in 2.483 seconds, with source and direct
dependency guards unchanged. Its source SHA-256 is
`f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8` and its
object SHA-256 is
`9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684`.
The full terminal receipt is
`observations/batch-085/stage-0425/terminal.json`, SHA-256
`5483e0f8444fcaeaec8a68929f63a77d2aa3435d27fafa1b89c78eed3dc57977`.

The full wrapper output is `observations/execution-monitor/runner.stdout`,
SHA-256 `5c3c05d2bb11a36207a9d3a21e4740f90379b33585c81443c0ca2e60171cb357`;
the wrapper result and sampled resources are in `monitor.json`, SHA-256
`49550f186b371959483811a7b2be529c580e5d9be6b6c96c20c83eb508bb46f4`.
The runner SHA-256 is
`30a06b0ef5ac4dc2d7fc09e63fb7ecded6831f08225b00270df37c96106b12a7`.
Five-second monitoring sampled at most one Lean child and minimum MemAvailable
18,470,804 KiB; short children and overlap can be missed between samples.

This completes the selected 425-module author rebuild. It is not an
independent replay, complete provider audit, or a proof of the requested
equation-to-internal-iPRA equivalence. Package, dynamic and historical object
ancestry remain unauthenticated, and the compact model-to-iPRA join remains
open. Source/provider mismatches at stages 276, 317 and 419 required local
checked proof corrections.
