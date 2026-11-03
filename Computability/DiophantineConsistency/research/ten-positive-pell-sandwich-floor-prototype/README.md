# Shared integer floor for Pell sandwiches

This generic model-level packet strengthens the previously checked scaled
rounding argument. `split_floor` retains the small remainder: under its
explicit scaled sandwich and positive witness hypotheses it constructs
`v < X^r` with `(X+1)^(2r) = 2*Y*X^r + v`. `transfer_floor` then proves
`K*Y < C < K*(Y+1)` for any second pair K,C satisfying the same strict
sandwich. It uses no graph, halt, or iPRA hypothesis or conclusion.

This is intended to compare an actual scaled graph witness with a separately
constructed unscaled source pair, using the same r, X, Y. That graph-specific
specialization and any converse are separate obligations.

Successful guarded check: `observations/fixeddigits-attempt04/`, object
`/tmp/pell-sandwich-floor-woudedwc/PellSandwichFloor.olean`, SHA-256
`ba64543021641436843a9603a586a83d5d4da1632cd0c782c43638af6b1a29b4`.
Attempts 01–02 record proof elaboration failures; attempt03 produced an
object but was rejected by the runner due to unused-variable warnings, and
is not the accepted check. The receipt pins the selected tool, source, runner
and providers, with inherited transitive project/package/source-object and
dynamic-library limitations.
