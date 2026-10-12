# Integration contract

## Placement

Keep this package intact under a new report/research directory chosen by the
repository maintainer. Do not assign report 88 automatically: the repository is
receiving concurrent contributions. No production file must be overwritten.
The relative imports make `scalar_separators/` usable from the package root.

## What to adapt into `fastunknot`

The maintained source layer should supply:

1. The exact standard matching matrix, complete quadrilateral pair exclusions,
   source-derived rational Euler functional, and original-coordinate map.
2. A validated triangulation and its authenticated relationship to the input
   diagram or current geometric reduction stage.
3. A proposed conflict-local column partition/tree and an explicit resource budget.

Call `compile_source` and then `verify_source_compilation`. A rank greater than
one or a cross-bag pair is a rejected decomposition proposal, not a negative
normal-surface result. The independent source replay checks both intersections
and the copied source rows. `Prepared` builds complete local ray lists once.

Use `solve(objective, zeros=...)` for original coordinate anchors. On `POSITIVE`,
run `verify` and project to the maintained source coordinate order. For a
source-compiled model, single-ray recipe gluing guarantees a source extreme ray.
Normalize to a primitive integer vector before applying the connected-normal
surface theorem. Retain the maintained geometric essential-disc or reduction
checks. The result names deliberately do not include `UNKNOT` or `KNOTTED`.

On `NONPOSITIVE`, the packet is complete for that objective and those coordinate
zeros only. Negative replay includes the complete local ray inventory and both
signed continuations. It does not prove absence of an essential disc outside
an incomplete anchor/sector family. Whole-recognition negative coverage remains
part of the maintained geometric algorithm.

## Reuse

Prepared lists may be shared across objectives and source-coordinate deletions.
Do not reuse across altered matching equations without recompiling or supplying
a separate checked transport proof. The generic `minimal_positive_support`
method is available for source-equivalent models with redundant scalar ports,
but the direct ray-extremality conclusion is only automatic for verified
rank-one source compilations.

## Dispatch and budgets

The implemented cost predictor is the sum, over bags and scalar sign chambers,
of the active-zero-set candidate counts. Counting only emitted rays can select
the wrong method. One bag provides a complete algebraic fallback, not a good
asymptotic bound. The actual capped fixture has more retained local rays after
splitting (13 versus 12) but substantially fewer candidate bases.

The delivered prototype has no implicit runtime cutoff. Add caller-specified
budgets and cooperative cancellation before routing arbitrary production inputs
through it. On exhaustion, return `INCONCLUSIVE`, preserving all original
fallbacks. There must be no path from an allowance being exhausted to a
nonpositive or knot verdict.

## Tests required before default-path promotion

Run the delivered standard-library suite, then integrate with the maintained
source/certificate tests and actual native triangulation corpus. Compare against
the incumbent dispatcher under identical preparation boundaries, especially
small cases and cases with no useful scalar decomposition. Test stale sources,
corrupted flux generators, missing conflicts, missing negative rays, malformed
face charts, vertex-link contamination, spheres, inessential discs, disconnected
inputs, and cancellation.

The current research evidence includes source-local matching and Euler tests,
not a run of the native suite. The four incoming ZIP bodies were unavailable.
The proposed module should therefore be reviewed as a new research candidate,
not an already validated production patch.
