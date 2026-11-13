# Independent checker frontier assessment

Pinned repository: `2fa4637b3bf922beea0052a5210c22b14482950b`.

## Measurements

The exact measurements are in `frontier_metrics.json`, reproduced under CPython 3.12.14 by `../code/measure_frontier.py`. Source files are parsed and measured, not executed by that script. Historical source paths below identify the original extraction; portable copies are listed in `../reference/frontier_manifest.json`.

| Contract family | Tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| Inspected compact whole-JSON programs | 249 | 271 | 477 |
| Inspected compact JSON-Lines programs | 244 | 265 | 605 |
| Native Eq/D goal validated, proof alphabet promised | 321 | 369 | 596 |
| Native Eq/D goal and entire proof alphabet validated | 330 | 380 | 621 |

Each row is a coordinate envelope over DIFFERENT complete programs. The JSON-Lines row's byte coordinate is only the minimum of the two selected current comparison programs, not a certified exhaustive minimum. The whole-JSON row also pools distinct certificate protocols (three-field packets vs four-field packets and a [goal,floor] header), so comparisons should name the actual matched control, not merely one pooled row.

The article explicitly excludes first-line and JSON-Lines programs from its ordinary-JSON envelope. Some incoming reports pool all framing protocols; that convention gives 244 / 265 / 477 but is not the size of any one program and is not a homogeneous contract comparison. These are achieved upper bounds, never proved lower bounds on all iPRA presentations.

The compact interfaces assume a canonical guarded public goal and exact integer/list certificate data. They do not themselves check the entire public grammar or all JSON types. The 596-byte native interface validates the public goal but still promises the proof-data alphabet. The 621-byte strict native interface validates both. Omitting these distinctions would overstate a small implementation's checking boundary.

## Current byte incumbent

`source_snapshot/incoming/ipra_head_conversion_2026-11-12/code/compact477.py` has exactly 272 tokens, 306 AST nodes and 477 normalized bytes. It is already prior work at the inspected snapshot. It replaces short-circuit parity selection by eager multiplication and changes the neutral retained resource from scalar zero to the empty array. Therefore it has a semantic canonical-certificate conversion argument; it does not have exact equality of every raw acceptance language with the 478-byte control.

The earlier `zero_test_split` program is 271 / 305 / 478. Its one-byte gain was obtained by supplying the initial scope floor with the goal, justified for canonical guarded goals. The same transformation is unsound for the full native goal grammar without an additional check; the article gives a counterexample mechanism. It cannot be transplanted indiscriminately to the validated native checkers.

## Reduction search result

I did not establish a smaller complete byte checker or a new smaller mathematical axiomatization. Several equivalent expression rewrites increase source length. A particularly tempting apparent 476-byte program is invalid and explicitly named `INVALID_lambda_scope.py`: replacing the singleton list comprehension by an immediately invoked lambda changes Python assignment-expression scope. The assigned `a` and `k` become inner-lambda locals and are read before assignment. Moreover, simply passing them as inner arguments would leave the opener closing over the wrong scope floor. This file is a negative diagnostic, not a candidate, and should not be included in a user-facing checker directory.

The source snapshot contains existing counterexamples to deleting entry scope validation, silently substituting an unchecked image, or accepting the next future eigenvariable prematurely. These checks cannot be removed merely because canonical examples continue to pass.

## Useful conclusion for the report

A new mathematical presentation must be distinguished from a checker encoding improvement. The inspected repository already contains many equivalent rule presentations with substantially larger explicit checkers. A new six-rule or three-family presentation alone does not establish the requested below-frontier complexity. A sound claim should give: one exact complete source module; its declared input contract; its matched control; the exact source measurement; a universal simulation or correspondence proof; and finite examples only as implementation evidence.
