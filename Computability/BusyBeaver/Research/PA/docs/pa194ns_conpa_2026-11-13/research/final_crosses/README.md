# Bounded controller follow-up

This directory contains optional research supporting the scope of the final
search. None of these experiments supplies a sub-194 machine or a new
consistency theorem. The accepted result remains the fixed PA194NS package.

## Frozen grammar / zero-closing screen

`check_zero_crosses.py` tests precisely 20 cases: five frozen source trees
(primary PA194, PA194R, PA194Q, PA194D, alternative 68-reader PA194), two
final closures (the original unconditional jump or a decrement of X), and
two source-entry interfaces (the original row or the known-zero-X
specialization). Every case uses the PA194NS fixed controller. The grammar
normalization expands two- and four-increment terminal names into the
corresponding identical binary subtrees before deduplicating readers.

The script computes exact maximum matching in the inherited local-fold
opportunity relation. It filters all actual incoming rows for the required
previous-bit context, then uses the documented three-step helper template.
The matching size is an optimistic simultaneous-fold count: for a prospective
sub-194 score the script also enumerates the matching's helper choices and
checks the final local detours simultaneously. No case reached that stage,
because every optimistic state count was 194.

| Grammar | Raw states | Maximum matching | Optimistic count |
|---|---:|---:|---:|
| Primary | 202 | 8 | 194 |
| R | 202 | 8 | 194 |
| Q | 202 | 8 | 194 |
| D | 204 | 10 | 194 |
| Alternative 68-reader | 203 | 9 | 194 |

These figures were the same for all four closure/entry combinations. They
are scoped results for fixed trees and one fold template, not lower bounds
for arbitrary machines, broader folds, or other source transformations.
`zero_crosses_receipt.json` records every case, pair set, and grammar hash.

Reproduce from any current directory:

    python3 -B check_zero_crosses.py --package /path/to/pa194ns --output /new/receipt.json

## Top-only Shift experiment: 195 states

`build_top_only.py` keeps the no-push MP result in T and instead attempts to
test T directly in Shift. It transfers old T to X, transfers old H to T
without adding to X, sets H to one, and calls the symmetric destructive
comparison. The intended surviving Shift effect is the usual
`(H, tail(W), D, head(W))`, with halting when the old T is one.

The source replacements, relative to the pinned original source, are:

    node163 = (node6, node54)
    node168 = (node37, (dec H, node38))
    node171 = (node170, (inc H, continueTo 3))

The additional transfer-loop reader makes the count 203 raw controls minus
eight folds = 195. The exact native edits and all tables are in the portable
builder and `top195_recorded/`. Construction-level symbolic verification
checks 4,750 outcomes over arbitrary registers; the whole blank frame is
checked at 58,004 transitions. The experiment has no separate independent
literal-tape audit or completed new logical calibration and is not presented
as an accepted consistency-machine theorem.

    python3 -B build_top_only.py --package /path/to/pa194ns --output /new/top195

Both scripts use only Python's standard library and the pinned compiler in
the accompanying PA194NS package. Keep assertions enabled.
