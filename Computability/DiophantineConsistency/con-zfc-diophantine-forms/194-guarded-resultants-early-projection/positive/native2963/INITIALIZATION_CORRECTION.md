# Correcting the compressed pages' initial head state

The first state-compression review checked all430 transitions but missed
one additional state occurrence in the native initialization tile. The
previous compressed pages kept the original initial head at state93.
Their claimed whole-language conjugacy was therefore not established.
This is a substantive calibration gap; equality of their reconstructed
coefficient bytes alone did not close it.

The original blank action writes1, moves right and enters state93. The
BFS state bijection fixes start0 and halt215 and sends93 to1. Accordingly
the initial head must be renamed too. In the complete943-tile language,
the initializer changes from `(3,436,4,188)` to `(3,436,4,4)`. In the
compact457-mode language it changes from `(3,4,4,698)` to
`(3,4,4,514)`. The displayed arithmetic recipe now defines this latter
entry as `(3,4,4,512+2u_0)`, using the already decoded first target.
The explicit first-action write/direction premise is checked too.

All four BFS-based TeX/PDF displays are corrected. Their action seeds,
radices, masks and three other coefficients are unchanged. Their new K
has434,054 bits and54,257 bytes, raw SHA256
`562494dbbe6e4651e55697f28596e801e341d50338bb902781c252912f3b2163`.
The former displays and receipts are retained under
[`history/pre-initializer-correction`](candidates/one-page-compression/history/pre-initializer-correction/README.md)
and explicitly marked superseded. Original-label pages, including the
722-character base62 variant, retain their entire original tuple.

## Full ordinary conjugacy argument

Let pi be the216-state bijection. The old vertical color `head(q,b)`
is mapped to `head(pi(q),b)`; bit colors0,1 and control colors434..438
stay fixed. Horizontal metadata colors0..5 stay fixed. The target-set
rank used for each right/left marker is recomputed after applying pi,
and the marker of q is mapped to the corresponding marker of pi(q).
These give separate bijections on the horizontal and vertical colors.

Applying these maps to the four sides of every old tile gives exactly
the943 new tiles, including the initialization, padding, start,
forbidden and halt tiles. Applying the inverse maps gives the reverse
inclusion. Thus mapping every edge color of any finite tiled rectangle
preserves adjacency, all allowed tiles and the designated boundary
conditions, in both directions. The induced finite-word/native-language
existence relation is equivalent. This is an ordinary proof for every
rectangle size; it is not inferred from bounded simulation.

The independent compact-mode check similarly maps all457 modes, with
separate horizontal target blocks and vertical head colors. Exact
arithmetic ranks and the collected selector reconstruct every coefficient
of the corrected whole tuple. The unchanged width/carry bounds apply to
these same bounded fields. This corrects the input to the inherited
uniform native/Pell theorem; it does not replace that theorem by a
finite coefficient calculation.

## Verification

[`check_page_state_conjugacy.py`](tools/check_page_state_conjugacy.py)
constructs the entire943-tile language from inert transitions, authenticates
its original literal hash, checks both color bijections and every tile,
then checks all457 compact modes. Deliberately restoring the old
initializer is rejected. Normal and optimized runs give identical
[`INITIALIZATION_CORRECTION.json`](candidates/one-page-compression/INITIALIZATION_CORRECTION.json).
The correction also emerged independently during the compact44 page
construction, which checks its own full943-tile language.

Both normal and optimized coefficient/page generators pass after the
correction. All four BFS PDFs have exactly one page, no overfull boxes,
and recover every printed seed character. The shortest recipe now has
2,297 nonwhite characters, four more than its superseded version. The
corrected771-digit collected recipe has2,518; the improvement remains
221 characters, approximately8.8%. The original tuple replay continues
to match all215,492 raw coefficient bytes exactly.

No Lean file was edited or run. The ordinary compiler/calculus
dependencies and the open internal-ZFC formalization remain explicit.
