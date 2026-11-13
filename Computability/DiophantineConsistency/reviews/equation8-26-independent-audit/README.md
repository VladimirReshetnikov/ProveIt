# Independent staged 26-variable display audit

The staged [TeX](../../research/adaptive-square-sums26-degree8/equation8-26.tex)
and [PDF](../../research/adaptive-square-sums26-degree8/equation8-26.pdf)
passed the finite independent audit in [`audit.py`](audit.py). The observed
session 62956 exited 0 with [receipt](receipt.json) SHA-256
`51a8b3eb9db964795c14505df38f522fd485ea647f0529974a34a0da1cf8448d`.
The PDF SHA-256 is
`47a78ee00d5868e383e4de6e7ea2ad829e8a85385f5b9486837c1450a2af5310`.

The audit independently follows all 126 printed gate rows and aliases against
the pinned live candidate graph, checks graph topology and liveness, matches
all 26 variables and four fixed ports to the exact historical Lean literal
source used in the author run, and uses the sparse-polynomial display checker
for all 39 definitions and 17 residual squares. It exercises sign, extra-square,
unknown-name and gate-operation mutations. The four-fixed-integer TeX block is
byte-identical to the original base-10 `equation.tex` block; this is not a
formal parsing or proof of that block's decoder/rank recipes. Two clean builds
produce the identical two-page PDF without TeX warnings. Both recorded page
images were visually inspected; no clipping or overlap was apparent, and the
long circuit rows wrap across lines within their columns.

The script deliberately requires normal Python: observed `-O` and `-OO`
invocations each exited 1 at the explicit guard. The check is finite display,
graph and historical source-binding evidence. It is not a second Lean replay,
a paired or source-current equivalence proof, a Lean degree theorem, or a
proof of global minimality. The inherited Foundation-wrapper, package and
dynamic-load limitations remain. The historical fixed constant recipe retains
the separate manually transcribed TeX interpretation noted in the 14-variable
binding audit. The status descriptions in the main README, proof plan and both
26-variable research READMEs were reviewed against the recorded 30-module
single-overlay author pass and independent artifact audit; their claims and
document links match the author-only scope.
