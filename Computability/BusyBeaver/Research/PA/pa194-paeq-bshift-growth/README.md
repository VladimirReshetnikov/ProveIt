# PAeq bound-variable shift and qVec growth

This package adapts the existing arithmetic-language shift-growth and qVec
trace arguments to the PAeq target language. In every IΣ₁ arithmetic model,
`termBShift_le` bounds an arbitrary target term-code shift by the displayed
`tau` expression; the essential target-language fact is that its function
symbols have arity at most two. `qVec_le` uses the same majorant as the
arithmetic-language qVec bound. Both apply to nonstandard input codes.

`bounded_trace_explicit` constructs the actual PAeq qVec history at any
model-internal length and bounds all its entries by a single arithmetic tower
value. `paired_source_target_traces` constructs both arithmetic and PAeq
qVec histories from the same seed, proving that same tower value bounds all
entries in both histories. These are internal coded traces, not external
iterations over standard naturals.

The port does not bound target PAeq substitution outputs or graph witnesses,
the formula-translation graph, or prove substitution compatibility. The
hashes identify the adapted PA196 input files; the current-Foundation target
language and its coding are checked separately in `pa194-paeq-formula`.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-bshift-growth/check.sh
```

The four target-side modules passed ordered suffix checks against the
retained PA196 prerequisites and audited project and Foundation objects; the
printed axioms contain no `sorryAx`. The generated wrapper was syntax-checked;
the full prerequisite-prefix replay remains pending.
