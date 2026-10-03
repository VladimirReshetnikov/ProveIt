# Per-step branch choices lower the complete two-step circuits to 44 / 43

The [safe composed emitter](three_mass_projected_endpoint_penalties.md) already
allows a different omitted selector at each source step. Exhausting that finite
choice on the four worked examples lowers the native / compact-clean
`INC2;DEC2` circuits from **46 / 45 to 44 / 43 operations**. The three-increment
circuits stay at **86 / 83**. Witness counts remain six and fifteen, and the
complete degree remains three.

This introduces no new emitter rewrite. Every original source condition,
endpoint and domain requirement remains enforced by the reviewed construction.
The selected endpoint mode can differ from the uniform baseline. At each step the omitted
selector is still restored as one minus the sum of all the retained selectors.
The already reviewed grouped nonnegativity proof applies independently at
each step and does not require the omitted index to be constant in time.
The selector and endpoint counterexamples and their paid guards remain valid.

In particular, choosing omitted indices `[0,1]` for the two-step source does
not assume that those branches were executed. The remaining selectors and
masses still represent every supplied tuple, and the complete polynomial
enforces the execution. Projection and unique natural restoration give the
same complete natural zero fibers as the original certificate.

## Actual finite search and fully paid winners

The [search helper](three_mass_mixed_branch_search.py) authenticates all six
compiler/review dependencies before executing their source bytes. Original
producer archives are authenticated by the reviewed mass-parent loader.
It enumerates every element of `{0,...,B-1}^h`, each of the direct, factored,
and Horner guard schedules, and each of no/initial/terminal/both endpoint
replacement. Thus there are exactly `12 B^h` emitted candidates per fixture.
Duplicate polynomials or schedules remain in this count.

The earlier comparison searched only constant branch-index lists. The new
helper extracts that exact subset as its baseline, including the no-endpoint
option on both sides. Ties are broken by fewer multiplications, then the
documented enumeration order. All affine loaders, state/value/clock rows,
projected endpoint penalties, squaring, guards, and final summations are paid
by the same compiler and metric.

| Fixed source and endpoint interface | Constant-index best | New complete cost | Omitted indices | Guard / endpoints | Witnesses |
|---|---:|---:|---|---|---:|
| `INC2;DEC2`, h=2, native y,T |46|16M+28A=44|0,1|Horner / both|6|
| Same, compact-clean T |45|17M+26A=43|0,1|Horner / both|6|
| Three `INC2`, h=3, native y,T |86|26M+60A=86|1,1,1|Factored / both|15|
| Same, compact-clean T |83|26M+57A=83|1,1,1|Factored / both|15|

These are minima over the stated 744 emitted candidates across four fixed
fixtures, not unrestricted arithmetic optima. The two-step examples explore
four layouts each; the three-step examples explore 27 each. There is no claim
that the constant-index choice is optimal for other programs or horizons.

For reference, the earlier fully paid mass-coordinate circuits were 56 / 56
and 107 / 105 respectively. The degree-two endpoint-only alternative costs
51 / 51 and 100 / 98, keeping eight / eighteen witnesses instead. Comparisons
must retain these degree and witness differences.

## Evidence and reproduction

For every emitted candidate the helper invokes the already independently
written, source-pinned [complete polynomial auditor](review_three_mass_projected_endpoint_penalties.md).
Its own sparse coefficient model reconstructs the entire polynomial from the
original exporter certificate and literal endpoint masks, validates every
residual/guard port, checks the exact cubic degree, and counts only live paid
gates. It does not rely on a successful simulated execution to infer the
polynomial identity or gate count.

The [receipt](three_mass_mixed_branch_search.json) records 62 complete branch
layouts, 744 complete coefficient/degree/ledger checks, 63,388 paid live gates,
5,388 retained residuals, and 2,136 whole weighted guards. It retains every
candidate ledger, each full winning circuit and original certificate, and
16 actual complete natural witness projections/restorations through the
original offsets. No core emitter changed. These checks reuse an independently
reviewed auditor; they are not a second implementation of its algebra engine.

```sh
python3 three_mass_mixed_branch_search.py \
  --root /path/to/native-stream-queue --repo /path/to/Proofs \
  --expect three_mass_mixed_branch_search.json
```

`--output PATH` writes a fresh deterministic receipt. Saved comparisons are
recursive and type-sensitive. The helper needs only standard-library Python
and read-only Git, and changes no original report or repository state.

The complete construction still has an external source table and horizon,
a paid raw `x+1` loader, and the inherited fixed-name research-emitter
interface. It supplies neither an ordinary-counter decoder nor a fixed-arity
unbounded-history representation. The universal polynomial bound remains 87.

The [independent search review](review_three_mass_mixed_branch_search.md)
reconstructs the complete ordered grid, regenerates and recounts all 744
schedules, checks the constant-index subset and tie convention, and verifies
all four full winning polynomials with the pinned independent engine. Root
read the full helper/note and replayed its receipt, as well as the author
receipt. No source or receipt correction was requested.
