# Exact 90-graph main evaluation

`TenPositive90MainRecipe.main_recipe` evaluates the main residual of the
selected `FreeJDirectMainGraph.graph` in an arbitrary commutative ring and
identifies it with the displayed factored expression. The argument is a
simplification of the actual Lean graph definition and keeps its computation
factored; no graph zero or numeric ports are assumed. Binding this expression
to a particular fresh witness, or to an external graph/PDF, is separate.

Accepted check: `observations/fixeddigits-attempt04/`, object
`/tmp/tenpositive-90mainrecipe-ok5bwir7/Direct90MainRecipe.olean`, SHA-256
`4ec8293088828b66c3e3d994a9612a18c22330c1983374d68fa9543eaac2404f`.
Attempt01 exhausted the 3-GiB Lean limit when expanding the polynomial;
attempt02 revealed the exact grouping; attempt03 had a superfluous final
tactic after simplification had closed the goal. All are retained. The runner
pins selected direct 90-graph objects and inherits the existing provider,
transitive source-object and dynamic-library limits.
