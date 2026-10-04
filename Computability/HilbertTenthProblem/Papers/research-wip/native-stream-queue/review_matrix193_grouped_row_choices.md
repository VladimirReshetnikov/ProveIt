# Independent review of grouped synchronized matrix transitions

**PASS, with local and fixed-duration scope.** The grouped construction
saves24 additions in each complete local source and preserves the exact
real transition relation. It does not supply an unbounded fixed-arity
Diophantine simulation or improve the established84-operation bound.

The reviewed author files have SHA256:

- `matrix193_grouped_row_choices.py`: `b2d850448f71ea8af8fc3bee3f3a95cb073f14ea1e65c8403618ebbf1bce3da6`
- `matrix193_grouped_row_choices.json`: `d70f8038b4110c3a8ce7579071dc779782958e69347bba7f628026b16521d260`
- `matrix193_grouped_row_choices.md`: `aa84987b2d28ed4b7c28ef0b8af6ce3c9f0de288415081834a37a169f8afc0f8`

I read the whole new helper and proof, its6 parent pin declarations, and
the literal emitted interfaces. Only the new helper was executed; all
frozen parent code was authenticated and treated as inert data. Fresh
normal and optimized replay against installed paths agrees with the
saved receipt.

For a fixed upper matrix K the replacement is
`prod_i(A_K+B_i)` by `A_K+prod_i B_i`. On real supplied ports all A_K and
B_i are sums of scalar squares, hence nonnegative. Either expression is
zero exactly when A_K=0 and at least one of its own group's B_i=0.
Grouping by the actual equal K values therefore retains the synchronized
choice of upper and lower actions. This argument would fail for arbitrary
signed polynomial factors or over complex numbers; neither is used here.
The note explicitly avoids claiming off-zero polynomial identity.

The saved inventory partitions all96 original tiles into72 groups
(56 singles,9 pairs,6 triples,1 quadruple). Each size-d group saves d-1
additions. Its d-1 internal multiplications plus the71 outer ones total95,
so the multiplication count is unchanged. The source independently
expands336 scalar residuals and2096 group coefficients, checks every
original identifier exactly once, and audits all live producers. The
resulting totals are2015=1103M+912A and2041=1115M+926A.

The countdown suffix retains all26 paid operations, both counter-square
guards and the original loader. Its independent62-coefficient check
proves `E_load*(P_grouped+n²+n'²)`. Thus a local zero is precisely LOAD
or an original TILE with n=n'=0. A finite path from n=x to n=0 has
exactly x loads; a load after any tile would make its endpoint negative
with no future increasing transition. Therefore accepted words remain
`LOAD^x TILE*`, even with signed counters. Integral initial rows and
integer affine actions force integral rows along any such real path.

Setting next_y0=t and all other ports to0 gives the complete polynomials
t^192 and t^194+t^192, respectively. These agree with gate-propagated
upper bounds192 and194 and prove exact degrees. The former next_x0
degree line is correctly discarded for this new off-zero polynomial.

For fixed h steps, summing h nonnegative2041-gate outputs and the paid
7-gate endpoint uses h additional additions:2042h+7 gates and5h signed
witnesses. Direct initialization costs0 gates. The analogous supplied-
target bound2016d+5 also counts all joins. These are copied-schedule
upper bounds; no exact degree after endpoint substitution or uniform
operation count across unrelated fixed-program tables is claimed.

The228 finite whole-source checks support the exact algebraic argument;
they are not used as a proof of unbounded simulation. The remaining
unbounded packing and positive-witness conversion obligations are stated
explicitly in the author note and receipt.
