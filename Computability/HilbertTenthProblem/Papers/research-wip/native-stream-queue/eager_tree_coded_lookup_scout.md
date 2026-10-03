# Zero-preserving triple codes for finite eager Tree lookups

This bounded source scout replaces nine field-lookup residuals per row of the
[constructor-projected packet](eager_tree_constructor_projection.md) by three
coded-lookup residuals. It preserves **exactly the same complete natural zero
tuples**, with no new or deleted supplied coordinates. At external size `N=8`,
with the parent's existing constant cleanup enabled, the best degree-10
schedule tested costs **1,172 = 445 multiplications + 727 additions/subtractions**,
versus the complete parent's 1,456. A separate degree-12 schedule costs
**1,156 = 445 multiplications + 711 additions/subtractions**. Both have 188
natural witnesses and 91 residuals. These are finite-certificate tradeoffs,
not a fixed-arity universal Diophantine construction or a paid ordinary-input
loader.

The [source](eager_tree_coded_lookup_scout.py) and
[deterministic receipt](eager_tree_coded_lookup_scout.json) pin the entire
constructor parent Python/JSON/proof trio. They read the complete saved parent
circuits without executing historical Python. The public prototype accepts
exact `N=1,...,8`; the same formulas and proof apply to the displayed uniform
external-`N` templates. It does not claim to expose an implementation for
arbitrary `N`.

## Injective natural code and the inactive-slot boundary

Put

\[
P(u,v)=(u+v)^2+u,\qquad C(x,y,z)=P(z,P(x,y)).
\]

For naturals, let `s=u+v`. Then `s² ≤ P(u,v) ≤ s²+s`, and these intervals for
successive integer `s` are disjoint because `s²+s < (s+1)²`. Thus `P` determines
`s`, then `u=P-s²`, then `v=s-u`. It is injective on natural pairs; nested
pairing is injective on natural triples in each of the six coordinate orders.
Also `P(0,0)=C(0,0,0)=0`. A pair costs exactly one addition for the sum, one
multiplication for its square, and one addition for the selected component;
a triple costs two multiplications and four additions before sharing.

Zero preservation is essential. Reusing the Tree constructor
`F(u,v)=(u+v)(u+v+1)+2v+2` itself would give a nonzero code for the zero target,
although an inactive slot has lookup sum zero. The proposed code has no such
constant offset. Injectivity is specifically over naturals: `P(-1,0)=P(0,0)`;
even on the nonnegative rational orthant,
`P(7/16,5/16)=P(0,1)=1`. These local examples delimit the proof and do not claim
to be complete signed or real counterexamples to the Tree packet.

## Exact zero-tuple theorem

Write a row's tags as `t0,...,t4`. The unchanged natural one-hot equation
`sum(t)=1` makes each tag zero or one. Put `A=t3+t4`. The unchanged pointer
row sums are `A,A,t3`. Since every pointer is natural, each slot therefore
has either all pointers zero or exactly one pointer equal to one. Strict
forwardness is already part of the parent interface: row `i` references only
rows `j>i`.

Let `(x_j,y_j,z_j)` denote a referenced row triple and use the row's unchanged
natural local fields `a,b,u,v,y,z`. The new degree-10 target codes are

\[
\begin{aligned}
D_0&=t_3 C(b,y,u)+t_4 C(y,a,u),\\
D_1&=t_3 C(a,y,v)+t_4 C(u,b,z),\\
D_2&=t_3 C(u,v,z).
\end{aligned}
\]

Replace the old three coordinate equations in slot `s` by

\[
R_{i,s}=\sum_{j>i}p_{i,s,j} C(x_j,y_j,z_j)-D_s=0.
\]

On an inactive slot both sides vanish, including the original three weighted
target coordinates. On an active slot the sum selects one natural row triple,
and exactly one branch is selected. Code injectivity makes its one new
comparison equivalent to all three original field comparisons. This proves
both directions of equivalence once the common one-hot and row-sum equations
are zero. All remaining residuals are unchanged. Both complete finalizers are
sums of squares, so a complete natural zero first forces those common
equations; hence the argument is not circular. It applies to every row,
including the last row with no available references. No reachable-row,
computation-minimality, or nonzero-input assumption is added.

All coordinates are unchanged, so this is a same-tuple natural-zero theorem,
stronger than a represented-triple existence statement. Composing it with
the constructor graph restoration gives the earlier triangular-parent
zero-fiber bijection. The earlier normalization from the unrestricted flow
parent still only preserves represented triples at each external `N`.

## Paid reuse and separate degree-12 chart

The existing `e=F(a,y)` construction already pays for
`s=a+y` and `p=s(s+1)`. Two exact all-value identities are

\[
P(a,y)=p-y,\qquad P(y,a)=p-a.
\]

The source verifies the literal existing constructor cone before reusing `p`.
For `C=P(z,P(x,y))`, these two inner pairs occur in different branch targets.
Each now costs one subtraction. This saves four gates per row compared with
two independent three-gate pair calls. The paid product remains live through the
retained output residual `t1*(z-F(a,y))`; the defining `e` equation was already
removed by the constructor projection. Neither its cost nor that of `q=F(0,b)` or
other parent arithmetic disappears from accounting. The source records the
available per-row pair recipes, which some enumerated coordinate orders do
not use. Optional syntactic sharing applies only to new code operations;
it never deduplicates old source rows globally.

The separate `hybrid` chart replaces only `D0` by

\[
H=t_3P(b,y)+t_4P(y,a),\qquad D_0'=P(Au,H).
\]

For each permitted `(t3,t4)=(0,0),(1,0),(0,1)`, this equals `D0` exactly, with
zero in the inactive case. This is a zero-set argument under common tag
conditions, **not** an all-value polynomial identity. It saves two additional
additions per row. The existing paid `A=t3+t4` port is reused explicitly.
The other target codes remain branch-gated.

For comparison, the `weighted` chart applies `C` directly to each of the
parent's three weighted target-coordinate triples. Zero preservation and
injectivity give the same natural zero theorem, but this chart raises degree
to 16 and is dominated in the tested cost/degree comparison.

## Complete literal ledgers and degree

Every code operation, lookup multiplication, residual subtraction, square,
and final sum addition is included. Row 0's triple code is never emitted:
strictly forward pointers cannot reference it. There are only `N-1` row
codes. This removes six otherwise dead gates from a naive estimate.

Let `c=0` mean selective parent cleanup and `c=1` mean its existing extra
constant cleanup. All schedules retain `(3N²+23N)/2` natural witnesses and
have `11N+3` residuals. The complete degree-10 schedule using the two paid
pair identities has

\[
M=\frac{3N^2+87N+2}{2},\quad
A=3N^2+(67-c)N+7,\quad
M+A=\frac{9N^2+(221-2c)N+16}{2}.
\]

It saves `6N²-14N+12` operations from the matching constructor parent. The
hybrid chart has the same multiplication count and two fewer additions per
row: replace `67-c` by `65-c`, or `221-2c` by `217-2c`. It saves
`6N²-12N+12` complete operations. These identities include `N=1` and `N=2`.
With cleanup enabled:

| N | Parent degree 10 | Coded degree 10 | Hybrid degree 12 | Natural witnesses | New residuals |
|---:|---:|---:|---:|---:|---:|
| 1 | 126 | 122 | 120 | 13 | 14 |
| 2 | 253 | 245 | 241 | 29 | 25 |
| 3 | 401 | 377 | 371 | 48 | 36 |
| 4 | 570 | 518 | 510 | 70 | 47 |
| 8 | 1456 | 1172 | 1156 | 188 | 91 |

Without new sharing or paid-pair reuse, either the basic gated chart or the
weighted chart costs `(9N²+(229-2c)N+16)/2`. Their multiplication counts differ:
`(3N²+91N+2)/2` gated versus `(3N²+101N+2)/2` weighted. Their respective
addition counts are `3N²+(69-c)N+7` and `3N²+(64-c)N+7`. At `N=8,c=1` both
cost 1,204. New-only syntactic sharing across six tested coordinate orders
reaches 1,180; exact paid-pair reuse reaches 1,172. These are results in the
specified small schedule family, not unrestricted arithmetic lower bounds.

For the gated chart, code degree is four, and multiplication by a branch or
pointer makes residual degree at most five. The retained constructor-input
residual already has nonzero degree five, so the complete SOS has exact
degree ten. In the hybrid chart, the first target has degree-six leader
`[t3(b+y)²+t4(a+y)²]²`; its square gives degree twelve. In the weighted chart
a degree-two weighted coordinate enters a degree-four code, producing a
nonzero degree-eight residual and exact degree sixteen. For every saved
schedule the receipt expands actual residual coefficients and checks the
nonzero maximum. The SOS of highest real homogeneous forms cannot cancel.

## Complete polynomial relation and reproducible scope

Although zero tuples agree, the full polynomials generally differ. If `L_old`
is the set of nine old field residuals per row, `R_new` the three coded
residuals, and all coordinates are supplied unchanged, the exact all-value
identity is

\[
F_{new}-F_{old}=\sum R_{new}^2-\sum L_{old}^2.
\]

The checker verifies all retained arithmetic rows literally, the complete
retained residual list, and both fully paid finalizers. It also evaluates the
entire correction on signed integer and rational assignments. This correction
is not described as polynomial equality or as signed-zero equivalence.

The census emits 416 schedules: eight sizes, two parent cleanup options,
six coordinate orders with both new-code-sharing and paid-pair options,
plus one weighted and one hybrid chart. These are 416 recipes, **not** 416
assertedly distinct polynomials. The receipt saves all census ledgers/hashes
and 19 full selected packets, including every best degree-10 size/cleanup
pair and the size-eight comparison charts. No universal source or native
Pell witness is constructed or claimed.

The writer passed 416 complete residual-degree and liveness checks, 1,248
full polynomial corrections (416 rational), 16,848 literal target values,
156 exact generic target coefficient identities, 468 exact active/inactive
chart identities, 13,182 finite injectivity examples, and 24,576 finite
active comparisons. A separate exact eager evaluator produced 99 complete
natural zeros across all five root rules and padding sizes; another 6,912
single-coordinate natural perturbations preserve the old/new zero verdict.
These finite tests supplement the general proof above. The source also checks
59 malformed calls, five defensive copies, three warmed parent pins, and
rejection under Python `-O`. The public scope is this bounded scout interface,
not a general hostile-input compiler service.

Replay from any working directory, with the three pinned constructor files
under `ROOT`:

```sh
python eager_tree_coded_lookup_scout.py --root ROOT \
  --expect eager_tree_coded_lookup_scout.json
```

Use `--output FILE` to write a fresh receipt. No repository files, archive
originals, or Git state were modified by this scout. The receipt performs no
historical author-suite reruns and imports no historical compiler modules.
