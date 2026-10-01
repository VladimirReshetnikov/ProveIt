# A dominated terminal endpoint gives256 operations

The [literal builder](neary_woods_universal_height256.py) removes one addition
from the [257-operation history-scale compiler](neary_woods_universal_history_scale257.md).
The default complete polynomial has **256=133M+123A**, **43 positive
witnesses**, four positive program parameters, ordinary positive input and
degree **at most1384**. Its certificate has255 operations and one final
product comparison. The separate fifth duration-bound interface is supported.
The [receipt](neary_woods_universal_height256.json) records complete emitted
sources, counts, affine identities and positive endpoint checks.

The accepted ordinary inputs are unchanged on the inherited valid shifted
program slices. The fixed program-offset convention, paid duration floor,
loader, physical counter, native sign arguments and universal U9 table are
unchanged. The saving uses the already paid terminal relation. It is separate
from the established75/87 results.

## 1. The redundant height contribution

Write W for the emitted `load__tag_input`, U_f for `hist__Ufinal`, and V_f
for the computed lower endpoint. On a valid shifted program slice the true
initial sentinel is V_0=W+1. The unchanged terminal rows implement

    V_f=t*U_f+c,
    t=2^(beta+1), c=2^beta, beta>=2.                 (1)

This is the terminal suffix in the [four-tile word representation](binary_tag_four_tile_history.md),
Section3. Both fixed numerals are positive before any equation is imposed.
Indeed the following argument only needs t,c>=1. All supplied coordinates
are positive, and the unchanged loader makes W>=1. Thus

    V_f>=U_f+1>=2.                                  (2)

The parent height and the new height are respectively

    D_parent=U_f+W+V_f+eta_parent,
    D_new=W+V_f+eta_new.                            (3)

The new definition gives all of the bounds needed for decoding before
native typing:

    D_new>=4,
    1<D_new,
    U_f<V_f<D_new,
    W+1<D_new.                                     (4)

The last strict inequality follows from V_f+eta_new>=3. It also bounds
the alternative initial value W-1 arising from a negative lower-transport
unit. On valid sentinel slices that alternative is positive; the weaker
nonnegative bound already follows from W>=1. No terminal equation or
assumed history semantics was used to prove(2)--(4): equation(1) is an
actual computed source definition.

## 2. Direct soundness and positive completeness

At a new positive zero every factor of each paid group is an integer unit.
The pretyping proof of257 uses the height only through D>=4, the actual
radix b=c_h*D with c_h>=8, and the positive range expression(D-1)J.
All are retained by(4). In particular P is still the positive sum of the
six supplied history quantities, P>=6, and the signed repunit still gives

    P=(b-1)J+epsilon, epsilon in{-1,+1},
    J>=1, b<=P+2, J<=P/6.

Consequently the same weak-repunit carry bounds give positive computed
native truth fields before any bit typing. The independent local native
rank argument, joint-index sign exclusion, paid-loader geometry-index
exclusion and mask-unit sign argument apply in their previous order.
They use the unchanged loader/duration bounds and these history margins;
they do not require D to exceed the sum of the three endpoints. The
native scale is then dyadic. The top history lanes and the Mersenne
obstruction of257 exclude the negative history-repunit sign without
assuming that sign in advance.

After typing, the range lanes bound each history digit by D-1. The
[slope-class history proof](pcp_affine_slope_class_history.md), Section3,
uses precisely the individual endpoint bounds, not an aggregate endpoint
sum, to compare the chronological expansions. Its local affine bound
a_i(D-1)+c_i<b is unchanged because b=c_h*D. The four endpoint digits are
1, U_f, V_f and the lower initial digit W+epsilon_L. Every one is below D
by(4). Thus both transport equations decode without carries. In the
negative lower branch the initial digit is W-1=V_0-2; the inherited
sentinel obstruction excludes it on valid program slices. The positive
branch has initial digit W+1=V_0 and recovers the genuine tag history.
The unchanged ordinary-input loader and physical-counter theorem then
give the same accepted ordinary input relation.

This is a direct soundness argument. It does not apply the parent's
positive-zero theorem to a nonpositive height slack. The global-bound
shift used in257 remains valid internally: its typed lower bound
beta_new>=((c_h-4)D+3)J-2>=17 also requires only D>=4.

Conversely, start with any positive parent257 zero on a valid program/input
slice, supplied by its complete universal-input theorem. Keep every other
coordinate fixed and set

    eta_new=eta_parent+U_f>0.                       (5)

Then(3) gives exactly the same D. Every later source value, unit factor,
group and finalizer is identical. This proves positive completeness for
every supported grouping and strong/scale choice. The parameter recipe
and ordinary input do not change. Soundness and completeness together
prove accepted-input equivalence on those valid slices.

## 3. Exact affine identity and its domain

For arbitrary integer assignments, including arbitrary integer
specializations of the fixed-numeral slots, define

    eta_parent=eta_new-U_f.                         (6)

The old private first sum is U_f+W; the old second sum is U_f+W+V_f,
which exceeds the new second sum W+V_f by U_f. Equation(6) therefore
makes the emitted height exactly equal. All other retained registers,
unit factors, residuals and complete polynomial outputs agree. Maps(5)
and(6) are inverse affine maps on the unrestricted integer coordinates.

The inverse map(6) need not preserve positivity: eta_new=U_f gives
eta_parent=0, while eta_new=1,U_f=2 gives eta_parent=-1. The checker
includes both boundaries. They are algebraic assignments, not asserted
complete native zeros. The theorem claims neither equality of positive
zero sets on the same tuples nor a positive-zero bijection.

The literal edit deletes `hist__height_sum__0` and changes
`hist__height_sum__1` to `hist__tag_terminal+load__tag_input`. The final
height addition stays paid. Guards reconstruct the whole canonical257
caller, including every ordinary domain/interface and unit-group schedule,
or reconstruct an exact grouping from its frozen partition engine. They
then check both endpoint-definition rows, the private sum/slack consumers
and recursive active exports. Both private sums are excluded from public
interfaces. Every emitted gate must reach the complete polynomial output.

## 4. Counts, degrees and inherited schedules

Exactly one addition disappears. No witness, comparison, multiplier or
fixed numeral is removed. The source propagates the same complete degree
dictionary as its parent, checked separately for every emitted schedule.
In particular D still has degree at most3 through W, P has degree1 through
the witness sum, and the default factor bounds remain

    14,40,9,209,490,114,24,264,6,96,6,96,4,4,4,4.

Their sum is1384. These are conservative bounds, not exact polynomial
degrees or circuit lower bounds.

The [frozen history-scale partition family](neary_woods_universal_history_scale_partitions.md)
can be rewritten uniformly. Each of its16 strong/scale bases and every
grouping has the same private height subgraph; the edit leaves all factor
weights and residual degrees unchanged and subtracts one operation.
Therefore its proven finite-family frontier shifts uniformly to

| Operations | Degree bound | Witnesses |
|---:|---:|---:|
|256|1384|43|
|258|1242|43|
|259|1196|43|
|260|858|43|
|261|606|44|
|262|560|44|
|263|458|44|
|264|412|44|
|265|306|44|
|266|276|44|
|267|230|44|
|268|212|44|

With43 witnesses fixed, the low-degree endpoint becomes264/456; with45
witnesses fixed it becomes271/212. This is an inherited uniform shift,
not a new optimization outside that finite grouping family. The builder
also retains both program-bound interfaces. Historical ancestor packets
are provenance and are not reapplied to the modified graph.

## 5. Reproducible validation

```sh
python3 neary_woods_universal_height256.py
```

The checker reconstructs the affine maps independently of the edited rows,
compares all retained source registers and complete outputs on signed and
positive assignments, tests positive parent projections, and forces zero
and negative affine parent gaps. Separate endpoint fixtures cover the
smallest positive terminal numerals as well as larger values. Literal
operation counts, unchanged degree dictionaries, source closure and
incompatible-caller rejections are checked for every supported context.
These are algebraic and domain checks; no full native Pell tuple is
claimed from a small test assignment.

The author writer and final fresh replay pass. The receipt covers82
literal ledgers,1312 complete affine output/register identities,
328 signed assignments,656 positive parent projections,164 zero/negative
affine parent-height boundaries,1500 independent endpoint/domain cases
and seven incompatible-caller rejections.

Gibbs independently reviewed the full proof, source and257/259 dependencies
and ran a fresh default replay, with no findings. His separate literal
executor and manual affine maps checked56 contexts:448 complete
source/output lifts,224 signed, including112 nonpositive parent-height
boundaries, and448 positive parent projections. He also checked108
endpoint fixtures,1296 weak-history fixtures, six malformed callers and
all six local links. These are algebraic/domain fixtures, not complete
Pell zeros. Root's independent full proof/source/dependency review and
fresh replay also pass. A separate executor and manual affine map check
240 complete outputs and retained-register identities across ten new
contexts, including120 signed assignments and138 nonpositive algebraic
parent gaps. Both bound interfaces and the43/44/45-witness endpoints are
covered. No mathematical findings remain.
