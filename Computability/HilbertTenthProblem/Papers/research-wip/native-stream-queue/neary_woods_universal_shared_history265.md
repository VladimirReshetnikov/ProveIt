# Share paid powers, selector prefixes and the radix decrement

The [positive-mask-unit successor](neary_woods_universal_mask_unit263.md)
gives263=134M+129A,252 certificate operations,4 comparisons,43 witnesses
and degree at most3857. It preserves the complete positive zero set on
the same supplied coordinates; off-zero values have explicit corrections.
Its mapped273/608 option uses44 witnesses. The exact integer identities
and all historical265 counts below remain unchanged.

The [factored partition compiler](neary_woods_universal_computed_ports_partitions.md)
has an exact algebraic successor costing **265=134M+131A**, with
**251=129M+122A certificate operations**, **five comparisons**, **43
positive witnesses**, four positive program parameters and degree at
most 3853. Three independent identities remove two multiplications and
two additions. No supplied coordinate or comparison changes.

The [source](neary_woods_universal_shared_history265.py) and
[receipt](neary_woods_universal_shared_history265.json) contain the
complete polynomial schedules and deterministic checks. The same
rewrites give degree at most 608 at 275 operations with 44 witnesses.
Every complete polynomial is identical to its corresponding parent,
including values on signed assignments. The separate 75-operation
certificate and 87-operation universal polynomial are unchanged.

## 1. Reuse a cubic in the four-term repunit

Write \(P\) for `hist__P__10`. The parent already pays for

\[
 P_2=P^2,\quad P_3=P_2P,\quad T_1=P+1,\quad T_2=P_2+T_1.
\]

It also computes a private \(P_2+1\) and then

\[
 R_4=T_1(P_2+1)=1+P+P^2+P^3.
\]

Instead set

\[
 R_4=P_3+T_2.
\]

Delete the private `hist__repunit_factor__52` addition and replace
the multiplication producing `hist__repunit_product__53` by that sum.
Two gates, one addition and one multiplication, become one addition:
**one multiplication is saved**. The tail and cubic already serve
other parts of the history, and remain fully charged. The identity
holds for every integer \(P\), including zero and negative values.

## 2. Reuse the selected-mask prefix in the controller word

Write \(S_i\) for the positive supplied `hist__Shat` coordinates;
no Boolean or one-hot interpretation is needed for this identity.
The parent controller word is

\[
 C=S_0+P\bigl(S_1+P(S_2+PS_3)\bigr).
\]

Its selected-mask construction separately already pays for

\[
 T=S_0+PS_1.
\]

The parent also computes \(V=S_2+PS_3\) as the first controller
Horner stage. Therefore use

\[
 C=T+P_2V.
\]

The old suffix after \(V\) consists of two multiplications and two
additions. The replacement uses one multiplication and one addition:
**one multiplication and one addition are saved**. Concretely, delete
the three private intermediate registers `hist__pack_product__46`,
`hist__pack_sum__47`, `hist__pack_product__48`; create the new product
`shared_history_selector_high`; retain the old final word name
`hist__pack_sum__49` with its unchanged value. Naming the replacement
product separately avoids presenting a changed intermediate value as
the old register's value.

The existing prefix \(T\), cubic and tail occur later in the parent's
literal order. A stable topological sort moves their producers before
their new consumers. Their dependencies are just the already paid
radix powers and supplied selectors, so neither reuse creates a cycle.

## 3. Reuse the paid radix decrement

The recoder already computes `Bm1=B-1`. It separately computes
`twiceB=B+B` solely to obtain `twiceBm1=twiceB-1`. Replace these
last two additions/subtractions by

\[
 \texttt{twiceBm1}=B+\texttt{Bm1}=2B-1.
\]

The result and all its consumers are unchanged; the private `twiceB`
register disappears. This saves **one addition** for every integer
\(B\). Root's independent local-expression scan found this third
identity while the first two rewrites were being implemented. That
bounded discovery scan is not used as an optimality argument.

The three transformations are disjoint except for common unchanged
inputs. All seven nonempty subsets are supported by the `repunit`,
`selectors` and `radix` flags. Starting from the default269 source:

| Enabled identities | Polynomial operations | Multiplications | Additions/subtractions |
|---|---:|---:|---:|
| Repunit | 268 | 135 | 133 |
| Selector prefix | 267 | 135 | 132 |
| Radix decrement | 268 | 136 | 132 |
| Repunit, selector prefix | 266 | 134 | 132 |
| Repunit, radix decrement | 267 | 135 | 132 |
| Selector prefix, radix decrement | 266 | 135 | 131 |
| All three | 265 | 134 | 131 |

Every listed source retains 43 positive witnesses, five comparisons,
the same parameters and degree bound 3853.

## 4. Complete polynomial and domain preservation

`rewrite` guards the exact producers of all referenced powers, tails,
selector prefixes and radix expressions. Every erased register must
have only a replaced arithmetic consumer. It must also be absent from
supplied coordinates, comparisons, unit factors, group products and
all nested public/interface trees, including the live fusion and
projected-coordinate interfaces. The new product name must be fresh.
These checks reject unrelated callers rather than silently discarding
their observable intermediate values.

All retained parent registers have identical values on every supplied
integer tuple. In particular all native norm/index/linear factors,
each group product and every comparison agree. The unchanged finalizer
therefore gives

\[
 P_{\mathrm{new}}(v)=P_{\mathrm{parent}}(v)
 \qquad\text{for every integer supplied tuple }v.
\]

The supplied parameters and witness lists are identical. The identity
map is thus a bijection of the full positive zero sets, even before
restricting to valid program parameters. The interpretation as a
universal ordinary-input polynomial still uses the parent's effective
valid U9 program slices, paid input loader and synchronized leading-zero
padding. No new interpretation of arbitrary program parameters is
asserted, and no native sign/rank or witness-existence argument changes.

`restore_parent_registers` reconstructs the erased internal values
solely for diagnostics. It introduces no supplied coordinates and its
unused reconstruction arithmetic is not part of the emitted circuit.
To replay an earlier helper that requires the parent graph, use the
stored `shared_history_parent` with the same supplied tuple. Historical
partition records retain their parent schedules; `ledger` obtains the
successor's counts directly from its actual source.

## 5. Uniform frontier shift and conservative degrees

These identities hold on every one of the sixteen inherited strong/
positive-scale bases and for either program interface. Their private
registers are not factors or comparison ports, so the same four-gate
saving applies to every grouping/finalizer in the parent's finite
family. The [exact partition optimum](neary_woods_universal_computed_ports_partitions.md#3-exact-finite-optimization)
therefore shifts uniformly by four operations after all three rewrites:

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
| 265 | 3853 | 43 |
| 266 | 3437 | 43 |
| 267 | 3391 | 43 |
| 268 | 2273 | 44 |
| 269 | 1505 | 44 |
| 270 | 1459 | 44 |
| 271 | 1094 | 44 |
| 272 | 1048 | 44 |
| 273 | 734 | 44 |
| 274 | 706 | 44 |
| 275 | 608 | 44 |

The fixed43-witness frontier becomes
\((265,3853),(266,3437),(267,3391),(268,2380),(270,1810),(272,1344)\).
The fixed44-witness frontier is the displayed frontier from268 to275.
The fixed45-witness frontier runs from271/2262 to278/608; its complete
list is stored in the receipt. These are the inherited finite-family
objectives after a uniform exact transformation, not a lower bound on
all circuits or a fresh search over other algebraic rewrites.

The full polynomials are identical, so all parent degree bounds remain
valid. Literal propagation on every rewritten schedule independently
returns the same complete degree dictionary, including native factor
and scale bounds. The guarded exact main-norm cancellation is untouched.
No equality known only at zeros is used to reduce an off-zero degree.
The default251-gate certificate and five comparisons require14 further
finalizer gates, giving265=134M+131A. All numeral multiplications count.

## 6. Reproducibility and validation

Run `neary_woods_universal_shared_history265.py` to reproduce the checks
and compare the receipt. `--write` regenerates it. `build()` returns the
default265 source; an explicit operation count selects another frontier
point. With no operation count, changing flags applies them to the
default269 parent. `rewrite` accepts any compatible literal source and
performs the guarded local transformations.

The author writer checks 2,464 literal ledgers: 352 inherited optimized
base/interface/group-count schedules times all seven flag subsets.
It also checks 6,048 complete output and retained/restored-register
identities, including 3,024 signed assignments, on all 32 one-group
base/interface contexts and all 44 distinct displayed frontier schedules.
These checks cover unit factors and the actual factor product represented
by every `group_products` entry. All degree dictionaries are unchanged.
Every emitted gate reaches the complete output.

Three independent coefficient-dictionary identities check the algebra
without sampling. Eleven incompatible-caller regressions exercise
private consumers, comparisons, nested exports, altered producer rows
and a fresh-name collision. The collision regression also guards the
distinction between an intended retained output and a genuinely new
temporary. The receipt stores the complete default-enabled sources of
all44 selected schedules; other flag variants have deterministic source
digests, coordinate lists, counts and complete builder recipes.

These are all-integer algebra/source checks, not materialized full
positive Pell zeros. Author receipt generation and fresh default replay
pass. Root's independent full source/algebra/domain review and fresh
default replay pass with no findings. A separate SymPy audit proves the
identities exactly. Root's own numeral-aware executor and manual
erased-register reconstruction checked 896 complete polynomial,
retained/restored-register and group identities, including 448 signed
assignments, across all 224 base/interface/flag contexts, without using
the author's reconstruction helper. All complete degree dictionaries,
supplied domains, comparisons and counts match their parents. All four
local links resolve, and the diff whitespace check passes.
