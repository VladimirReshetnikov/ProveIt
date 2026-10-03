# An188-operation recoder by projecting the redundant geometry bound

For every fixed integer k>=3, the complete positive dyadic-duration
relation of the [population-width recoder](native_binary_population_width_recoder.md)
has a polynomial with **188=93M+95A operations**, **39 positive existential
coordinates**, and degree **at most303**. The certificate has
**147=79M+68A operations and14 comparisons**. The ordinary positive
parameters remain x,z. No universal tag composition is claimed here.

The change deletes one private addition, comparison and positive slack.
The existing duration equation already forces that slack to be positive
when the retained comparisons hold. The
[source](native_binary_population_width_bound188.py) and
[receipt](native_binary_population_width_bound188.json) preserve the raw,
native-unit and normalized-strong alternatives.

## 1. Exact source change and the untyped bound

Use the parent notation

\[
 Q=q+g,\quad B=2^{k-1}Q,\quad R=(2^k-1)J,\qquad g>0.
\]

The supplied duration, quotient and duration slack are denoted by ell,v,h.
The retained comparisons include

\[
 x+\mathrm{input\_slack}=q,\qquad
 (B-1)v+\ell=J,\qquad \ell+h=B-1.                 \tag{1}
\]

Delete only the source row and comparison

    geo__geometry_index_bound = B + geo__index_beta
    geo__geometry_index_bound = geometry_index

and delete the positive coordinate `geo__index_beta`. Here
`geometry_index` is R. The source asserts that the deleted coordinate
has exactly this one source consumer and no comparison consumer; the
deleted register has no source consumer and only the displayed
comparison. All other operations and comparisons retain their order.

At any positive zero of the retained raw comparisons, (1) gives q>=2,
Q>=3, and B>=12. Before either native kernel is invoked, positivity of
v and ell gives

\[
 J=(B-1)v+\ell\ge B,
 \qquad R=(2^k-1)J\ge7B>B>Q,\qquad R\ge84.         \tag{2}
\]

Thus the omitted slack has the unique restoration

\[
 \mathrm{geo\_index\_beta}=R-B>0.                 \tag{3}
\]

In particular the raw geometry at scale Q and index R still has all
three hypotheses used in the parent proof: R>B, R>=9 and R>Q. The
argument uses neither the population conclusion nor any AND decoding.
It does not assume that the old stronger quadratic scale bound holds.

For a complete compressed raw source, ell may already be the computed
positive register `program_duration_bound`. The same reasoning applies:
only ell>=1, v>=1 and the retained duration equation are needed.

## 2. Exact positive zero projection and the full converse

Every old full positive raw zero projects to a new one by forgetting
the deleted coordinate. Conversely, (3) extends every new full positive
raw zero to an old one with all retained coordinates unchanged. The
deleted equation makes this extension unique. Hence the two positive
zero sets are in bijection over all their retained coordinates.

The parent's full theorem therefore applies without a changed input or
output contract. Every positive zero has a common integer n such that

\[
\begin{gathered}
 n\ge2,\qquad n\text{ is a power of two},\qquad 0<x<2^n,\\
 z=\sum_{j<n}\operatorname{bit}_j(x)2^{kj},\qquad
 q=2^n,\quad Q=2^{kn}=q^k,\quad B=2^{kn+k-1},\\
 P=B^n,\quad J=\sum_{j<n}B^j,\quad
 K=\sum_{j<n}(2B)^j,\quad \ell=n.                 \tag{4}
\end{gathered}
\]

This imports the already proved sequence: raw geometry yields
Q=2^popcount(R); the prescribed AND types its positive scale; the first
repunit and disjoint k-bit blocks give popcount(R)=kn; the second
repunit and q<Q force the same duration n; and the joined low-bit AND
forces n to be dyadic. The retained outer extraction then fixes the
unique spread output. The bound needed at the beginning of that
sequence is now supplied by (2).

For every dyadic n>=2 and positive x<2^n, the parent converse supplies
the outer values in (4), the shifted quotient and positive range gaps,
and full positive extensions of both native kernels. Its geometry
extension uses the actual scale Q and repeated-mask index R, not the
old geometry at scale q and index J. Forget its positive coordinate
(3); this produces every required new witness. Thus no existential
native coordinate has been left unpaid or merely presumed to exist.

The projection is not a positive map on arbitrary supplied tuples.
For example, in the new raw source at k=3, setting every supplied
coordinate and parameter to1 gives Q=2, B=8 and R=7. The restored slack
is then minus one. That tuple does not satisfy (1).

There is nevertheless a useful exact off-zero identity over integers.
Substitute (3) into the old source, with no sign requirement. Its deleted
row becomes R and its deleted residual is identically zero. Every other
certificate register, comparison residual and final polynomial has
the same value as in the new source. This identity explains the signed
source checks; positivity follows separately, only at zeros, from (2).

## 3. Units and strong normalization remain valid

The deletion is made after the population-width rewrite and before
the [native-unit rewrite](native_binary_dyadic_duration_units.md).
It changes neither a norm nor a unit factor. The native-unit alternative
still has seven factors: six norm factors that exclude minus one on
all integer tuples, and the single unrestricted AND checksum.

For any integer unit product U and retained integer residuals rho_i,

\[
 U\left(1+\sum_i\rho_i^2\right)-1=0              \tag{5}
\]

implies U=1 and every rho_i=0. Indeed the second factor is a positive
integer, so an integer product equal to1 has both factors equal to1.
The six sign-safe factors then force the remaining checksum to1.
The parent identities restore the native comparisons and the13
projected positive coordinates. The duration comparison is among
the retained outer comparisons. Once it is restored, (2) supplies
the deleted geometry slack, before the raw kernel theorem is used.

The parent coordinate-positivity checks are unchanged: restored
q=x+input_slack is at least2; Q adds the positive power gap; restored
P=(B-1)J+1 is positive; and the fused prescribed-AND fields and its
packed native index retain their positive formulas. Removing the
private index slack introduces no new dependence into these lifts.

The normalized option also adjoins both proved strong units
`f^2-Delta*(i*c^2)^2`. Each excludes minus one over integers. Soundness
restores the old strong equation using `i_old=Delta*i`; completeness
uses the full canonical reconstruction of f,i,j,o,y in each native
core at its actual index. The existing source dependency checks still
pass, since none of these ten reconstructed coordinates occurs in
the duration, repeated mask, repunits or deleted bound. As in the
parent theorem, this normalization preserves the complete positive
input/output relation; it is not a bijection between all old and new
strong-coordinate tuples.

For each of the three separately fixed forms, however, deleting just
the bound gives the positive zero-set bijection of Section2 to the
corresponding192-parent form. The off-zero integer source identity
also holds for each form, including its final unit polynomial: the
unit product is unchanged and one outer residual becomes identically
zero after (3).

## 4. Paid ledgers and the public rewrite

Every operation below is a binary multiplication, addition or
subtraction. Fixed numerals have degree zero; using one as an operand
still incurs the displayed gate. No fixed numeral role is added.

|Form|Certificate M+A|Certificate total|Comparisons|Positive witnesses|Polynomial M+A|Polynomial total|Degree bound|
|---|---:|---:|---:|---:|---:|---:|---:|
|Raw SOS|69M+68A|137|35|52|104M+137A|241|52|
|Native units|75M+68A|143|16|39|91M+99A|190|195|
|Normalized strong units|79M+68A|147|14|39|93M+95A|188|303|

Relative to the corresponding population-width parent, each form
removes one certificate addition and one comparison. Finalization
therefore saves one multiplication and three additions in total:
four polynomial operations and one positive witness. Relative to
the older width-dependent normalized count `190+mu(k)`, this188
count saves `mu(k)+2` operations with the same39 witnesses. The
contract remains k>=3; no claim here changes the width2 recoder.

The degree bounds are obtained from the actual entire polynomial DAG,
adding degrees at multiplication and taking the maximum at addition
or subtraction. They are conservative and independent of k, and no
exact-degree claim is made. The deleted residual was not dominant in
this propagation, so the parent bounds52,195,303 remain valid.

The public API is `remove_bound(old)`. Its input is a literal raw
packet already transformed by `native_binary_population_width_recoder.rewrite`.
Besides the private-consumer checks, it verifies the two-gate width
metadata, mask role, duration-multiple row and both retained duration
comparisons. A supplied duration is positive by its domain; a computed
duration must have an explicitly positive addition/multiplication
expression over positive inputs. The helper supports formal fixed
numerals with their original exact role definitions, so it can act on
the [complete compressed raw compiler](binary_tag_parameterized_compressed_compiler.md)
without expanding enormous constants.

When present, `boundary_comparisons` is decremented precisely when the
deleted comparison lies in that prefix. This preserves the boundary
versus history split. The helper neither runs the later full-compiler
unit rewrite nor changes its history metadata. The receipt checks
that both existing full-compiler unit and normalization guards accept
the resulting source. A full tag composition and its degree bound
require their own packet; this note claims only the recoder and this
literal raw rewrite interface.

## 5. Verification scope

The author checks576 complete old/new certificate and polynomial
identities over widths3,4,7,16,64,257 and all three forms;288 use signed
supplied tuples. Of these,192 raw cases also compare every retained
residual with the independently stated raw geometry/AND formulas and
its SOS, and384 unit cases run the complete inherited norm-correction
and positive-coordinate audits. Negative off-zero slack restorations
are counted rather than excluded.

There are also256 direct untyped positive-duration implications,
119 genuine outer bit/duration fixtures (42 dyadic and77 non-dyadic),
and an explicit positive off-zero example with negative
restored slack. The non-dyadic cases retain the parent's rejecting
low-bit test. Eighteen complete ledgers record all widths/forms.

Three complete compressed raw API fixtures preserve all11 fixed
numeral roles, use the computed program-dependent duration, and pass
both subsequent full unit/normalization source guards. An additional48
complete compressed raw output identities include24 signed cases.
Seven malformed private-bound contracts are explicitly rejected.

These are source identities, bound implications and genuine outer
arithmetic fixtures. They are not claims to have numerically built
the enormous full Pell witnesses. Those witnesses are supplied by
the full positive converse and normalization theorems above.

Author writer and fresh default replay passed. Native-controller's full
proof/source/fresh-default review passed without findings. Its separate
audit added192 complete source, residual and final-output projection
identities at widths6,12,23,80 across all three forms, including96 signed
assignments and113 negative off-zero slack restorations. All local note
links resolve. The reduce-complete75 agent's independent full
proof/source/fresh-default review also passed without findings. Its own
literal executor checked216 further whole-source/output identities at
widths5,11,24 across all forms, including108 signed assignments and134
negative off-zero slack restorations.
Root's final proof/source review and fresh-default replay also passed.

```sh
python3 native_binary_population_width_bound188.py
```
