# Factoring the paid counter repunit gives the U21 source376

The [literal successor](korec_packed_repunit376.py) saves **two operations**
from [selector-sharing378](korec_packed_selector_sharing378.md). Its default
is **376=143M+233A**, with375 certificate operations, one comparison,
50 positive witnesses and degree at most21549. It retains one fixed positive
program parameter and ordinary positive input. The separate two-program
interface costs **375=144M+231A**, with374 certificate operations, one
comparison,50 witnesses and degree at most40706; its inherited fixed-radix
parameter conditions are unchanged.

The complete integer polynomial is identical on the same supplied
coordinates. All source comparisons, domains, public values and native
factors remain unchanged. Both complete halting directions therefore
follow from the parent with its existing program conventions. No new
positivity, bit typing, chronology or sign argument is required. The
independent U9 and75/87 bounds are unaffected.

## 1. Exact local identity and source accounting

Let `D=counter_radix_72`. The parent already computes the powers
`D2_73` through `D7_78` for the counter and control lanes. Its repunit uses
seven additions:

```
counter_repunit_85 = 1 + D
counter_repunit_86 = counter_repunit_85 + D2_73
counter_repunit_87 = counter_repunit_86 + D3_74
counter_repunit_88 = counter_repunit_87 + D4_75
counter_repunit_89 = counter_repunit_88 + D5_76
counter_repunit_90 = counter_repunit_89 + D6_77
counter_repunit_91 = counter_repunit_90 + D7_78.
```

The polynomial identity

\[
  1+D+D^2+\cdots+D^7=(1+D)(1+D^2)(1+D^4)                 \tag{1}
\]

holds over every commutative ring. Each integer from0 through7 has exactly
one binary expansion using1,2,4, so expanding the right side gives each
power exactly once. In particular, the identity requires neither a
positive nor a dyadic radix.

Keep `counter_repunit_85`, remove the five private prefixes86 through90,
and emit

```
counter_repunit_D2_one = D2_73 + 1
counter_repunit_D4_one = D4_75 + 1
counter_repunit_first_product = counter_repunit_85 * counter_repunit_D2_one
counter_repunit_91 = counter_repunit_first_product * counter_repunit_D4_one.
```

Including the retained first addition, this costs3A+2M instead of7A:
**two fewer total operations, two more multiplications, and four fewer
additions**. The paid powers are retained because their counter and control
consumers remain. Every new gate is live in the complete polynomial.

The erased registers restore as

\[
 \texttt{counter\_repunit}_{84+i}=\sum_{j=0}^{i}D^j,
 \qquad 2\le i\le6.                                      \tag{2}
\]

The final repunit has its old value by(1). Every other retained register
then has its old value by induction through the unchanged downstream
source. Thus all residuals, factors, public ports, and both complete
finalizers are identical over arbitrary integer assignments. No supplied
coordinate is erased or introduced. The identity map on supplied
coordinates gives equality of the complete positive-zero sets, not only
equality of an outer projection.

## 2. Guards, interfaces and degree bounds

`rewrite(old)` accepts only a complete canonical selector378 packet in
one of its three forms (`fields`, `range_unit`, `units`) and either of its
two program interfaces. Equality to the canonical packet includes all
supplied domains and active metadata.

The local `rewrite_rows(old)` helper guards the literal power definitions
and all seven repunit additions. Each of the five erased prefixes must
have exactly its next chain row as its sole consumer. Recursive export
guards reject a deleted prefix in supplied parameters, auxiliaries,
comparisons, outer pairs, factors, group products, public registers,
interfaces or native restoration metadata. Fresh temporary names are
required. The helper topologically sorts and checks the rewritten source
and verifies its exact opcode change.

This helper certifies an integer graph identity, not the completeness of
an arbitrary host compiler. A host using it outside the six emitted
canonical packets must independently guard its complete parent and
rebuild its own metadata. No frozen partition source is changed here.

If the propagated degree of `D` is \(d\), the old repunit has bound \(7d\).
The three factors in(1) have bounds \(d,2d,4d\); their product again has
bound \(7d\). Every retained downstream degree is unchanged. The actual
checker requires equality of the full inherited degree dictionaries for
both finalizers in all six contexts, including their guarded main-norm
cancellation. These are propagated upper bounds, not claims that the
complete polynomial has exactly the displayed degree.

## 3. Literal ledgers and reproducible verification

Every row retains50 positive witnesses. Product-finalizer ledgers are:

| Program parameters | Form | Certificate | Comparisons | Polynomial | M | A | Degree bound |
|---:|---|---:|---:|---:|---:|---:|---:|
|one|fields|367|4|378|144|234|21540|
|one|range unit|369|3|377|144|233|21549|
|one|all units|375|1|376|143|233|21549|
|two|fields|366|4|377|145|232|40690|
|two|range unit|368|3|376|145|231|40706|
|two|all units|374|1|375|144|231|40706|

For `fields` and `range_unit`, SOS and product finalizers have the same
operation count. For `units`, squaring the final residual adds one
multiplication, giving377 or376. The SOS degree bounds in table order
are43016,43034,43098,81256,81288,81412.

The [receipt](korec_packed_repunit376.json) stores all six complete product
sources, both finalizer ledgers and their hashes. Run
`python3 korec_packed_repunit376.py`; `--write` regenerates it. Author receipt
generation and a separate fresh default replay pass. The source audit
checks384 complete retained-register
and manually reconstructed prefix maps, including192 signed assignments.
Both finalizers give768 complete output identities, including384 signed
cases. An independent coefficient expansion of(1) gives eight coefficients
all equal to1. Nine malformed callers exercise additional prefix consumers,
nested exports, altered power or repunit rows, colliding temporary names,
missing comparisons and repeat application. These are source identities,
not instantiated complete native Pell zeros.

The bounded discovery work also checked two-gate sum/subtraction trees
among181 existing homogeneous selector forms, finding377 eligible trees
and no further saving. A separate two-gate weighted check used23 paid
radix-polynomial or small-integer coefficients and found89 eligible trees,
again without a saving. Those finite scouts motivate stopping this local
search; they do not establish optimality among other circuits, larger
cones, control codes or coordinate changes. The repunit identity and its
literal ledger are independent of the scouts.

Independent full proof/source review and a further fresh default replay
pass without findings. A separate executor checks144 complete retained
register and manual prefix-restoration maps, plus288 complete polynomial
identities, half signed, over all six forms/interfaces and both finalizers.
It independently verifies the twelve opcode shifts and complete degree
dictionaries. All three local links and whitespace checks pass.
