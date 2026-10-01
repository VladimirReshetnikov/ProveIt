# A positive mask gap gives a285-operation universal U9 polynomial

The [loader-scale288 source](neary_woods_universal_loader_scale288.md)
has a **285=140M+145A** successor with **47 positive witnesses**, eight
comparisons,262 certificate operations and degree **at most3980**.
Its four positive program parameters and ordinary positive input are
unchanged. The smaller-degree option becomes **295=140M+155A**, with
48 witnesses,13 comparisons,257 certificate operations and degree
**at most608**. The separate75/87 bounds are unchanged.

The [source](neary_woods_universal_mask_gap285.py) and
[receipt](neary_woods_universal_mask_gap285.json) define the mask witness
above the already-supplied quotient witness. The retained mask-scale
equation then implies the old lower-output bound. This is a bijection
between the complete positive zero sets of the new and selected288
parent polynomials. It does not strengthen that parent's inherited
valid-program completeness theorem into a theorem about arbitrary
invalid program parameters.

## 1. Exact retained source and one positive definition

Use the parent's recoder notation q=input_bound, h=quotient_hat,
J=duration_J and S=scale. Write Ahat=projected_Ahat. Its literal rows give

    q=x+input_slack,
    r_load=q+z+power_gap,
    Q=(2^D-1)*r_load+1,
    B=2^(D-1)*Q,
    P=(B-1)*J+1,
    S=q*P,
    mask_scale=(2B-1)*K+1,
    Ahat=(Q-1)*(h-1)+z+1.                          (1)

Here D is the unchanged fixed U9 data width, in particular D>=2.
The displayed formulas are interpretations of the existing literal
source; no uncharged evaluation of those fixed coefficients is added.
The two old comparisons are

    mask_scale=S,
    Ahat+fusion_output_slack=S.                    (2)

Originally K and fusion_output_slack were independent positive
witnesses. Keep the latter coordinate under its literal name but give
it a new meaning g>0. Define instead

    K=h+g.                                        (3)

Delete the old one-addition bound register and its comparison, and
remove K from the supplied witness list. The addition in(3) replaces
the deleted addition, so certificate cost is unchanged. The first
comparison in(2) remains.

The source guards every row in(1), both comparisons in(2), the private
consumer of the old slack, and the absence of exports of the deleted
bound/slack. It keeps all native factors, program parameters and other
comparisons. K is now a computed positive register in every existing
consumer, and the complete source is topologically sorted again.

## 2. Soundness and the exact positive lift at zeros

Before any equation, q>=2 and r_load=q+z+power_gap>z+1. Therefore

    Q-1>z+1,
    1<=Ahat<=(Q-1)*h,
    B>=Q,
    K=h+g>h.                                      (4)

The first two statements use h>=1. In fact Ahat>=z+1>=2. Thus, on
every positive new supplied tuple,

    mask_scale-Ahat
      >= (2B-1)*K+1-(Q-1)*h > 0.                  (5)

At a new zero the retained comparison gives mask_scale=S. Restore
the old coordinates by

    K_old=h+g,
    fusion_output_slack_old=S-Ahat.                (6)

Both are then strictly positive. Every other supplied coordinate is
unchanged, as is every retained certificate register and native factor.
The removed comparison is identically true under(6). Consequently
the new zero lifts to a complete positive zero of the selected parent.
This establishes soundness before invoking any recoder interpretation
to prove the converse.

It is essential that positivity of the second coordinate in(6) uses
the retained equation. An arbitrary positive input can have S<Ahat.
The receipt preserves an explicit such regression. The identity map
is not advertised as an unconditional map of positive orthants.

## 3. Every old positive zero has a positive mask gap

The full parent theorem restores the complete recoder relation on
every positive zero. From the [joint-AND parent](neary_woods_universal_joint_and.md)
and the [dyadic-duration recoder](native_binary_dyadic_duration_units.md),
there is a dyadic n>=2 with

    q=2^n>=4, Q=q^D, B=2^(D-1)*Q,
    P=B^n, J=(B^n-1)/(B-1)>=B+1>1,
    0<x<q,
    Ahat-1=(xJ) AND K <= xJ.                       (7)

These are consequences of complete positive zeros, including the
parent's restored native cores. They are not inferred from a bounded
outer fixture or assumed before restoring that parent.

Since z>=0, (1) and(7) imply

    h <= xJ/(Q-1)+1
      <= (q-1)J/(q^2-1)+1
       = J/(q+1)+1 <= J.                           (8)

The last inequality follows from q>=4,J>=2. The retained scale
equation separately gives

    K = (q*((B-1)J+1)-1)/(2B-1)
      > q*(B-1)*J/(2B-1)
      >= q*J/3 > J,                               (9)

using q>1,B>=2 and q>=4. Hence K>h. Thus the inverse map is

    g=K_old-h>0,
    erase the supplied coordinate K_old.           (10)

Under this map the newly computed K equals K_old. All retained
comparisons and factors agree, so the resulting tuple is a new zero.
The old bound equation uniquely gives its removed slack as S-Ahat.
Equations(6) and(10) are consequently inverse on the complete positive
zero sets, with every other supplied native coordinate fixed.

In particular no fresh Pell auxiliaries or new input padding are needed
for this additional reduction. The loader parent still obtains its own
completeness from sufficiently long valid-program padding, with the
same exact synchronized128n counter. This proof preserves that theorem
and all four program parameters without adding a stronger input claim.

## 4. Whole-polynomial identities and the positive off-zero extension

Let G denote the new polynomial and F its selected parent. Map(6) is
algebraic over all integer assignments, although its restored slack may
be negative off zeros. It gives the exact identity

    G(v)=F(lift_identity(v)).                      (11)

Indeed the removed residual is zero and all retained residuals and
unit products agree. The checker executes both complete sources;
it does not test only the deleted bound in isolation.

There is also an unconditional positive extension, replacing the
second line of(6) by

    fusion_output_slack_old=mask_scale-Ahat>0.      (12)

This uses(5), but off zeros the old bound residual now equals the
retained scale residual R=mask_scale-S. For an anchored product
finalizer with unchanged unit product W,

    F(lift_positive(v))=G(v)+W*R^2.                (13)

For a pure sum-of-squares finalizer the correction is simply R^2.
Both identities are checked on arbitrary signed assignments. The two
lifts coincide at every new zero. Recording(13) avoids confusing a
positive off-zero extension with equality of the full polynomials.

## 5. Costs, degree bounds and preserved alternatives

One paid addition replaces one paid addition, one comparison disappears,
and one supplied positive witness becomes a computed register. Each
selected parent's complete finalizer therefore loses exactly3 operations:
one multiplication and two additions. All fixed-numeral recipes and
all native source formulas remain unchanged.

The transformed cost/degree-bound frontier is

|Polynomial cost|Degree upper bound|Positive witnesses|
|---:|---:|---:|
|285|3980|47|
|286|3486|47|
|287|3440|47|
|288|2322|48|
|289|1554|48|
|290|1508|48|
|291|1142|48|
|292|1098|48|
|293|766|48|
|294|734|48|
|295|608|48|

The separate fixed47-witness option gives292 operations,257 certificate
gates,12 comparisons and degree at most1344. It differs from the48-witness
292/1098 point in the table. These are inherited finite-family choices,
not an unrestricted or three-objective optimum.

The new K is affine, so its degree bound remains1. No retained factor
degree changes. The erased bound residual has the same scale term as
the retained mask-scale residual and cannot increase the remaining
maximum. The actual checker reruns the frozen guarded main-norm
cancellation and complete residual/factor propagation on every source;
each reported degree-bound dictionary equals its parent's. No zero-set
equation is used to reduce a polynomial degree, and no exact degree is
claimed.

Both the four-program-parameter interface and the separate duration-bound
interface are supported by `build`. `lift_to_parent` defaults to(6);
`positive_extension=True` chooses(12). `project_from_parent` implements
(10), whose positivity claim applies to parent zeros. All inherited
metadata remains historical; this wrapper first restores its exact
`mask_gap_parent` before any earlier coordinate map is applied.

## 6. Reproducible evidence

```sh
python3 neary_woods_universal_mask_gap285.py
```

The receipt emits24 sources: eleven frontier points and the fixed47
alternative, each on both program interfaces. It checks768 complete
identity-lift outputs,384 signed, plus768 complete corrected-extension
outputs and1,536 coordinate round trips. The384 positive-extension
assignments have strictly positive restored coordinates. Every emitted
gate reaches its final output.

Another600 exact typed recoder fixtures check(7)--(9), of which561
also satisfy the preceding positive loader-gap condition. These are
component fixtures, not numerical complete universal polynomial zeros.
The full converse is the inherited theorem and the all-index inequalities
above. An explicit off-zero example has S-Ahat<0 but mask_scale-Ahat>0,
so it also checks the limitation of the identity lift.

Author receipt generation and a fresh default replay pass. An independent
reviewer completed the full proof/source review and a fresh default replay
without findings. Its separate literal JSON-source executor and manual
coordinate formulas checked192 complete identity lifts and192 corrected
positive-extension outputs across all24 schedules, including96 signed
assignments. Another960 exact typed recoder inequalities passed. All five
local links resolve. No full positive Pell zero was numerically claimed
by these supplementary checks.
