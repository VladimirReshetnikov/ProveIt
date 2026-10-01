# Define the loader scale: a288-operation universal U9 polynomial

The loader's repunit comparison can be absorbed into the definition of
the recoder scale. The resulting universal U9 polynomial costs
**288=141M+147A** operations, with **262=132M+130A** certificate gates,
**9 comparisons**, **48 positive existential witnesses**, and degree
**at most3980**. It has the same ordinary positive input and four positive
program parameters as the [291-operation construction](neary_woods_universal_positive_scale291.md).
The separate75/87 frontier is unchanged.

The [source](neary_woods_universal_loader_scale288.py) and
[receipt](neary_woods_universal_loader_scale288.json) also transform the
[grouped positive-scale family](neary_woods_universal_positive_scale_partitions.md).
Its degree-at-most608 option now costs **298=141M+157A**, with
257 certificate gates,14 comparisons and49 witnesses. A separate
48-witness option costs295 with degree at most1344.

Soundness is given by a positive lift on every supplied positive tuple.
Completeness uses sufficiently long leading-zero padding for the inherited
**valid U9 program slices**. This is not a bijection of all parent zeros,
and equality of the represented relation for arbitrary invalid program
parameters is not asserted. The fixed polynomial remains universal in
the same ordinary-input sense proved by its U9 parent.

## 1. Three existing gates and one removed comparison

Let D be the unchanged fixed data width, let Lambda=2^D, and write
kappa=Lambda-1. The literal fixed-numeral role `repunit_divisor` is kappa.
It is positive; indeed D>=3 in the inherited construction. This Lambda
is the data-block radix, not the variable recoder base B.

Write q for `input_bound`, r for `load__r`, and g for the old supplied
`power_gap`. The parent source contains

    q=x+input_slack,
    floor=q+z,
    Q=floor+g,
    modulus=Q-1,
    repunit_product=kappa*r,
    comparison repunit_product=modulus.             (1)

All supplied coordinates are positive. Q enters the recoder and loader;
r enters the two already-paid loader coefficient multiplications. The
repunit-product register has no other source consumer or comparison.

Keep a new positive b in the old spelling `power_gap`, omit supplied r,
and replace the last three arithmetic gates in(1) by

    r=floor+b,
    modulus=kappa*r,
    Q=modulus+1.                                    (2)

Delete the repunit comparison. There are still three gates,1M+2A.
The unchanged first two additions give the same total1M+4A for the
five-gate closure. No multiplication by kappa is free, and there is
no division or exponentiation in the emitted replacement.

The rewrite checks these literal producer rows, the private repunit
product and gap consumers, the sole deleted comparison, and transitive
independence of floor from both changed coordinates. It then sorts the
source after r changes from an auxiliary to a register. All other
arithmetic gates, every unit factor and all remaining comparisons retain
their literal formulas. The source has one fewer positive witness and
one fewer comparison at exactly the same certificate cost.

## 2. Unconditional positive forward lift

For any new supplied positive tuple define the old coordinates by

    r_old=q+z+b,
    g_old=Q-q-z=(kappa-1)(q+z)+kappa*b+1.             (3)

Since kappa>=1, both restored coordinates are positive before any native
equation. The old Q is the new Q, the old r is the new computed r, and
the old repunit comparison is identically true. Every other old source
register therefore equals its new counterpart. Only the unused old
repunit-product register is absent from the new source.

In particular, a new positive zero lifts to a parent positive zero with
unchanged x and every program parameter. All parent soundness conclusions
apply. This includes the two coupled native cores, the accepted tag
history, input decoding and exact counter synchronization; no new sign
or rank hypothesis is needed.

For arbitrary integer assignments, including signed assignments, the
same algebraic map gives an exact whole-output identity

    F_new(v)=F_parent(Phi(v)).                        (4)

The erased residual is identically zero and every retained residual and
group product agrees. This holds for both the SOS and unsquared grouped
finalizers. Positivity of the map is separately asserted only on the
stated positive domain with the actual positive fixed kappa.

## 3. Completeness by valid-program padding

The [literal U9 input theorem](neary_woods_universal_u9_tag_chain.md),
Section2, proves that the fixed recognizer ignores arbitrary leading-zero
padding of the binary spelling of x. Every positive x has arbitrarily
large dyadic input lengths n satisfying n>E_S and x<2^n, and the recognizer
accepts the same x under all of them. The
[population-tag proof](neary_woods_universal_population_tag.md), Sections1
and3, transfers those padded inputs to the full arithmetic construction.
The exact least initialization counter remains128n, since

    64n<64n+b_S<128n.

Increasing n changes the padded input and its exact synchronized counter
together. It does not substitute an arbitrary oversized counter for the
same unpadded tape.

Fix a valid program tuple for a recursively enumerable set S and x in S.
Choose a dyadic n sufficiently large for every parent requirement and also

    n>=3, n>=bitlength(x)+1.                         (5)

The parent completeness proof supplies a zero with

    q=2^n, Q=Lambda^n,
    z=sum_i bit_i(x)*Lambda^i,
    r_old=1+Lambda+...+Lambda^(n-1).                  (6)

The highest digit of z is absent by(5), so

    r_old-z>=Lambda^(n-1)>2^n=q,                     (7)

where the strict inequality follows from D>=2 and n>=3. Thus

    b=r_old-q-z>0.                                  (8)

Erase the old r coordinate and replace g by b. Equations(2) restore the
same r,Q, all loader outputs and all native inputs as at the chosen parent
zero. Every new comparison and final polynomial vanishes. Canonical
all-factor-one extensions in the grouped parent remain available, so the
argument applies to every displayed partition and both duration interfaces.

Consequently the one fixed288-operation polynomial G satisfies, on the
same effectively chosen valid program parameters,

    x in S iff exists y_1,...,y_48>0:
    G(x,A_S,B_S,T_S,E_S,y_1,...,y_48)=0.

The fixed U9 table, ordinary input map and all fixed-numeral recipes are
unchanged. In particular D remains47946621298704238734708993009920.
The independent fifth duration-bound interface admits the same choice
of sufficiently large n and is checked separately in the source.

The inverse formula(8) is not positive on every typed parent tuple.
For example, with x=2^n-1 the spread equals the full repunit, so
r_old-q-z=-q. A finite recoder-only regression D=3,n=2,x=3 has
q=4,Q=64,z=r_old=9: its old gap is51 and its proposed new gap is-4.
That fixture is not a materialized universal-polynomial zero. It makes
clear why completeness is based on padding rather than an unrestricted
coordinate bijection. For arbitrary invalid program coefficients, this
packet claims only the positive sound lift to the parent, not the padding
invariance established for valid U9 program slices.

## 4. Costs and unchanged degree bounds

Each construction removes one comparison from a finalizer costing
C+3e-1, where C is the certificate cost and e its comparison count.
It therefore saves1M+2A and one witness. The transformed cost/degree-bound
frontier from the parent's finite family is

| Polynomial | M | A | Degree bound | Witnesses |
|---:|---:|---:|---:|---:|
|288|141|147|3980|48|
|289|140|149|3486|48|
|290|139|151|3440|48|
|291|142|149|2322|49|
|292|141|151|1554|49|
|293|140|153|1508|49|
|294|141|153|1142|49|
|295|140|155|1098|49|
|296|141|155|766|49|
|297|140|157|734|49|
|298|141|157|608|49|

Witness counts vary, so this is not a three-objective witness optimum.
Restricting to48 witnesses also gives295/1344, with257 certificate gates
and13 comparisons; its operation count must not be confused with the
49-witness295/1098 option.

The scale Q, modulus and newly computed r all have propagated degree1,
as their old values did. Every retained factor degree is unchanged. The
erased loader residual has bound1 and does not determine the maximum
ordinary-residual bound of any of the sixteen bases. The checker reruns
the actual degree propagation, including the frozen guarded main-norm
cancellation, and compares its result with the parent schedule. For SOS
it includes every group residual; for an unsquared anchor it adds the
anchor bound to twice the maximum of all squared residual bounds.

Thus the original partition objective is unchanged for every base and
grouping, while cost and witness count uniformly decrease by3 and1.
The parent's finite-family optimum608 for that conservative objective
still applies. No exact polynomial degree or unrestricted arithmetic
optimum is claimed.

## 5. Reproducible evidence

```sh
python3 neary_woods_universal_loader_scale288.py
```

All eleven frontier schedules are emitted on both program interfaces,
as is the48-witness295/1344 alternative. These24 sources receive768
whole-output identities,384 signed, with384 positive forward lifts and
768 coordinate round trips. Every emitted gate reaches the final output;
all literal multiplication/addition and comparison/witness counts are
checked. The numerical identities use finite substitutions for the fixed
numerals; the actual enormous fixed recipes remain symbolic and unchanged.

Another552 exact padded recoder/loader fixtures check(6)--(8), alongside
the explicit nonpositive-inverse regression. None is claimed to supply
the astronomical positive native Pell witnesses. Those extensions follow
from the inherited complete converses and the valid-program padding proof.

Author writer and fresh default replay passed. An independent reviewer
completed the full proof/source/fresh-default review with no findings,
including the actual valid-program padding and synchronized-counter
sections of the U9 parents. Its separate literal executor and manual
coordinate formulas checked192 complete source/output identities,
96 signed and96 positive, across all24 schedules; another2,177 exact
padded-scale inequalities passed. All six local links resolve.

A second independent full proof/source/fresh-default review also passed
without findings. Its separate literal executor checked another192
whole source/output identities across all24 schedules,96 signed and96
positive, including equality of every shared certificate register and
positivity of every positive lift. Neither review interprets the padded
converse as an all-tuple inverse or as a theorem for invalid program
parameters.
