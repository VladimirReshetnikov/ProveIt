# Absorb the duration bound into the input scale: a282-operation U9 polynomial

The [computed-port successor](neary_woods_universal_computed_ports275.md)
gives275 operations,43 witnesses and degree at most3853 by specializing
three native fields and the grouped checksum. It preserves accepted
outer instances; this282 parent remains reproducible.

The explicit U9 universal polynomial now costs **282=139M+143A**
operations, with **262=132M+130A** certificate gates, **7 comparisons**,
**46 positive existential witnesses**, four positive program parameters
and degree **at most3980**. Defining the input scale above both the
ordinary input and the extracted duration makes the separate duration
bound automatic. One comparison and one witness disappear at unchanged
certificate cost.

The [source](neary_woods_universal_duration_floor282.py) and
[receipt](neary_woods_universal_duration_floor282.json) transform the
entire reviewed [mask-gap285 family](neary_woods_universal_mask_gap285.md).
The degree-at-most608 option costs **292=139M+153A**, with257 certificate
gates,12 comparisons and47 witnesses. Keeping46 witnesses gives289
operations at degree at most1344. These are alternative explicit
universal constructions; the separate75/87 bounds remain unchanged.

The forward lift is positive on every supplied positive tuple. The
converse uses the same valid-program leading-zero padding as the
[loader288 theorem](neary_woods_universal_loader_scale288.md).
No bijection of all parent zeros or completeness for arbitrary invalid
program parameters is asserted.

## 1. Replace two additions and delete one bound

Write ell for the positive register `program_duration_bound`, q for
`input_bound`, and b for the positive supplied `input_slack`. The parent
computes, for its usual four program parameters,

    ell=program_E+program_duration_gap,
    q=x+b,
    duration_bound=ell+duration_slack,
    comparison duration_bound=B-1.                 (1)

The fifth-parameter interface instead uses `program_bound` in place of
`program_E` in the first line. Both are supported without changing the
program parameters. All existential coordinates and x are positive.
The already-paid loader computes

    r=q+z+power_gap,
    Q=kappa*r+1,
    B=c*Q,                                         (2)

where kappa=2^D-1 and c=2^(D-1) are the unchanged fixed numerals, with
D>=2. They are positive integers. The actual U9 width remains the
parent's fixed D=47946621298704238734708993009920; no fixed multiplication
is removed from the operation count.

Replace the second and third additions in(1) by

    duration_input_floor=x+ell,
    q=duration_input_floor+b.                       (3)

Delete the comparison in(1) and the supplied `duration_slack`. The new
b is still positive, but has a different meaning. The source retains
every other gate and comparison, including the actual duration equation

    J=(B-1)*duration_quotient+ell.                   (4)

The two additions in(3) replace exactly two additions. This is not an
unpaid assumption ell<B-1: that inequality follows from the new literal
positive formulas before any native equation is applied.

The rewrite checks the producer rows in(1)--(4), the fixed-numeral roles,
the sole removed comparison, all private consumers and recursive public
interfaces. In particular neither changed slack may be consumed by any
other arithmetic row or exported directly. The source is sorted after
the replacement, and all emitted gates reach the final polynomial.

## 2. Positive sound lift and complete polynomial identity

For every new supplied tuple, restore parent coordinates by

    b_old=ell+b,
    duration_slack_old=B-1-ell.                     (5)

All other supplied coordinates remain fixed. For positive inputs,

    q=x+ell+b>ell,
    r=q+z+power_gap>q,
    Q=kappa*r+1>q,
    B=c*Q>=Q.

Since these are integer inequalities, B-1-ell>0. Thus both restored
slacks are positive before any zero-set hypothesis. The old q is
x+b_old=x+ell+b, equal to the new q. The old Q,B and every remaining
source register therefore agree with their new counterparts. The old
duration bound becomes identically B-1.

For arbitrary integer assignments, including signed ones, this gives
the exact identity between the complete emitted polynomials

    F_new(v)=F_285(Phi(v)).                         (6)

Every retained residual and every grouped unit factor is identical;
the one removed residual is zero under(5). Identity(6) holds both for
the anchored grouped-unit finalizers and for the all-SOS option.
Positivity of Phi is separately asserted on the positive domain with
the actual positive fixed numerals.

Every positive zero of the new polynomial consequently lifts to a
positive parent zero with the same ordinary input and program
parameters. All parent conclusions follow, including full native
strong equations, both ratios, exact input decoding, shared duration,
history control and synchronized counter. This argument adds no new
rank or sign lemma.

## 3. Completeness on the same universal program slices

The [literal U9 input theorem](neary_woods_universal_u9_tag_chain.md)
and loader288 completeness proof permit arbitrarily long dyadic
leading-zero padding for every positive ordinary input. Fix a valid
program slice for a recursively enumerable set S and x in S. Choose a
dyadic length n large enough for all inherited requirements, and with

    n>=4, bitlength(x)<n.                           (7)

The parent's complete extension has

    ell=n, q=2^n, 0<x<2^(n-1),
    Q=2^(Dn), z=sum_i bit_i(x)*2^(Di).

The exact duration equality ell=n is proved by the retained repunit
congruence and the parent's bound; it is not an informal interpretation
of an arbitrary witness. The [dyadic-duration proof](native_binary_dyadic_duration_recoder.md),
Sections3--4, establishes this identification before the low-bit test.
The later complete parent rewrites preserve it.

Set

    b_new=q-x-n.

Since x<2^(n-1) and 2^(n-1)>n for n>=4, this is strictly positive.
Erase the old duration slack and replace the old input slack by b_new.
The new formulas(3) then restore exactly the old q, hence Q,B,J and all
other retained registers. Every retained comparison and final polynomial
vanishes. Canonical all-factor-one native extensions remain available
for every partition in the family.

The loader's existing proof also supplies r-q-z>0 under(7), so the new
coordinate condition is compatible with its positive loader gap. The
leading-zero padding changes both the encoded input and the exact
initialization counter, which remains128n. It does not replace the
counter by an arbitrary larger value on the same unpadded tape. The
inherited valid recognizer accepts the same x at each such padding.

Therefore the one fixed282-operation polynomial G has, for the same
effective valid program tuple,

    x in S iff exists y_1,...,y_46>0:
        G(x,A_S,B_S,T_S,E_S,y_1,...,y_46)=0.

The independent fifth duration-bound interface permits the same choice
of a sufficiently large n and is checked separately. For arbitrary
invalid program parameters, only the sound positive lift is claimed.

The inverse formula b_new=b_old-ell need not be positive at every typed
parent configuration. For D=8,n=8,x=251, take q=256,Q=2^64 and the
ordinary spread z. The loader repunit has

    r-z=2^16, r-q-z=65280>0,
    b_old=q-x=5, b_new=q-x-n=-3.

These are exact recoder/loader coordinates, not a constructed complete
universal-polynomial zero. They show why arbitrary parent-tuple
positivity is not the converse argument; padding is the argument used.

## 4. Literal cost and conservative degree family

Deleting one comparison from a finalizer costing C+3e-1 saves1M+2A.
The certificate retains C gates and loses one existential coordinate.
The full transformed family is:

| Polynomial operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|282|3980|46|
|283|3486|46|
|284|3440|46|
|285|2322|47|
|286|1554|47|
|287|1508|47|
|288|1142|47|
|289|1098|47|
|290|766|47|
|291|734|47|
|292|608|47|

The separate46-witness289/1344 option has257 certificate gates and11
comparisons. The first row has262 certificate gates and7 comparisons;
the last has257 and12. Witnesses do not include x or the program
parameters. This is the inherited finite operation/degree family, not a
claim of a global optimum or of simultaneous witness-count optimality.

Both ell and the new input floor are affine, so q retains degree1 when
all supplied coordinates and program parameters have degree1. Every
retained factor degree is unchanged. The erased duration residual has
degree1 and does not determine the maximum remaining residual degree.
The checker recomputes the full guarded degree propagation, including
the literal main-norm cancellation, and verifies equality with the
parent's entire degree-bound dictionary at all24 schedules. These are
conservative upper bounds; no zero-set equation is used to lower an
off-zero polynomial degree.

## 5. Reproducible checks

```sh
python3 neary_woods_universal_duration_floor282.py
```

The receipt contains24 literal schedules: eleven frontier points and
the fixed46-witness alternative on both program interfaces. It checks
768 complete polynomial identities,384 signed, and768 coordinate round
trips. The384 positive assignments all have positive restored coordinates.
It also checks552 padded recoder/loader configurations and the stated
nonpositive-inverse regression. All these numeric configurations are
component checks, not materialized complete native Pell zeros.

`build` accepts the same grouped-family choices; `polynomial_source`
returns the actual acyclic output schedule. `lift_to_parent` restores
(5), and `project_from_parent` applies the inverse formula without
claiming positivity outside the padded completeness domain. Historical
metadata stays attached to its original packet; this wrapper restores
its exact `duration_floor_parent` before any earlier coordinate lift.

Author receipt generation and a fresh default replay pass. An independent
reviewer completed the full proof/source review and a separate fresh
default replay without findings. Its literal executor and manual lift
checked192 complete output/register/residual/factor identities,96 signed,
with96 positive lifts across all24 schedules. It independently assembled
288 padded recoder/loader/mask cases, retaining K>quotient_hat and the
exact duration congruence. These remain component and algebraic checks,
not constructed complete native Pell zeros. All local links resolve.
