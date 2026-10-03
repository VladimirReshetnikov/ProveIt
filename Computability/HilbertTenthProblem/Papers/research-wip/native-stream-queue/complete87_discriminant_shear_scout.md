# Discriminant shears do not lower87 in a specified finite circuit family

The complete normalized asymmetric87 source was tested against a new family of exact main/input norm rewrites. The baseline remains **87=48M+39A**. The least expensive changed schedule is **88=48M+40A**, including a schedule that rewrites both norms together. No86-operation candidate results from this finite family.

This is distinct from the earlier joint-norm scout: that scout replaced the product of the main and input norms by one norm using composition. Here every one of the eight individual factor values is preserved. The proposal cancels the discriminant term inside each norm and shares its resulting affine coefficients between the two norms. No input, strong condition, ratio bound, coordinate, compiler numeral or finalizer is removed.

## Exact algebra

Use the actual normalized87 registers

```
a=R12, H=a4m5=4a+3, Delta=A=a²+H,
c=R10a, kappa=index_rhs,
l=X+(rho+sigma)H, m=W+rho H,
D=ac+l, mu=a*kappa+m.
```

The main and input factors are `D²-Delta*c²` and `mu²-Delta*kappa²`. For either pair `(z,b)=(c,l)` or `(kappa,m)`, put

```
u=a+lambda,
beta=b-lambda*z,
H_lambda=4a+3-2lambda*a-lambda².
```

Then the two exact Horner forms are

```
(az+b)²-Delta*z²
  = beta*(beta+2u*z)-H_lambda*z²
  = beta²+z*(2u*beta-H_lambda*z).
```

The three coefficient constructions considered are

```
H_lambda=(4-2lambda)*a+(3-lambda²),
H_lambda=(4-2lambda)*u+(lambda-1)*(lambda-3),
H_lambda=H-lambda*(2a+lambda).
```

For `lambda=0`, the existing H register is reused. For `lambda=2`, the coefficient is the fixed constant−1. Two further collapsed forms exploit `H_1=2u` and `H_3=-2u`:

```
lambda=1: beta²+2u*z*(beta-z),
lambda=3: beta²+2u*z*(beta+z).
```

All identities are polynomial identities over the integers. Computed `beta`, `u`, and the coefficient may be signed. They are intermediate registers, so no positive-coordinate hypothesis is being changed or silently imposed.

## The complete finite family

Each norm has57 mode choices:

- Its exact parent evaluation.
- Each shift `lambda` in `{−4,−3,−2,−1,0,1,2,3,4}`, each of the two Horner forms, and each of the three coefficient constructions:54 choices.
- The two collapsed forms at1 and3.

The checker enumerates all57²=3,249 pairs. Some choices emit the same source because the0/2 coefficient cases override all three coefficient construction options; these deliberate duplicate mode choices are counted as choices, not asserted to be distinct polynomials or circuits.

Every choice rewrites the literal complete parent source. The pass visits only ancestors of the complete output, applies exact commutative common-subexpression reuse, folds operations on integer literals, and removes copies and multiplication by0 or1. Multiplication by−1 is one charged subtraction. The same pass leaves the baseline at87 operations. Every addition/subtraction/multiplication still emitted, including multiplication by a fixed coefficient, counts one. Every full candidate is checked for topological closure, live gates and exactly the original free-coordinate set:19 positive witnesses, the ordinary input x, and six fixed numeral ports.

There is no search over arbitrary algebraic circuits, arbitrary integer shifts, arbitrary factor replacements or witness changes. The finite enumeration is exhaustive only for these declared templates and shifts.

## Exact result and the shared88 schedule

The least complete costs when changing exactly one norm, or changing both with the same shift, are:

| Shift | Main only | Input only | Both |
|---:|---:|---:|---:|
|−4|93|93|95|
|−3|93|93|95|
|−2|93|93|95|
|−1|92|92|93|
|0|88|88|88|
|1|90|89|90|
|2|90|90|91|
|3|91|90|92|
|4|93|93|95|

The enumeration also allows different shifts and different templates for the two norms. None has cost below88 unless both norms retain the parent evaluation, whose cost is87. Among all3,249 choices, exactly one mode pair costs87;27 cost88. The receipt records every choice, its exact M/A counts, and the complete cost histogram.

The best joint rewrite uses `lambda=0` and the factored form. It computes one shared `t=2a` and evaluates

```
Nmain=l*(l+t*c)-H*c²,
Ninput=m*(m+t*kappa)-H*kappa².
```

Both norms retain exactly their old values. The two canceled root computations and their norm blocks previously cost12 gates once the common `H,c²,kappa²` and gamma products are treated as already paid. The replacement costs13: one operation for each of l,m,t, and five operations for each displayed norm. Applying the rewrites separately would charge the doubling of a twice; joint reuse recovers one addition. The complete resulting circuit is88=48M+40A. Its strong, auxiliary, input and ratio consumers keep all genuinely live prerequisites; in particular c² and Delta are not falsely counted as deleted.

This result rules out an improvement only in the finite evaluation family above. It is not a general arithmetic lower bound, a rejection of other positive projections, or an optimum over all universal representations.

## All-value source proof and replay

The checker authenticates the actual asymmetric source and its saved literal source, the normalized strong87 source, and the coupled88 source by SHA-256 before reading the selected87 DAG. It proves three parameterized algebraic identities and the two collapsed identities using exact symbolic expansion.

It additionally interprets the actual emitted norm expressions at the independent cuts `a,c,kappa,X,gammaH,W,rhoH`. For every one of the3,249 schedules, both norm expressions are checked against the original scalar formulas. This checks6,498 literal norm identities; caching avoids re-expanding the42 distinct expressions. This is an exact source check, not evaluation at finitely many points.

With the two proved norms used as symbolic cuts, an independent expression-DAG interner compares all eight factor values and the entire product-minus-one output against the original source. It checks29,241 exact downstream identities. All other definitions are unchanged, except exact common-subexpression reuse. These source identities prove equality of the entire polynomial on every integer assignment; consequently the original full positive zero set and valid fixed-program-slice theorem are preserved without any new semantic assumption.

As supplementary tests, every mode pair receives one positive and one signed integer assignment over four fixed radix fixtures:6,498 complete output comparisons, including3,249 signed cases, and51,984 individual factor comparisons. No complete imported universal zero or astronomical Pell witness is materialized. The fixtures are algebra tests, not finite substitutes for the inherited universality proof.

The receipt includes the complete unchanged baseline and a complete best source for each nonempty subset of the two changed norms. All remaining mode choices are reproducible from the listed templates and exact source pins. Saved receipt comparison is recursive and type-sensitive.

```
python complete87_discriminant_shear_scout.py --root /path/to/native-stream-queue --expect complete87_discriminant_shear_scout.json
```

`--output` writes a receipt to the specified path. The helper reads its pinned inputs and writes only an explicitly requested output; it has no permanent scratch-path dependency and imports no parent compiler module. This is a bounded negative arithmetic result, with an88-operation exact alternative, and no new universal operation bound.

The integrating review read the complete source and proof, checked the shear and shifted-coefficient identities and full-schedule accounting, and reproduced the complete saved receipt with a fresh run. No unresolved finding remained within the declared finite family.
