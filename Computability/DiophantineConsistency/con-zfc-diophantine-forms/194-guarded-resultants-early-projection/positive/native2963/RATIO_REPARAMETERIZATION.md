# Exact elimination of the F-divisibility quotient

[`RatioReparameterization.lean`](Lean/DiophantineConsistency/RatioReparameterization.lean)
checks package 52's Section 3 substitution. For `0<B<C`, `F>0`,
`J | F-1`, and `C | F-1`, it proves

```
old H = B+j_old*C,  j_old>=1,
J*F | Q*F+J*(H-C)
```

is equivalent to `J | Q` and `H=C+F*(B+j_new*C)` for a natural
`j_new`. The same value of `H` is preserved. The theorem
`exists_old_iff_new` transports any additional predicate on `H`, so it
also preserves square tests involving the later Pell register `I`.

The exported witness data are explicit computable natural numbers:

```
newIndex = (((H-C)/F-B)/C).toNat
oldIndex = (1+((F-1)/C)*B+F*j_new).toNat.
```

Their correctness theorems establish exact divisibility and nonnegativity
before using either natural-number conversion. No witness is selected from
an existence theorem. The old index constructed by the reverse formula is
at least one.

The source register `E=i*J*D*C^2`, `F=(A^2-1)*E^2+1` has explicit
polynomial formulas for `(F-1)/J` and `(F-1)/C`. Their identities prove
both congruences without positivity or square assumptions.
`vars_F_congruences` instantiates them directly for
`Jones1982.Nine.Vars` from the existing `NineRatio.lean` interface.

The regression file checks nontrivial forward/reverse indices, the `F=1`
boundary, actual coefficient recipes, and counterexamples when the
coprimality congruence, the congruence modulo `C`, or the positive old-index
requirement is omitted. The arithmetic definitions use no axioms; theorem
audits use only Lean's three standard axioms. This establishes the exact
reparameterization step, independently of the source compiler semantics.

`NativeNineRatio52` now instantiates the substitution on the actual
`Jones1982.Nine.Vars` registers. `ratio_sound_new` recovers the central-binomial
divisibility, that `b` is a power of two, and `8*g<cap` from the four new
conditions. `ratio_complete_new` supplies the six new natural witnesses
from the existing stronger bound `32*g<cap` and divisibility. Its new index
may be zero; the explicit reverse index is positive and preserves `H`.
The numerical size hypotheses are exactly those of the existing Jones
ratio interface. This closes the ratio substitution against that theorem,
while retaining the separate source and native calibration obligations.
