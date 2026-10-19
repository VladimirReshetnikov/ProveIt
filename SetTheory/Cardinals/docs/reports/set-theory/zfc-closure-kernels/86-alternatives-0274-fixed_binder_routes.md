# Fixed-variable CP/GIC specialization: sound route, negative first cost test

## Result

Fixing the names used by the two set-theory schemas is semantically viable
while retaining the full original logical engine. In the first complete
compiler experiment it is larger, not smaller: the 268-state control becomes
277–284 states. This is useful negative evidence against counting eliminated
parameter copies as independent binary-state savings.

The alternative is distinct from the rejected equality-free calculus: all
eight original logical rows, native equality, both vacuity rows, generalization
and the existing schema gates remain. There is no claim that the new binary
tables have a verified ZFC-consistency endpoint; their source emissions and
compiler edges were checked, while the new ordinary calibration below has
not been formalized into the numerical/backend Lean interface.

## Exact formulas

Use implication, membership, equality, universal quantification and the
existing relative-falsity abbreviations from `theory_backend_experiment.py`.
Let C(a,b,c) be the exact original CP row (`bundle_C`). Replace it by the single
open formula C(0,1,2). It is understood as a theorem schema with all assignments,
or equivalently with universal closure in its only free seed variable 2.
There is no need to emit that universal closure: unrestricted GEN already
provides it.

For the GIC row, let phi be the decoded matrix represented by current
numerical parameter c. Fix its input/output variable labels at 0,1 and choose
a fresh hull label k=c+2. The emitted formula is:

  exists k [
    forall 0 (R(0,1) -> forall 1 (phi -> exists 1 (phi and R(1,k))))
    and forall 1 (R(1,k) -> exists 0 phi)
  ].

This is the original GIC template with matrix, input, output and hull roles
separated. The emitted matrix is still arbitrary c; no syntactic parser or
renaming routine is added to the machine. The proof compiler, off-machine,
renames each desired finite formula to put its two exposed coordinates at
0,1 and all other parameters at labels >=2, while freshening bound variables.
Such renamed formulas occur in the exhaustive matrix enumeration.

The same experiment also tests k=c+1. For c>0 the native code bound makes
this fresh, and k>=2 avoids the fixed coordinate labels. The exceptional c=0
is treated explicitly below. Using k=c without a zero-case treatment is not
accepted: its low-code alias has a different, unjustified effect.

## Ordinary semantic proof

Work in any nonempty irreflexive membership structure. Relative falsity R(0,0)
is false under every assignment, including assignments under binders. Thus
relative negation, conjunction and existential abbreviations have their usual
classical meaning, without needing a separate reserved variable convention.

1. Expanding C(0,1,2) gives exactly the ordinary CP requirement for the seed
   denoted by variable 2. Since assignments of that free variable are
   unrestricted, every seed is covered. Its two quantified coordinates are
   distinct, so there is no accidental capture.
2. For a fresh label k, expanding the displayed GIC formula says that every
   member x of the input domain whose phi-fiber is inhabited has at least one
   phi-related witness in the represented hull, and every member of that hull
   has a phi-preimage. This is precisely native GIC, with the exposed input
   and output labels fixed and all additional parameters still arbitrary.
3. Capture-safe finite variable renaming is available in the **retained full**
   calculus. Given any finite native GIC matrix, rename its exposed labels to
   0,1 and all remaining free/bound labels away from them; choose the positive
   numerical code c of the result. For positive native codes, every occurring
   label is strictly below c. Hence k=c+1 or c+2 is fresh. The encoded schema
   instance therefore realizes the desired instance up to the proved logical
   alpha/substitution equivalences. This uses native equality and its two
   atomic membership congruence rows; it must not be transferred to the
   previously refuted equality-free logical engine.
4. For arbitrary numerical c>0, the existing native decoder gives a finite
   formula whose labels satisfy the same bound. The k=c+2 version also handles
   c=0 directly: the truth alias has no semantic dependence on the fresh hull
   coordinate. Thus every generated instance is true in the usual ZFC model
   used for the original soundness direction.
5. In the k=c+1 version, c=0 gives k=1, colliding with the output coordinate.
   Expanding that literal instance, using phi=True and irreflexivity, reduces
   its first conjunct to `forall x not R(x,k)` and makes the second conjunct
   true. It is exactly the existence of an empty object. Native GIC already
   supplies an empty object from a false matrix, and ZFC proves its existence.
   This exceptional instance therefore does not change the calibration.
6. The original gate c!=a,b is retained around the conjunction bundle. It does
   not suppress any fixed-coordinate GIC matrix: for every c choose the now
   otherwise-unused gate parameters a,b distinct from c. Likewise C(0,1,2)
   is obtained at any allowed gate triple. Both vacuity schemas retain their
   original actual parameter meanings and their required side conditions.

Accordingly the full fixed-coordinate theory has the same ordinary native
CP/GIC consistency calibration, and so the same target Con(ZFC), subject to
transporting the unchanged complete logical engine and the numerical/physical
interfaces. This is a proof plan with explicit ordinary semantic arguments;
we have not claimed a completed Lean proof of the new theory comparison.

## Exact macro and state-cost plan

No new register is needed. Existing scalar pushes and constructors are reused:

- literal 0: macro 171;
- literal 1: macro 177;
- literal 2: macro 177 followed by increment top-wff;
- fresh k=c+1: macro 168 followed by one increment top-wff;
- fresh k=c+2: macro 168 followed by two increments top-wff.

The original logical prefix and cleanup/gate tail remain in place. The
compiler experiment independently symbolically executes AX and re-extracts
all emitted DAG edges. Its 100 grammar seeds times three exponents per recipe
(1,800 trials total) produced complete totalized binary tables:

| Source | Working states | Difference from matched control |
|---|---:|---:|
| Original, reviewed conjunction layout | 268 | 0 |
| C fixed only | 280 | +12 |
| G fixed, k=c+1 | 277 | +9 |
| G fixed, k=c+2 | 277 | +9 |
| C and G fixed, k=c+1 | 283 | +15 |
| C and G fixed, k=c+2 | 284 | +16 |

Source of exact counts and tables:
`../machine_encoding/fixed_axioms/results.json`.
The relative overhead depends on the actual grammar/framework; it is not
legitimate to subtract nine or twelve states from the optimized 246-state
machine or assume a constant 62-state framework for every source.

## Independent finite diagnostics

`fixed_binder_semantics.py` evaluates independently constructed named formula
trees and compares them with direct CP/GIC relational specifications over all
irreflexive relations on one, two and three elements. Results in
`fixed_binder_semantics_results.json`:

- 201 fixed-C seed cases;
- 98,434 fresh fixed-G matrix/domain cases;
- 69 zero-alias k=c+1/empty-object cases;
- all 98,704 comparisons pass.

These tests confirm the local expansions and catch capture mistakes. Finite
models do not witness the strength of the full infinitary schema, and these
checks are not substitutes for the all-domain arguments above.
