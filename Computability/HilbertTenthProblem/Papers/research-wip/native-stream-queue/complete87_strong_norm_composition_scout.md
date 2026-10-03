# Strong-norm composition: a bounded negative result on complete87

No smaller complete source was found. The normalized asymmetric universal polynomial remains **87 = 48M + 39A**, exact degree169, with its ordinary positive input and19 positive witnesses. The new family composes the strong norm with the main or input norm, or composes all three common-discriminant norms. This extends the earlier main/input joint-norm scout in a different dimension; it does not rerun its four schedules or the3,249 discriminant-shear choices.

| New complete schedule family | Best total | M | A |
|---|---:|---:|---:|
| Main and strong norm |92|52|40|
| Input and strong norm |91|51|40|
| All three common-discriminant norms |94|53|41|
| Main and strong norm, factoring the common c |92|52|40|

These are complete polynomial costs after exact common-subexpression reuse and pruning, including every surviving prerequisite, fixed-coefficient multiplication, square, subtraction, product and final subtraction of1. They are not isolated norm-block counts. There is no new operation bound, witness projection or universality claim.

The source-pinned prototype is `complete87_strong_norm_composition_scout.py`; the receipt is `complete87_strong_norm_composition_scout.json`. They read the frozen normalized source from `complete75_asymmetric_scale_tradeoffs.json` after authenticating that file and the asymmetric, normalized-strong and coupled parent sources. No parent module is imported, and no repository file is written. The prototype requires an explicit repository WIP root and writes only its explicitly requested output.

## Exact algebra and complete positive-zero semantics

Use precisely the parent's quantities

    Delta = (a+2)^2-1,
    c = kY+eta, kappa = 2d*x+b+delta*Delta,
    D = ac+X+(rho+sigma)H,
    mu = a*kappa+W+rho*H,
    t = i*c^2.

The relevant factors are

    Nm = D^2-Delta*c^2,
    Ni = mu^2-Delta*kappa^2,
    Ns = f^2-Delta*t^2.

The other five factors are unchanged: the first norm, auxiliary norm, packed index, transport and coupled linear unit. The source register `A` is Delta; it is not the mathematical Pell parameter a+2.

For any commutative ring, either sign s in{-1,1} gives

    (x^2-Delta*y^2)(u^2-Delta*v^2)
      = (xu+s*Delta*yv)^2 - Delta*(yu+s*xv)^2.

The literal schoolbook schedule computes the two products in each root. The alternative uses

    p=xu, r=yv,
    real=p+s*Delta*r,
    imag=(x+y)(u+s*v)-p-s*r.

This is the exact three-product multiplication identity, with all additions charged; its lower multiplication count does not make it cheaper in the equal-cost model. The final norm takes two squares, multiplication by Delta and one subtraction. Applying the identity twice composes all three factors. No root positivity or Pell classification is assumed in this arithmetic identity.

The separate c-factored schedule exploits the actual source's `t=i*c^2`. Put r=i*c and reuse its `Ac2=Delta*c^2` register. Then

    Nm*Ns = (D*f+s*Ac2*r)^2 - Ac2*(f+s*D*r)^2.

Here r is computed and charged. This identity is valid for either sign and all integer inputs. It does not weaken `t=i*c^2` to the unsound inherited-rank shortcut `t=i*c`.

For each candidate, all original definitions except the final product register remain literally unchanged before pruning. The new finalizer multiplies the proved joint factor by precisely the other original factors, then subtracts1. Thus **each complete new polynomial is identical to the parent polynomial on every integer tuple**, not merely equivalent on a canonical or positive subset. Its degree is consequently exactly169; its complete supplied positive zero set and ordinary input relation are unchanged. In particular the original proof still restores all eight individual units to+1, retains both strict ratio slacks, preserves the full strong-rank condition and handles the signed index/transport/linear factors in the original dependency order. Combining norms in the evaluator does not delete those mathematical factors.

## Finite family and paid consumers

The enumerated family has106 choices:

- Two strong-containing pairs, each with two signs and two multiplication algorithms:8 choices.
- All six ordered triples, two signs at each composition, and either algorithm at each composition:96 choices.
- The two signs in the special c-factored main/strong construction:2 choices.

Some ordered/sign choices produce equal arithmetic functions or duplicate schedules. The count is of declared choices, not distinct polynomials. Every choice is rebuilt as a complete DAG. The only simplifications are exact commutative common-subexpression reuse, integer constant evaluation, zero/one identities, and pruning dead definitions. No arbitrary symbolic optimizer decides the claimed gate counts. The same pass leaves the baseline at87 operations. Multiplication by a nontrivial fixed constant counts one.

The shared consumers prevent apparent deletions. The auxiliary factor still needs `Delta^2*t^2`, so the strong norm's t-square and discriminant products are not automatically removed by norm composition. The `c^2` computation also remains needed through `t=i*c^2`. The root D's input, ratio and source definitions are retained wherever a composed root uses them. All actual survivors, including newly computed r in the factored schedule, appear in the saved emitted sources.

A separate tempting unit rewrite, replacing `Delta^2*t^2` by `Delta*(f^2-1)`, was already covered by the earlier joint-norm scout and is not counted here as new evidence: it costs88 because the original `Delta*t^2` remains live in the strong factor and the substitute needs an extra subtraction. Likewise no unsquared sum of norm residuals is proposed: these residuals can have either sign away from zeros, so their nonnegativity cannot be assumed from the final unit theorem. No first-ratio slack, input norm or rank factor was removed to make a local ledger look smaller.

## Reproducible evidence and scope

The receipt records every choice and its exact M/A ledger, and a complete best source for each of the four families. It verifies:

-106 exact symbolic identities of the literal new joint expressions, using independent cuts at Delta,D,c,mu,kappa,f,i and the actual relation t=i*c^2;
-106 complete finalizer factorizations and9,116 checks that all86 retained old definitions were unchanged;
-2,544 complete old/new polynomial evaluations, including1,272 signed assignments;
-exactly the same free-input set, topological closure and liveness of every paid gate in every emitted circuit.

The finite numerical assignments use modest integer source inputs and admissible-looking radix/mask fixtures. They check polynomial evaluation, not actual acceptance of a compiled program and not astronomical complete Pell witnesses. The all-value identity supplies the proof of zero-set preservation; the numerical cases supplement it.

Reproduce with:

    /path/to/sympy-python complete87_strong_norm_composition_scout.py \
      --root /path/to/native-stream-queue \
      --output /path/to/fresh-receipt.json \
      --expect complete87_strong_norm_composition_scout.json

Receipt comparison is recursive and type-sensitive, and execution under `python -O` is rejected. This is an exhaustive test only of the106 explicit norm-composition schedules. It does not rule out better arbitrary circuits, different auxiliary normalizations, other finalizers, or a new universal representation below87 operations.

## Root review

Root read the literal generator, common-discriminant identities, c-factored
strong-rank substitution, full finalizer construction and saved ledgers. A fresh
writer replay reproduced the frozen receipt byte for byte. The conclusions
remain bounded to the declared 106 schedules; the 87-operation benchmark and
its ordinary-input, positive-witness and exact-degree claims are unchanged.
