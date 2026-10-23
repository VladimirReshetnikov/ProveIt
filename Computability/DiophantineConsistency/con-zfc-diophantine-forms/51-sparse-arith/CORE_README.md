# Sparse quadratic targets and smaller consistency equations

These files specify explicit integer-coefficient polynomials whose
nonsolvability in their stated domains is ZFC-provably equivalent to
syntactic Con(ZFC), using the inherited machine/compiler and arithmetic
results identified in the accompanying proofs. No consistency premise is
assumed. No global minimality or new end-to-end formalization is claimed.

Pinned repository: `VladimirReshetnikov/ProveIt`, commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`.

| Equation | Domain | Variables | Exact degree | Live binary operations |
|---|---|---:|---:|---:|
| Main signed equation | Unrestricted integers | 10 | 54,768,104 | 709 |
| Main positive equation | Strictly positive integers | 9 | 33,332,620 | 682 |
| Companion natural equation | Nonnegative integers | 9 | 33,332,620 | 685 |

The direct prior comparisons are package40's ten-integer equation
(237,520,456 / 782) and package45's nine-positive equation
(129,875,980 / 788). Different witness domains are compared separately.

## New ingredients

1. Use the actual quadratic supports to place the22 extraction targets.
   The largest target falls from35,177 to7,243, while all528 possible
   quadratic terms in the dense packed square are still checked for
   interference. The product support span falls from36,775 to8,841.
2. Encode positive parent coordinates by adding the packed successor
   word once inside the square. Keep the raw quadratic coefficients;
   the weighted records decrease from136 to94.
3. For the ten-integer finalizer, use the proved arithmetic separator
   with weights1,b,bK. The separate finalizer proof handles the possible
   square-class cancellations. Exact algebraic sharing reduces the
   literal evaluator further.

## Authoritative artifacts

- `data/polynomial.json`: complete ten-integer arithmetic DAG.
- `nine/generated/multitarget_nine_positive.json`: primary nine-positive DAG.
- `nine/generated/multitarget_nine_natural.json`: primary nine-natural DAG.
- `data/targets.json`, `data/weights.json`: literal finite positions.
- `data/coefficient_recipes.json`: raw quadratic rows and all derived leaves.
- `data/fixed_values.json`, `nine/fixed_values.json`: payload manifests.
- `coefficients/payloads/`: actual coherent native ports and fixed leaves.
- `SOURCE_PROOF.md`: full sparse-source proof and domain checks.
- `nine/PROOF.md`: source composition with the Jones finalizer and exact degree.
- `upstream/`: identified inherited proofs and parent data, with source pins.
- `certificates/`, `nine/generated/VERIFICATION.json`: finite audit receipts.

The ten-integer source proof uses the accompanying new finalizer proof for
its changed separator. The report assembles that argument with the source
and inherited semantic dependencies. Polynomial registers are abbreviations,
not extra quantified variables; every exponent is fixed and nonnegative.

## Reproduce

Run from this directory with Python3.10 or newer:

    python3 verify_release.py

Only the Python standard library is needed. Verification runs in a temporary
copy. It rebuilds the literal circuits, checks exact symbolic parent and
extraction identities, verifies fixed integer bytes, and reruns the degree
and literal-formula audits. It also checks the routines with Python's
optimization flag so checks cannot silently disappear under `-O`.

The separate nine-variable degree-certificate DAGs use700/703 operations.
They evaluate the same polynomials after resolving a leading cancellation;
the smaller682/685-operation DAGs are the primary evaluators.

The finite audits prove the finite identities and degree facts they report.
They do not by themselves prove the unbounded native-window compiler, Sun's
arithmetic theorems, or the Jones ratio theorem. The mathematical proof
states those inherited dependencies explicitly.
