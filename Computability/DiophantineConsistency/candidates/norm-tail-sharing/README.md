# One fewer operation in complete two-root norms

Over every commutative ring,

```
(t²-s(a+b))²-4s²ab = (t²+s(a-b))²-4sat².
```

Both sides expand to the same six monomials. The right side reuses t²
and removes the extra multiplication s*s. No unknown, hypothesis,
coefficient or zero-set transformation is introduced. This is an identity
of the entire polynomials on every signed assignment, not merely an
existence equivalence.

| Literal | Domain | Unknowns | New operations | Parent operations | Exact degree |
|---|---|---:|---:|---:|---:|
| saturated_positive.json | Positive integers | 9 | **433** | 434 | 1,628,768 |
| saturated_natural.json | Nonnegative integers | 9 | 440 | 441 | 1,628,768 |
| saturated_radical_positive.json | Positive integers | 9 | **1,073** | 1,074 | 1,103,950 |
| saturated_radical_natural.json | Nonnegative integers | 9 | 1,080 | 1,081 | 1,103,950 |
| radical_jd_positive.json | Positive integers | 9 | **722** | 723 | 1,158,228 |
| integer10_baseline.json | Unrestricted integers | 10 | **479** | 480 | 1,245,324 |
| integer10_linear.json | Unrestricted integers | 10 | **483** | 484 | 1,179,788 |
| integer10_cubic.json | Unrestricted integers | 10 | **486** | 487 | 1,114,252 |
| integer10_sixterm.json | Unrestricted integers | 10 | **520** | 521 | 1,081,125 |

Operations count every live binary addition, subtraction and multiplication,
including squares and fixed scalar products. Constant leaves and shared
reuse cost zero. All nodes and declared variables are live. The inherited
exact degrees are unchanged by the polynomial identity; unreduced DAG
degree bounds are recorded separately.

`PARENTS.json` pins each whole immutable parent. For each child, the
`*_identity.json` certificate gives four cut nodes and a complete prefix
map. An exact sparse integer-ring normalizer checks the entire replaced
tail. Every other child node is verified as an unchanged parent gate after
remapping. The union covers every node, so there is no unaudited remainder.
A changed final subtraction is rejected. Sixty signed modular assignments
with the actual fixed integers compare the output and every retained node;
these are extra transcription controls rather than the identity proof.

## Whole coefficients and ordinary interpretation

The saturated circuits retain the complete compact54-sharp11-leaf binding
in `../gap2082-compact54`. The J,D radical circuit retains the whole
original31 tuple and its exact derived leaves. The ten-integer group
retains its own twelve actual signed integers in `source10/fixed/`, with
both compressed and uncompressed hashes in `FIXED_COEFFICIENTS.json`.
Each is authenticated during replay; there are no variable coefficient
ports. No coefficient is transplanted between families.

The parent ordinary equivalences and their reviews are in
[`saturated-nine`](../saturated-nine/README.md),
[`radical-jd-shared`](../radical-jd-shared/README.md), and
[the ten-integer shear review](../../PROPOSAL_REVIEW_POLYNOMIAL_SHEARS_NORM10.md).
Composing an identity with those interpretations requires no additional
Pell or positivity argument. Their named native/compiler/refutation
calibration remains inherited. This local reduction does not supply a
new end-to-end Lean or encoded internal-ZFC proof. Formalization is paused.

The ten-integer parents and payloads come from the immutable polynomial-
shears archive at440dd03ab8. Exact member and archive pins and original
licenses are retained under `source10/`. `NORM10_REPLAY.json` records all
three parent component stages in normal and optimized scratch replays;
all regenerated literal bytes agree with intake.

## Replay

From the repository root:

```sh
python3 Computability/DiophantineConsistency/tools/build_norm_tail_sharing.py --check
python3 -O Computability/DiophantineConsistency/tools/build_norm_tail_sharing.py --check
```

The generator reads previous literal graphs as inert data. It executes no
historical emitter, consistency search or Lean command. The parent
candidate directories and incoming archives remain unchanged.
