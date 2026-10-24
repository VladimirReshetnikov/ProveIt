# Fourteen unrestricted integers, degree568,145 operations

This separate literal evaluator computes exactly the reviewed
147-operation `crt14_degree568` polynomial from
`ConZFC_Constructive_Reductions_2026-10-23.zip`. It has **14 unrestricted
integer unknowns**, exact total degree **568**, and **145 live binary
operations**:88 multiplications,30 additions and27 subtractions. The six
complete fixed coefficients, including both cone coefficients and the
already shifted MF, are unchanged.

The complete equation is the output of `equation.json` set equal to0.
Variable and coefficient leaves are explicit, shared registers are
abbreviations rather than additional unknowns, and every node is live.
The two exact removals are:

```
parent node24 = beta*J,
parent node25 = 1+node24,
parent node41 = node25-1 = node24;

parent node66 = Delta*I^2,
parent node67 = 1+node66,
parent node68 = node67-1 = node66.
```

Replace every reference to old41 by old24, and every reference to old68
by old66, then renumber every retained node and every named register.
`NODE_REMAP.json` supplies all175 parent-to173 child entries, including
both deleted aliases and the complete output map. Each local identity
is `(1+x)-1=x` in every commutative ring. Induction along the original
node order proves equality of every mapped node and hence of the entire
output polynomial for arbitrary variable and coefficient values. This
is stronger than zero-existence equivalence and needs no sign/Pell
assumption.

The inherited ordinary proof is `source/parent/PROOF.md`, with its
independent review in `source/ordinary-peer.md`. Both original complete
scoped author replays and independent normal/-O receipts are embedded
in `source/original-review*.json`. `SOURCE_PINS.json` authenticates the
whole immutable archive and every one of its104 integer-component
members; selected ordinary proof sources and all six coefficient
payloads are copied here. No archival coefficient generator or formal
proof source is executed, edited or compiled.

The identity preserves all exceptional branches, the positivity guard,
the unit-product finalizer and every signed witness. In particular,
there is no attempt here to import the new positive-domain main-root
elimination into this integer equation. Its signed main parameter and
projection require a separate proof.

The source's unbounded degree proof transfers verbatim. The norm has
exact degree512 and the final equation568, with the positive actual
coefficient

```
[j^256 w^88 v^104 h^16 r^32 c^64 z^8] P
    = 2^520 * 3^344 * beta^256.
```

The syntactic upper bound from the literal graph is632. Two complete
actual-six-port line controls attain degree568; these supplement the
ordinary leading-form proof and are not used to infer an upper bound.

`check.py` imports only the independent sparse-ring oracle. It verifies
all495 coefficients of the cleared four-root norm with every one of
its six cut ports bound, the unit-product finalizer identity, topology,
liveness, both exact aliases and all remaps. It authenticates every
compressed and raw coefficient byte, compares every mapped node on100
actual-port controls (including v=0/c=0) and50 signed free-coefficient
controls, and rejects two corrupted alias definitions/uses.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_constructive_integer14_shared.py --check
python -B Computability/DiophantineConsistency/candidates/constructive-integer14-shared/check.py
python -B -O Computability/DiophantineConsistency/tools/build_constructive_integer14_shared.py --check
python -B -O Computability/DiophantineConsistency/candidates/constructive-integer14-shared/check.py
```

All pass; command receipts are in `VERIFICATION.json`, and
`MANIFEST.json` seals the packet. The incoming archive, frozen parents,
canonical PDF/TeX and common documents remain untouched. This remains an
ordinary arithmetic reduction with the original named native/refutation
calibration. Lean is paused, the internal-ZFC derivation remains open,
and no consistency proof or global minimum is claimed.
