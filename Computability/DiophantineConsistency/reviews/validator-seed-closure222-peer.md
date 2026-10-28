# Actual internal C222 seed closure — independent review

26 October 2026. **PASS; no correction requested.** Reviewer:
`circuit_reduction`, author of neither reviewed source. I read the entire
132-line main, 52-line checks, 123-line `ValidatorSeedWitness222`, actual
`ArithmeticSeedTemplates222` definitions, the relevant frozen Eind and
relational deductions, the author receipt and replay metadata. This is
an independent source/math/provenance review. Per the assigned scope I
did not run Lean again; root owns the separate independent fresh replay.

| Frozen artifact | SHA256 |
|---|---|
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedClosure222.lean` | `e0fa4d18aca886701bfc6a4593f2b468372e4bc220d497cdfe05aa25e1d77d83` |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedClosure222Checks.lean` | `07c829b62543c4ae10cd7d7f3c65cacf3c2c09a77a170e40c973a2d3373dd0e3` |
| [Author receipt](validator-seed-closure222-author.md) | `89277fab413ce5d3e056d932cac94b687442363aead9d2ede1c55469b4833fe8` |
| [Replay metadata](validator-seed-closure222-replay.json) | `a26ffb2dd781c1d863fcea15e0bc394baef8c80baf5997c2ba230897f17c7ccf` |

`closure_support` preserves the literal closure body. Its inner
`¬∀a(m→¬U)` is converted by the existing finite certificate to
`∃a(m∧U)`, projected to `∃a m`, and eliminated using exactly `Vac a m`.
The supplied matrix vacuity is thus used at the input binder `a`, not at
the container/matrix self-label. All four numeric codes remain arbitrary.
The final universal at `b` is applied to a closed implication proof.
There is no generic GEN-under-open-assumptions step.

`seed_supported_request` retains the actual gates `c≠a,c≠b` and the
additional explicit input vacuity `Vac a c`. The empty-object instance
uses false code 1, `a=b=0,c=1`, and `vac_falsum 0`. Both seed gates follow
from `1≠0`. Its output is precisely the actual checker certificate for
`∃1 ∀0 ¬(0∈1)`, with no unasserted fresh-label or positivity restriction.
The focused `a=b=1,c=0` check separately verifies a legal zero self-label
using `vac_truth 1`.

For the generic singleton deduction, closure gives membership⇒Eind and
the previously proved request gives `p∈k`. The new symmetry certificate
uses `Eind_euclid p b b` with reflexive `Eind b b`. The reverse membership
implication uses `Eind_el_l b k p` in the correct direction after that
symmetry. Generalizing it at `b` uses the explicit resource
`Vac b (wel p k)`, whose two gates are exactly `b≠p,k`. Universal
distribution combines both directions into the actual encoded `biff`.
No vacuity of the open closure/request assumption or arbitrary primitive
equality atom is supplied implicitly.

The final choices are `b=p+1`, `k=Eind(b,p)`, `a=k+1`. The existing
literal constructor bounds prove `k>b,p` in the arbitrary internal IΣ₁
structure. Consequently `a≠b,p`, `k≠a,b`, and `b≠p,k` all follow, and
`Eind_vac b p a` provides the required matrix vacuity. The proof never
assumes `Vac k k`. The fixed numeric label `k` is selected before the
formula is constructed. The conclusion is singleton membership up to
Eind, not a claim of primitive-equality extensionality. `p=0` is allowed.
The final GEN at `p` acts on an established CProv theorem with no open
assumption; the exported witnesses use the actual
`ArithmeticHistory222.value code = formula+1`.

All main results are internal numeric proof-code deductions. The checks'
last theorem, `concrete_c222_singleton`, deliberately applies
`cProv_nat_iff` to specialize the established result to standard Nat
`KCode222.C222`. That adapter is a final check, not a premise or oracle
in the internal main. The preceding Nat checks expose history values
directly. This distinction matches the author receipt's scope.

I independently rehashed all 127 selected input sources, 412 cached object
companions, 38 external boundaries, compiler and package-manifest pins,
parent receipt/drivers, both final sources/snapshots/objects/logs/timings,
and the rejected development record. Every comparison passed. The final
source text embedded in the receipt agrees with the reviewed files. The
author's final capped runs passed in 2.95/1.92 seconds with an empty main
log and 14 axiom reports containing only `propext`, `Classical.choice`,
and `Quot.sound`. The rejected run was only the ambiguous `one_ne_zero`
name; checks were not executed on that failed main. The corrected final
pair is the accepted run. These observations do not claim a fresh replay
of the 95 Foundation modules or the rest of the cached closure.

This packet proves actual finite C222 checker witnesses for support,
empty objects and singletons up to Eind. It does not prove the stronger
native container/GIC axioms, general represented proof translation,
semantic validity of the seed, machine calibration, or the final PA/HA
equation-consistency equivalence. No reviewed source, dependency object,
shared document or Git state was changed by this review.
