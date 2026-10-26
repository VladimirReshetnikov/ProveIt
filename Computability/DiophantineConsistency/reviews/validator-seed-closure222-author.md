# Actual internal C222 seed closure, empty objects and singletons

**PASS, author validation.** `controller_certificate` authored and fully
self-reviewed the new132-line `ZFCinPA.ValidatorSeedClosure222` and52-line
checks. The sole import is the frozen `ValidatorSeedWitness222`. The new
results produce actual C222 checker proof witnesses over every internal
arithmetic model of IΣ₁; no external Nat completeness or semantic seed
validity is assumed. Only these two new sources and this packet's receipts
were added; no accepted source, shared object or Git state was changed.

| Frozen artifact | SHA-256 |
| --- | --- |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedClosure222.lean` | `e0fa4d18aca886701bfc6a4593f2b468372e4bc220d497cdfe05aa25e1d77d83` |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedClosure222Checks.lean` | `07c829b62543c4ae10cd7d7f3c65cacf3c2c09a77a170e40c973a2d3373dd0e3` |
| `reviews/validator-seed-closure222-replay.json` | `a26ffb2dd781c1d863fcea15e0bc394baef8c80baf5997c2ba230897f17c7ccf` |

The first two paths are repository-relative; the replay path is relative
to `Computability/DiophantineConsistency/`.

`closure_support a b k m` assumes exactly the explicit certificate
`Vac a m`. It derives

```text
CProv222(clos(a,b,k,m) → ∀b(b∈k → m)).
```

The literal closure contains `¬∀a(m→¬U)`, with the original inner universal
`U` retained. The proof first invokes the checked finite conversion to
`∃a(m∧U)`, then projects m and eliminates that existential using the supplied
vacuity. Universal monotonicity at b finishes the implication. This is not
a definitional identification of the double-negated connective encodings.
All four codes remain arbitrary. `seed_supported_request` combines this
with the actual seed under precisely `c≠a,c≠b`; it does not assume `Vac c c`.

The false-matrix instance uses a=b=0 and c=1. Both literal gates hold, and
`Vac 0 1` is the established false-code certificate. It yields the actual
empty-object formula

```text
CProv222(∃1 ∀0 ¬(0∈1)).
```

For each arbitrary internal p, set b=p+1, k=Eind(b,p), and a=k+1. The checked
code bounds k>b,p prove the seed gates and `Vac a(Eind(b,p))`; they also
prove b≠p,k. Closure supplies membership⇒Eind. The earlier request theorem
supplies p∈k. The new `Eind_symm` is a finite deduction from actual Eind
Euclideanness and primitive-reflexivity⇒Eind. Membership transport then
supplies Eind⇒membership. This reverse implication is universally
generalized only after using `Vac b(p∈k)`, justified by b≠p,k. The two
universal implications are joined by actual conjunction/distribution
certificates. No GEN-under-hypotheses oracle is supplied.

The final singleton conclusion is

```text
CProv222(∃k (p∈k ∧ ∀b (b∈k ↔ Eind(b,p)))),
  b=p+1, k=Eind(p+1,p).
```

Here k is a fixed numeric label chosen before constructing the formula,
not a variable recomputed inside its own binder. The required matrix
vacuity is at a=k+1; self-label vacuity is never assumed. Both free p and
its universal closure are exported, together with the exact
`∃code, ArithmeticHistory222.value code = formula+1` witnesses.
Checks retain a=b=1,c=0 in the supported-seed projection, arbitrary-model
p=0, actual Nat empty/singleton history witnesses, and the concrete C222
derivability adapter in that direction. False code1 is unchanged.

Both complete sources and the adapted preparation/compile drivers were
read before execution; the final sources were reread in full afterward.
The first main build failed solely because `one_ne_zero` was ambiguous
between the opened namespaces. Qualifying `_root_.one_ne_zero` resolved
both occurrences. Its rejected source, log and timing remain in the replay
record. No statement, premise, mathematical deduction or resource cap
changed.

Final fresh main/checks passed in2.95/1.92 seconds, maximum RSS1,817,488 KiB.
The main log is empty. All14 focused axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. Fresh object hashes are
`1286d05cda77fc759ed06f01c5fd0fc96a82822be250d6a9c17afe3082081501`
and `894a19ea954498025dc085b38127af927e7844329e05a1c78fbabb217fc0baa8`.

The private overlay is `/tmp/seed-closure222-controller-o2lwm86j/lib`.
Input inventory SHA is
`220a0ad8470b90c42e475a553261a01be96b0aadede0d772b9e1463dbbba6aa5`.
It reauthenticates127 cached current-source modules, including95 Foundation
modules,412 object companions and38 explicit external import boundaries.
Only the new two leaves were compiled, with Lean4.32.0,
`-M6000 -j1 -DElab.async=false`, private symlinks and a512MiB disk reserve.
All selected source, object, compiler, manifest and external pins matched
before and after. The final free space observation was955,285,504 bytes.
This is not a fresh Foundation or whole-repository replay.

`complemented47_review` independently challenged the proposed normalization,
binder conditions and symmetry direction before implementation; that plan
review is distinct from the forthcoming full frozen-source review and
root's independent replay.

Empty objects and singletons are substantive consequences of the actual
helper-free seed. They do not yet give the full transitive/power-closed
native container axiom, arbitrary GIC, uniform theory translation,
semantic validity of all seeds, runtime calibration or PA/HA provability
of the equation/consistency equivalence. Those larger obligations remain
open.
