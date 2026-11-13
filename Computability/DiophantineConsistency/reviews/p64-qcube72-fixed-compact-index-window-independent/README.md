# Independent review of fixed compact first-index window

**PASS within recorded direct-provider scope.** The no-Lean `check.py`
verifies the successful attempt01 retained and terminal receipts/logs,
source, runner, helper, output object, all recorded direct guards, and both
direct project-provider objects against their successful producer receipts.
The axiom report contains only `propext`, `Classical.choice`, and
`Quot.sound`. This is not a Lean replay; transitive, dynamic and
between-sample ancestry remains inherited.

The theorem assumes an `IΣ₁` model, arbitrary natural `K`, and an actual
positive 72-graph zero at the fixed symbolic compact ports. It concludes
that **one and the same model index** `n` satisfies `n<R<2n`, together with
both first-Pell coordinate identities, for the actual graph rank `R`. In
the source, the existential witness `n` and its `n<R` proof are extracted
from the fixed compact first-index theorem. The same `n` and its first
coordinate identity are passed to the generic half-index lemma along with
the fixed compact main coordinate at `R`; the final tuple returns that same
`n`, `n<R`, and `R<2n` together. Model indices can be nonstandard.

The theorem does not prove the stronger `2n=R+1`, the missing first-index
congruence, a 72-to-76 reverse map, a consistency equivalence, or an iPRA
endpoint. The “Unchecked draft” source header predates the successful check
and is retained unchanged. The two direct project inputs are reviewed in
[fixed compact first index](../p64-qcube72-fixed-compact-first-index-independent/README.md)
and [generic half-index lower](../p64-qcube72-half-index-lower-independent/README.md).

Run while the captured temporary paths remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-fixed-compact-index-window-independent/check.py
```
