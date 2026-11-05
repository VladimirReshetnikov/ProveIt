# Independent review of the actual-rank composition

**PASS within the recorded direct-provider scope.** The no-Lean `check.py`
checks the successful attempt03 retained and terminal receipt, source,
runner and helper, object and log hashes, all recorded guards, and the two
direct provider objects against their own successful receipts. The compiler
log contains only the expected axiom report: `propext`, `Classical.choice`
and `Quot.sound`. These are Lean metatheory axioms in the report, not
additional axioms of iPRA. Provider transitive, dynamic, and between-sample
ancestry is inherited; this audit is neither a Lean replay nor a source-only
rebuild. Its temporary object and provider paths must still exist to rerun it.

The theorem `FreeMainRankedMain.main_at_rank` takes an `IΣ₁` model, natural
ports, positive witnesses and an actual 72-graph zero, together with **all**
three premises `q≥33`, `0<R` and `2R<c`. Here `R` is the actual graph rank
defined in `FreeMainAuxNorm.rank`, with natural-model truncated subtraction.
It concludes that the main Pell coordinates at this `R` equal a root `g` and
the actual graph coordinate `c`. It obtains the strong and auxiliary norm
identities from the actual zero and passes them to the separately reviewed
conditional rank theorem. No unconditional rank positivity, half-window,
first-index congruence, 72-to-76 reverse implication, or iPRA endpoint follows
from this client alone.

The direct providers link to the separately reviewed
[conditional rank](../p64-qcube72-conditional-rank-independent/README.md) and
[actual auxiliary norm](../p64-qcube72-aux-norm-independent/README.md)
packets. The successful theorem source still says “Unchecked draft” because
those source bytes were retained unchanged. Attempts 01 and 02 are failures
and are not used for the passing conclusion.

Run while the captured temporary objects remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-ranked-main-independent/check.py
```
