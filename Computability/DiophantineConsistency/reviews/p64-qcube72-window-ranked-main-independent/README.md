# Independent review of the window-to-ranked-main bridge

**PASS within the recorded direct-provider scope.** The no-Lean `check.py`
checks the successful attempt02 terminal and retained receipt and log,
source, runner, helper and object hashes, all direct guards, and the exact
object links to three successful producer receipts. The compiler output
contains only `propext`, `Classical.choice` and `Quot.sound`; these are Lean
metatheory axioms in the report, not extra axioms of iPRA. No Lean replay or
source-only transitive rebuild was performed. Transitive, dynamic and
between-sample ancestry remains inherited. The temporary artifacts must
remain available to rerun the audit.

`FreeMainWindowRankedMain.main_at_rank` assumes an `IΣ₁` model, natural
ports, positive witnesses, an actual 72-graph zero, `q≥33`, and both model
inequalities `p₂<p₀` and `p₃<2p₀`. Its conclusion gives a main Pell root
`g` with the main Pell coordinates at the **actual graph rank** `R` equal to
`g` and `c`. It applies the generic rank-window theorem for positivity and
`R+1<q⁴`, then derives `2R<c` using the main Pell equation, positivity of
the graph variables and the conditional half-window theorem, and applies
the ranked-main client. The ranked-main client previously used the explicit
`0<R` and `2R<c` assumptions; this bridge discharges them under the two
mask inequalities and other stated hypotheses.

The direct links lead to the independently reviewed [generic rank
window](../p64-qcube72-generic-rank-window-independent/README.md),
[rank half-window](../p64-qcube72-rank-half-independent/README.md) and
[ranked-main](../p64-qcube72-ranked-main-independent/README.md) packets.
This theorem does not itself specialize the compact ports, derive the first
Pell-index congruence, construct a 72-to-76 reverse witness or establish an
iPRA endpoint. The old source comment calling the proof unchecked is retained
byte-for-byte; the successful attempt02 gives its recorded status.

Run while the captured provider paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-window-ranked-main-independent/check.py
```
