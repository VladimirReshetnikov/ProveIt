# Independent review of symbolic-port ranked-main client

**PASS within recorded direct-provider scope.** The no-Lean `check.py`
verifies the attempt03 terminal and retained receipts and logs, source,
runner, helper and object hashes, recorded direct guards, and the bridge
object against its successful producer receipt. `CompactSymbolicPorts` and
`ArithmeticStandardCasts` are pinned captured provider objects; their full
source-to-object and transitive ancestry is not independently rebuilt here.
Both expected axiom reports list only `propext`, `Classical.choice`, and
`Quot.sound`. This review is not a Lean replay; transitive, dynamic and
between-sample ancestry is inherited.

For an `IΣ₁` model, the auxiliary `q_lower` theorem assumes `b+1=exp(590069)`
and `J>0`. Its proof uses `exp(6)=64`, monotonicity of exponentiation,
`590069≥6`, and `bJ≥b` to obtain `bJ+1≥64≥33`. The main theorem uses
**variable natural ports** `(beta,K,L,beta+H)` and assumes `(beta:V)+1` is
that model exponential, `L<beta`, `beta+H<2beta`, an actual 72-graph zero
and positive witnesses. It applies the checked window-to-ranked-main bridge
to identify the main Pell coordinates at the actual graph rank. All three
cast identities or inequalities are hypotheses of this theorem.

This client does not itself specialize the concrete compact tuple or
establish the first-index congruence, reverse witness map, consistency
equivalence, or iPRA endpoint. The “source-only draft” source header is
retained byte-for-byte; attempt03 supplies the recorded checked status.
The bridge producer is reviewed separately in the [window-ranked-main
review](../p64-qcube72-window-ranked-main-independent/README.md).

Run while the captured temporary paths remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-symbolic-ranked-main-independent/check.py
```
