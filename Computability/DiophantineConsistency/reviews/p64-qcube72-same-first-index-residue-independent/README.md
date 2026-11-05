# Independent review of the same-index first Pell residue

**PASS within recorded direct-provider scope.** The no-Lean `check.py`
checks the successful attempt01 retained and terminal receipts/logs, source,
runner, helper, output object, all recorded direct guards, and the direct
index-window object against its successful producer receipt. Both axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. This
is not a Lean replay; transitive, dynamic and between-sample provider ancestry
remains inherited.

The generic helper assumes `P>0` and
`2*ycoord n (2*(P−1)+1)=k` in an `IΣ₁` model. It applies the Pell residue
quotient theorem **to that supplied `n`** with modulus `2P`, obtaining a model
element `s` with `k=2n+4Ps`. Model-natural subtraction is truncated; `P>0`
justifies `(P−1)+1=P` and the modulus premise.

The fixed-port client assumes an actual positive 72-graph zero in the model
at the fixed compact symbolic tuple with arbitrary natural `K`. It extracts
one `n` satisfying `n<R<2n` and the two first-Pell coordinate identities,
establishes `P=XY²>0`, applies the helper to **that same `n`**, and returns
the window, both coordinate identities, and the residue
`k=2n+4Ps` together with a model witness `s`. Both `n` and `s` can be
nonstandard model elements. This avoids a separate index-uniqueness step.

The theorem does not prove `2n=R+1`, `U|h`, the old carrier congruence, a
reverse witness map, a consistency equivalence, or an iPRA endpoint. The
“Unchecked draft” source header predates the successful attempt01 and is
retained byte-for-byte. The direct project provider is reviewed separately
in the [fixed compact index-window review](../p64-qcube72-fixed-compact-index-window-independent/README.md).

Run while the captured temporary paths remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-same-first-index-residue-independent/check.py
```
