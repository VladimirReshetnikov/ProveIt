# K/S with mixed commutation preserves refutability

Replace unrestricted rho8 by K and S, and replace rho4 by the single schema

```text
M(i,j,A) = Q_i NN(Q_j A) → NN(Q_j(Q_i A)).
```

Keep every other exact Code254/KCode222 row, the original gated bundle,
truth zero, MP and theorem-only GEN. The [ordinary proof](proof.md) gives
primitive-recursive refutation translations in both directions between this
new calculus and the accepted native calculus. Thus their consistency
statements are equivalent by an argument formalizable in PA, and the accepted
native calibration transfers the equivalence to ZFC.

This is a reviewed ordinary calibration. The [independent root review](root-review.md)
read the complete proof, its atomic-stability prerequisites and the finite
bridge checker and found no defect. A second [source review](opening-review.json)
by `opening_encoder` also found no defect and explicitly discloses authorship
of the earlier Hilbert infrastructure. The frozen proof retains its original
“proposal” header; this README records its subsequent review status.
There is no new Lean/Rocq theorem, compiled source, transition table, runtime
simulation or startup proof in this packet. K/S alone remains unresolved by
this argument. The equivalence concerns finite refutations, not identical
derivable native codes.

The key construction co-translates formula codes **and numeric variable
labels**, preserving the matrix/private-label coupling in the exact bundle.
An explicit delimiter argument proves injectivity, hence preservation of the
bundle gates. Atomic stability makes every translated code stable; the mixed
row supplies the translated commutation rule. The bundle bridge retains both
nested quantified negations and their two reversals of implication.

The original [finite result](bridge-result.json) checks 1,364 Hilbert nodes
and seven closed conditional bridges. The [builder](check_bridges.py) uses
an exact copy of the earlier [Hilbert checker](hilbert.py); its only axiom
schemas in this run are K, S, rho2 and rho6. M and the bundle are discharged
premises in the local bridges, and every GEN premise is closed. This finite
check supports the local arrows; the all-natural injectivity and
proof-translation arguments remain ordinary mathematics in the proof.
The [complete proof DAG](bridge-dag.json.gz) is gzip-compressed without changing
its decoded bytes. The [original freeze](freeze.json) preserves source and
execution pins; [publication.json](publication.json) maps those exact bytes.
The initial run passed. No separate stdout/stderr files were captured, and no
reconstructed transcript is represented as a raw process log.

Source 144 supplied the K/S-only atomic-stability lemmas. `opening_encoder`
made their finite Hilbert implementation explicit in the
[earlier K/S+QS proof](../k218-quantifier-stability/README.md).
Root suggested co-translating labels and the replacement mixed row and
independently reviewed this result. `review_upstream_reflection` authored the
injectivity argument, literal-bundle bridge, complete refutation translation
and seven-bridge checker. The accepted [218-state construction](../candidate-k218/README.md)
continues to use its original classical rows.

To reproduce only the inexpensive finite bridges, run from the repository
root using a new directory:

```sh
mkdir /tmp/k218-mixed-commutation-check
cp Computability/BusyBeaver/Research/ZFC/k218-ks-mixed-commutation/check_bridges.py /tmp/k218-mixed-commutation-check/
cp Computability/BusyBeaver/Research/ZFC/k218-ks-mixed-commutation/hilbert.py /tmp/k218-mixed-commutation-check/
python3 -B /tmp/k218-mixed-commutation-check/check_bridges.py
```

It writes fresh `bridge-result.json` and `bridge-dag.json` beside the copied
scripts. The library pin is checked before import. No external dependency,
solver, network access or proof-assistant compiler is needed. The builder
refuses to replace an existing result.
