# Fresh-base 67/94 existential no-zero and standard-iPRA endpoint

`FreshCarrier94.lean` checks four declarations for the positive shift of the current-port `Carrier94Syntax.expression94`:

* `halts_of_zero94`: an actual candidate zero in an arbitrary IΣ₁ model gives a time at which the decimal215 machine halts.
* `zero94_of_zero`: a maintained-equation zero gives a candidate zero after replacing the strong multiplier by `Delta*i`.
* `bridge94`: their existential no-zero predicates agree via the checked current14 machine bridge.
* `standard_equivalence94`: standard iPRA derives the candidate's no-zero sentence iff the negation of the mapped native ZFC-refutation sentence.

This is an **existential** transfer; it does not claim every candidate zero maps back at the same valuation or even with the same strong witness. It establishes the existence of an internal derivation in Lean, not the consistency of ZFC. The mapped Gödel–Gentzen translation of the Foundation consistency sentence is a separate corollary, not checked in this packet.

The source is a local adaptation of `ModelCarrier94`: it reuses `FreshModel106` for the maintained evaluator and model positivity, and directly assembles the no-zero bridge using the existing current14 `HACurrentEquation2011.polynomialBridge`. The other imports come from the separately documented [six-module fresh-base build](../current2011-ordinary94-six-module-build/README.md), including the minimally edited extraction snapshot described there. The complete external [source-to-graph comparison](../current2011-ordinary67-94-syntax-binding/README.md) and the independent [graph/degree certificate](../current2011-ordinary67-94-candidate/README.md) are separate checks; no PDF binding or Lean `totalDegree` theorem is asserted.

Guarded attempt01 passed with actual outer session 81138 exit 0, Lean exit 0, four expected `[propext, Classical.choice, Quot.sound]` reports, 284 stable input/companion/shadow slots, no warnings or `sorryAx`, and no stop. The object `/tmp/current2011-ordinary94-fresh-endpoint-check01/FreshCarrier94.olean` has SHA-256 `dfe72edd726a5a140d509f606f866ce6dd8e8d1f008bc96a957c1c1509ce642c`. `attempt01/result.json` records the child and guard data, while `attempt01/outer-observation.json` records the observed outer exit separately.

The runner uses Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled process-group RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. It authenticates the six installed module objects and their captured result receipts, plus direct providers and their recorded companion/shadow slots. It does not dynamically trace all transitive loads or independently rebuild the inherited base. The initial 106 extension final-client failure and the separately passing corrected client are preserved in that inherited ancestry.

| Artifact | SHA-256 |
| --- | --- |
| `FreshCarrier94.lean` | `fc792393a91b12a34346e02aeefff3e799f710c1651afccdaaa5fd26c914747e` |
| `check01.py` | `86f635d8dada820d2663120c7b6ecffc89effa3706ee0ad7b237ca0a6850e872` |
| `attempt01/result.json` | `5378e5fae67be1259a9b28143ab9be3d08d3c6e3e6cdfef55ae05676923311de` |
| `attempt01/compile.log` | `8418179400ea0bc51a9e2c86f4cc6182e059e25e8f46fc3c5a5ed3183194f0d2` |
| `attempt01/outer-observation.json` | `0558700490d565cad5a56a22e74693f7d79b4e8b6b56c54d1cc3ab7f56c217f9` |
