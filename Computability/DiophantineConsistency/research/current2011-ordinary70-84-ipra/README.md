# Current-port 70/84 iPRA and translated-consistency endpoint

`OrdinarySphere7084IPRA.lean` proves that standard iPRA derives both the no-zero sentence for the positive shift of the literal 70/84 expression iff the negation of the mapped native ZFC-refutation sentence, and that no-zero sentence iff `(Semiformula.lMap embedding sourceSentence)ᴺ`, the mapped Gödel–Gentzen translation of the Foundation ZFC-consistency sentence.

The Lean theorem witnesses internal derivability; it does not assert ZFC consistency. The client composes the checked [same-valuation equivalence in every IΣ₁ model](../current2011-ordinary70-84-model-join/README.md) with the [67/94 existential no-zero endpoint](../current2011-ordinary94-fresh-endpoint/README.md). The latter's reverse transfer uses machine soundness rather than a same-valuation witness map; the 70/84-to-67/94 equivalence does hold at the same valuation.

The 70 literal expression is linked to the [integer-leaf graph and degree-84 certificate](../current2011-ordinary70-84-candidate/README.md) by a separate external row parser. The exact fixed-port degree and binary operation count are externally audited, not Lean `totalDegree` or file-semantics theorems. The maintained equation/PDF is unchanged.

Guarded attempt01 passed: actual outer session 92210 exit 0, Lean exit 0, three expected `[propext, Classical.choice, Quot.sound]` reports, no warnings or `sorryAx`, 800 stable recorded guard slots, and no stop. The output `/tmp/current2011-ordinary70-84-ipra-check01/OrdinarySphere7084IPRA.olean` has SHA-256 `8a5118c46ede8edf5cab817207405e58c4a8632320d9ad8095ed48194a981eb9`. Child receipt and actual outer terminal observation are retained separately under `attempt01/`.

The runner used Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled process-group RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. It pins the checked model join, 67/94 endpoint and selected direct predecessors and recorded source/receipt slots. The guards do not constitute a complete transitive dynamic-load trace or an independent rebuild of the inherited base.

| Artifact | SHA-256 |
| --- | --- |
| `OrdinarySphere7084IPRA.lean` | `94af95ca1e15003016c71f8dc2e0f643c07d42aad6d4c4c958248974c1065e77` |
| `check01.py` | `3e7bb228c9854ccac011edcb36a778fd30c85cc09f3249dcb219137c9822de9f` |
| `attempt01/result.json` | `f73e1c926e9b5f178f486de44478973122d648fe743de321a649d58572fe9643` |
| `attempt01/compile.log` | `b0e58376280cc1454998904e1ed4946afa13619bc11be2555d0b14d8ab2205da` |
| `attempt01/outer-observation.json` | `9da8bd98574e3f38fa04789b1fede43f0c9bdf49747304441153df5f2358c521` |
