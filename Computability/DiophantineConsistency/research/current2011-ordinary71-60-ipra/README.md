# Current-port 71/60 iPRA and translated-consistency endpoint

`OrdinarySphere7160IPRA.lean` proves that standard iPRA derives both:

* the no-zero sentence for the positive shift of the literal 71/60 expression iff the negation of the mapped native ZFC-refutation sentence; and
* that no-zero sentence iff `(Semiformula.lMap embedding sourceSentence)ᴺ`, the mapped Gödel–Gentzen translation of the Foundation ZFC-consistency sentence.

The Lean theorem is a witness to internal derivability; it does not assert ZFC consistency. The client composes the checked [same-valuation equivalence in every IΣ₁ model](../current2011-ordinary71-60-model-join/README.md) with the [67/94 existential no-zero endpoint](../current2011-ordinary94-fresh-endpoint/README.md). The latter's reverse transfer runs through machine soundness rather than a same-valuation witness map; the former's 71/60-to-67/94 equivalence does hold at the same valuation.

The 71 literal expression is linked to the [integer-leaf graph and degree-60 certificate](../current2011-ordinary71-60-candidate/README.md) by a separate external row parser. The exact fixed-port degree and binary operation count are externally audited, not Lean `totalDegree` or file-semantics theorems. The maintained equation/PDF is unchanged.

Guarded attempt01 passed: actual outer session 77676 exit 0, Lean exit 0, three expected `[propext, Classical.choice, Quot.sound]` reports, no warnings or `sorryAx`, 525 stable recorded guard slots, and no stop. The output `/tmp/current2011-ordinary71-60-ipra-check01/OrdinarySphere7160IPRA.olean` has SHA-256 `652809cc682ad29cc7ed71fcdd008514c7b6d9438a59ff221d80a9e61ae71256`. Child receipt and actual outer terminal observation are retained separately under `attempt01/`.

The runner used Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled process-group RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. It pins the checked model join, 67/94 endpoint and selected direct predecessors and recorded source/receipt slots. The guards do not constitute a complete transitive dynamic-load trace or an independent rebuild of the inherited base.

| Artifact | SHA-256 |
| --- | --- |
| `OrdinarySphere7160IPRA.lean` | `a169a2e71e6699ef84f6196f43ef3bb54245208213cc32f776adadfa622f4421` |
| `check01.py` | `1f2d2b5c598357b98478702afcf9ff70a2783d3dd9c64bf1d437bd48a453d5c5` |
| `attempt01/result.json` | `02a0f2ee160b713451846433b47a097df22c4590c24711fb567fe2f1abac45b8` |
| `attempt01/compile.log` | `dcd89bfab11a0a7040239ef3c78921d7c00f42403baed4251b9f76181f37a027` |
| `attempt01/outer-observation.json` | `7c9e2f0d4ad8fa861a8aec2640bca30ad86014eefcd96a6fc2193fa286682b92` |
