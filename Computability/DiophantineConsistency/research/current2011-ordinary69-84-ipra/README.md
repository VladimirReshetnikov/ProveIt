# Current-port 69/84 all-model and iPRA endpoint

`OrdinarySphere6984IPRA.lean` checks that the positive-shifted 69/84 and 70/84 expressions have the same zero at the same valuation in every IΣ₁ model. It then proves that standard iPRA derives both the 69/84 no-zero sentence iff the negation of the mapped native ZFC-refutation sentence, and that no-zero sentence iff `(Semiformula.lMap embedding sourceSentence)ᴺ`, the mapped Gödel–Gentzen translation of the Foundation ZFC-consistency sentence.

The proof composes the [69/70 all-ring value identity](../current2011-ordinary69-84-literal/README.md) with the checked [70/84 iPRA endpoint](../current2011-ordinary70-84-ipra/README.md). The latter ultimately uses the 67/94 existential no-zero transfer via machine soundness. The 69/84-to-70/84 equality and model-zero equivalence preserve each valuation; the later reverse transfer is existential. Lean witnesses internal derivability; this does not assert ZFC consistency.

The 69 literal expression is linked to the [integer-leaf graph and degree-84 certificate](../current2011-ordinary69-84-candidate/README.md) by a separate external row parser. The exact fixed-port degree and binary operation count are external checks, not Lean `totalDegree` or file-semantics theorems. The maintained equation/PDF is unchanged.

Guarded attempt01 passed: actual outer session 34228 exit 0, Lean exit 0, four expected `[propext, Classical.choice, Quot.sound]` reports, no warnings or `sorryAx`, 1,035 stable recorded guard slots, and no stop. The output `/tmp/current2011-ordinary69-84-ipra-check01/OrdinarySphere6984IPRA.olean` has SHA-256 `b637b0c851a20ecb141a5a7a3267615e403294bc355ca21a6839c21a2fef68e3`. The child receipt and actual outer terminal observation are retained separately under `attempt01/`.

The runner used Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled process-group RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. It pins the checked literal and 70/84 endpoint objects and selected direct predecessors and recorded source/receipt slots. The guards do not constitute a complete transitive dynamic-load trace or an independent rebuild of the inherited base.

| Artifact | SHA-256 |
| --- | --- |
| `OrdinarySphere6984IPRA.lean` | `5de0f23e5624ec63dc10708d68325adcd8e90455e26b687535ac70e376b6b5db` |
| `check01.py` | `75123ea96b4699b6d0ef313433664476a554d05e491ebadfa5989c9a76b892f5` |
| `attempt01/result.json` | `a2dd7786c10308bcbb79e1a545bfce481ae0d5ae92043fccf36bf9a26d79cf07` |
| `attempt01/compile.log` | `f1b1c313b8a5bdb12db421a5953c8b46934c7d98d0732e7e188778c7b8f5455d` |
| `attempt01/outer-observation.json` | `aa65e1a50779b6166ddefb57c3676f7c0b2704a75a48e2cf17f0af218838bbe5` |
