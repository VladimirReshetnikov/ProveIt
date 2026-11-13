# Fresh-base 67/94 translated-consistency endpoint

`Translated94.lean` checks that standard iPRA derives the biconditional between the no-zero sentence for `Carrier94Syntax.naturalExpression94` and `(Semiformula.lMap embedding sourceSentence)ᴺ`, the mapped Gödel–Gentzen translation of the Foundation ZFC-consistency source sentence. It composes the checked [fresh 67/94 endpoint](../current2011-ordinary94-fresh-endpoint/README.md) with `IPRABoundedRhoZFC.zfcEquiv`. This is a Lean witness to an internal derivability statement, not a proof that ZFC is consistent.

The source endpoint proves existential no-zero equivalence through machine soundness; it does not claim a same-valuation reverse equivalence. The source-to-67-row graph comparison and degree-94 certificate are external checks linked by the endpoint packet; no Lean total-degree or PDF-binding theorem is claimed.

Guarded attempt01 passed: actual outer session 61207 exit 0, Lean exit 0, one expected `[propext, Classical.choice, Quot.sound]` report, 326 stable input/companion/shadow guard slots and no stop. Its output `/tmp/current2011-ordinary94-fresh-translated-check01/Translated94.olean` has SHA-256 `9864c3dc909141f45cb44717f7fc8d0bc571847c9d703942b4368e3edd1eba0d`. The child result and outer observation are retained separately under `attempt01/`.

The run used Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled process-group RSS stop at 3.5 GiB and a 10-GiB available-host-memory stop. The runner pins the endpoint and six module objects and their captured direct records. Those guards do not dynamically trace all inherited transitive loads, retroactively enforce producer resource limits, or constitute an independent rebuild of the current14 base.

| Artifact | SHA-256 |
| --- | --- |
| `Translated94.lean` | `2c86bbcf3e0bd807da52c634572b22b9f44471cd8af68243dd4cc5c2bb64ca66` |
| `check01.py` | `2b32183af3d64c170878cc00ddcac39e25fa4d4593117647024d31d0d1879930` |
| `attempt01/result.json` | `675f4e568e1c6bc82365cef14414928d113a28164cd7b782b1cb152b95fbdd62` |
| `attempt01/compile.log` | `384e891ab4b907e3f322eb1e8b49da2a5314bc710926d76948ee9445cd4214fe` |
| `attempt01/outer-observation.json` | `7add47ea76ee72b1255fd4b6aa235fb1c952b983c239cd907c918807ef26087d` |
