# Fresh-base translated-consistency sphere endpoints

`TranslatedSpheres.lean` checks two standard-iPRA derivations, one for each current-port 14/71/80 and 14/72/68 sphere expression. Each states that the corresponding positive-shifted no-zero sentence is equivalent to `(Semiformula.lMap embedding sourceSentence)ᴺ`, the mapped Gödel–Gentzen translation of the Foundation ZFC-consistency source sentence. The proofs compose the separate checked fresh-base sphere endpoints with `IPRABoundedRhoZFC.zfcEquiv`. These theorems establish Lean objects witnessing internal derivability, not consistency itself.

The direct producer is [`FreshCarrierSpheres`](../current2011-spheres-fresh-base/README.md), which contains both all-IΣ₁ same-zero theorems and standard-iPRA mapped-refutation endpoints; its independently generated 71/72 full-DAG binding and existing external degree certificates are documented there. Those finite count, degree and graph correspondence checks are separate from these Lean theorems. The maintained equation/PDF is unchanged.

Guarded attempt01 passed: Lean and the actual outer session 19379 both exited 0, no warnings or `sorryAx`, two expected `[propext, Classical.choice, Quot.sound]` axiom reports, 488 stable recorded guard slots, eight RSS samples and no stop. The output object is `/tmp/current2011-spheres-fresh-translated-priority-check01/TranslatedSpheres.olean`, SHA-256 `890d9de3298c927712251cfc2d0361a7319813fcf8e7964f108ab5054d26af79`. `attempt01/result.json` records child/guard data; `attempt01/outer-observation.json` separately records the actual outer exit.

The runner uses Lean `-M2800`, one worker, nice 19, idle I/O, a 120-second limit, sampled process-group RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. It pins the sphere object `37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020`, the `FreshModel106` object, their recorded sources and direct/companion/shadow slots before and after. This is not a transitive dynamic load trace or a new independent base rebuild, and its resource limits do not retroactively apply to producers. Run `python3 -I -S -B check01.py` only with its fixed inputs available and absent output path.

| Artifact | SHA-256 |
| --- | --- |
| `TranslatedSpheres.lean` | `57f0275670e99cb0fb5171f37c7b98bd82fc75f93985db0b3b3a292366e11c5d` |
| `check01.py` | `e0195badcf935a3741ecd605abedaef8e10b946934d73e35ef5f3e4400665e66` |
| `attempt01/result.json` | `d3311197caca8f3168a6cb5388408e3d66504489d26d2ea2fb99b4cd807b1060` |
| `attempt01/compile.log` | `0de90eeb2005b7726b904048f2c3c0cdf9733be8bc4809f5e27f6ab33de33108` |
| `attempt01/outer-observation.json` | `573357726ec2b4b5dffee9aefcb902b3c15aa3488b37b5a38ca7ba5074abf016` |
