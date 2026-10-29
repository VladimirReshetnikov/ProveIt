# Shared witness-bound proof validation

Source commit `a58822e2ff37f7076a9ad8b3d0537b3a75c45080` and parent `641e6227aaf9bfe33c876237097ee73f16e326e3` match the tested final and baseline `ArithmeticConstructionAssembly.lean` snapshots byte-for-byte. Their SHA-256 hashes are `1cc5bd39c814ab497fd326ec091265fa8f3969e46f54712b9c928b3f45eaba2f` (parent) and `36b2e60d6a79530a8616f01165a871f1b302d46567df84621a1fc3e6cc1c0681` (commit). The change removes 13 net lines by expressing the repeated proof tactic once in a `section members`-local macro. The ten existing theorem statements, definitions, assumptions and imports remain unchanged. The original proofs were moved by `1b2d29dded2` and trace in its parent to Claude-coauthored `f1463077445`.

Paired source-ordered builds of `ArithmeticConstructionAssembly`, `ArithmeticConstructionBound`, and `ArithmeticCurrentConstruction2011` all passed. The target objects differ; both unchanged direct-client objects are byte-identical across phases. All six build logs are empty. The initial pair used a historical transitive PowerRecovery/FirstNorm provider chain; a source-current provider rebuild and paired target/client replay produced exactly the same corresponding objects. The refreshed build objects are:

| Module | Baseline SHA-256 | Final SHA-256 |
|---|---|---|
| `ArithmeticConstructionAssembly` | `e7f69999cd0ced816ece92c68ae5ffe60052e3c4802a464c946eee29053d3e71` | `318e46220bb483989e2852bff47830337d08daa7da32415dfa45609beea01a86` |
| `ArithmeticConstructionBound` | `b99aa2b68acf9b93716c38e30381921cdb8bed6ed822990d73a9b72da5f9c259` | `b99aa2b68acf9b93716c38e30381921cdb8bed6ed822990d73a9b72da5f9c259` |
| `ArithmeticCurrentConstruction2011` | `4eb80a884111110533ec5c7a16767079f176dc512f334b5096d0264eb4cc95e0` | `4eb80a884111110533ec5c7a16767079f176dc512f334b5096d0264eb4cc95e0` |

The refreshed provider chain rebuilds the following current-source modules; each row pins its before/after source, actual first-path inputs and output object:

| Module | Source SHA-256 | Object SHA-256 |
|---|---|---|
| `ArithmeticPellPowerRecovery` | `8b01819d4814e68efc399df146d705015a3ded742bedf5a5b59dc054ca3b016b` | `6f3522b965cb55e4229ba8007fa5f01babeacc4df94e8f3df76a9a15c5d01b18` |
| `ArithmeticHalfBinomialSandwich` | `29e88bc407c6db1ea32962cc30b975c824cca76bec499f4764e6563bfc036966` | `61db8eb1a1f287bbe58c3e72eb05d4fb3f810dff6361892cf044364b856e69c0` |
| `ArithmeticHalfBinomial` | `35e749c1e5757314d772a03308d84d3a322a61ce93e4cd5c3293b659f2af8b00` | `e53329dcceb598267b33f2ba38baf2df7344aa91f91475e58656c92c5de070b9` |
| `ArithmeticOuterSeed` | `78db14630fd6f01ef36f227ab4681e620624b07130b20c284e950153cd0011a7` | `7cfb8a4d7c2cac0d8188fed5792585854ac68e1987928943486d68c86f3dc2c8` |
| `ArithmeticConstructionBoundPell` | `bfb6db9d60d53d0d6283081e6a8b92e3feff4b9c1295f316d9a0bd64cb284ef8` | `1980d51eaadd5d22d1c81217ae25342b5b183df4c0d65575324839587be3cb6a` |

The provider build pinned current FirstNorm (`8ed12b630d`) and its rebuilt current FirstIndex objects from `/dev/shm/firstnorm-time-positive/final-records.json` before and after each build. Twelve external direct project source/object inputs have successful source-matched producer receipts:

- `ArithmeticTilingWord`: source `b412f70d7089bd9387b00cfa6a5d82b75baaf3cf9d665d85ce9f1e8b8e64c049`, object `db92ef94779be73a6bc6b79dde7edfadfec9958a6a0c36c72011a55bd212ce31`; `/tmp/rowrel-sharing/alternate-records.json`.
- `ArithmeticPackingCells`: source `587aba5c1fdc98187f40301e613d3594c5b579dd5da6c070bc73651bc92e8174`, object `0ba3df188c1fae546e103aee68f47e96deda4c4a1782e33da6bd1c6a932b0f1a`; `/dev/shm/claude-transport-sharing/assembly-phase-records.json`.
- `ArithmeticRankForcing2011`: source `5dc4f4170b0d2e0202dade59dd2da97e511d5869ee5b1db2e624367b69a8394d`, object `6f662b989ef254022389ba70e4bcecfadced9b72b99e26533891e71f4efbb7b0`; `/tmp/four-positive-wrappers/refreshed-final-records.json`.
- `ArithmeticController`: source `ad3dc1fe546f22f92134860b2ec0bf94a0983a163c2dd2d166639a34ca1e79d2`, object `9d7d5436e5e98c3d025254e27714ae0f1f532a037ee5844f05a4a6b373681126`; `/tmp/construction-share/bound-refresh-records.json`.
- `ArithmeticConstructionUnit`: source `12b2d20c5aeb22bca72c7caa02e8fcaf28d3eff7e1559240ec4cdf62c37e297e`, object `3e3f5908d210bd4ade3b9c4905f1cec32c43c44758ed24fa9c67ac48f093666e`; `/tmp/variation-tail-sharing/refreshed-common-records.json`.
- `ArithmeticConstructionVariation`: source `fd64bbaaa59016ac501ed3d1e53124f0f9163fc51767cbf1428dd95dc78c2672`, object `1d5398ef9465346996d318960a4d4ad41af6111059e60cd58cfdfd32c945b293`; `/tmp/variation-tail-sharing/refreshed2-final-records.json`.
- `ArithmeticOuterSeed`: source `78db14630fd6f01ef36f227ab4681e620624b07130b20c284e950153cd0011a7`, object `7cfb8a4d7c2cac0d8188fed5792585854ac68e1987928943486d68c86f3dc2c8`; `/dev/shm/wb-member-macro/provider-records.json`.
- `ArithmeticPellAuxiliarySeed`: source `f3769f93fe14b8ad50310050e8dbf9b7fa4347adda34af63eeee1abe470fd2c2`, object `77a7611beed37708c840269caf2d7f042fd3c9ad2a8aaa32d98fafd6df044743`; `/dev/shm/pell-half-p-pos/final-records.json`.
- `ArithmeticConstructionBoundPell`: source `bfb6db9d60d53d0d6283081e6a8b92e3feff4b9c1295f316d9a0bd64cb284ef8`, object `1980d51eaadd5d22d1c81217ae25342b5b183df4c0d65575324839587be3cb6a`; `/dev/shm/wb-member-macro/provider-records.json`.
- `ArithmeticConstructionZero`: source `fdef557a958ba7176529795359d5145a0e713ffe8a4a38a1f8609bd59d3e617c`, object `d7df6e08c7d2089edfba036b794f81905bb94499e5f0a3afcee32e161702229b`; `/dev/shm/construction-tau-positive/final-records.json`.
- `ArithmeticCurrentSentence2011`: source `10c1a2e92f05c9765e91fd872050b25c23a94754ec87a0122aebd2e4c90c13e6`, object `42b8d5c746802687ba40fdaa93304c6c5f0513a5b0f674c8434795081febbfdb`; `/tmp/signed-pairs-factors/final-records.json`.
- `ArithmeticLocalNormalization`: source `5d5c6d4850083c1cc1993cad50da5b88dba39948a034133d19f1d2169f477803`, object `f78f08081135f5295c9516cd97208d5799818700223c01c3c767ebc84f29006d`; `/tmp/construction-share/bound-refresh-records.json`.

Eight refreshed probes pin all three phase target/client objects and eight provider objects. Their 58 common namespace declaration names have byte-identical printed types and axioms; two private generated macro syntax/implementation declarations are added. Sampled simp and instance registration outputs match. These reports do not establish equality of proof bodies or all persistent extensions. An independent external-import test attempted `wb_bound h` after importing both initial and refreshed Assembly objects: all four runs produced the same unknown-tactic error. This tests that named syntax, not all possible parser extensions.

Final-phase client input source paths sample the baseline workspace Assembly source before adoption; the final target build independently links the actual imported object to the final source snapshot. Wider project, Foundation and Mathlib transitive dependencies remain cached; no full current-source closure is claimed. Raw logs and compiled objects are not included. Full validation depends on the transient external files and build environment, which may later disappear.

External evidence files and SHA-256 hashes:

- `/dev/shm/wb-member-macro/README.txt`: `ee39242344cd2e09bc6ec33751d689bfe0ee064d2889d5223b1a9ba799959e05`.
- `/dev/shm/wb-member-macro/baseline-records.json`: `351fda701522f81ba08161dcb3f657e44cb7800d334efc75006f8f538d7285c1`.
- `/dev/shm/wb-member-macro/final-records.json`: `b23cceebd56fa13058e56e18f1a7bb163e1a34f1544279b46d29dfb7de25a18b`.
- `/dev/shm/wb-member-macro/baseline-fresh-records.json`: `ff47cc44036ff4934775b15d2f7aa1219abc2618a959f70444e7dec1e4e621ea`.
- `/dev/shm/wb-member-macro/final-fresh-records.json`: `4edfc3d71351cb3cdd11fd673649e479eecbe8b28cd3816287f11bff762ccda5`.
- `/dev/shm/wb-member-macro/provider-records.json`: `98c6220090037223751ff2ac94563df5fa99c92f306452701749bc40937be9d3`.
- `/dev/shm/wb-member-macro/fresh-probe-records.json`: `92720fa47f272f8ebae0a36bf210706bb43852a6c56aaa647ace65f48e98ad89`.
- `/dev/shm/wb-member-macro/build.py`: `2e58bb9da33ec4798ff83bcceb47d2b83957e47ee58b2ea2513f5ce933b25419`.
- `/dev/shm/wb-member-macro/build-fresh.py`: `34fe7f70f69ebe3141fca4bc96f198cf493a9a9583fc00ce2d4fc139c1fd1386`.
- `/dev/shm/wb-member-macro/build-providers.py`: `c53015a8365168d9fab3260e8a4f8783bc931af31774d2c34040b99f1320fed7`.
- `/dev/shm/wb-member-macro/probe.py`: `e3eea6e0f51a3324084eec3cb55e79b12371a9d522755d90c219f08ba7d88d2a`.
- `/dev/shm/wb-member-macro/audit.py`: `5d9286488f125cccaec7d58fc479df51842cfec7a50953758b5485a1294242fd`.
- `/dev/shm/wb-member-macro/audit.log`: `40204302fc3c56cc64d6ecb398033197a879c55ca17512b9a2b6cce963910d42`.
- `/dev/shm/wb-macro-peer-93/external-parse.lean`: `5f8f29f03febd8087b350d6e79f3989e433e8a5376e7fc1d7a27d8ad407df99c`.
- `/dev/shm/wb-macro-peer-93/external-parse-records.json`: `36a415228e7b5ea31fb5e99b98ddb766ea6eb77c2f735315e3543df48c210f14`.
- `/dev/shm/wb-macro-peer-93/fresh-external-parse-records.json`: `d465e87e4ca1487c87baac3f8e4fa882e21b4b1fb316b23e6609f12f2ee779f4`.
- `/tmp/wb-macro-peer-review-93.txt`: `5255642cff77acd5087a12f4c403c61e27dedcda78984fbd8f2bab71802b3287`.
- `/tmp/wb-macro-peer-audit-93.py`: `9f0083dc9a814de463e41dc49b8af6cdb810531f7c8ae2617f3ee8000640ee1c`.
- `/tmp/wb-macro-peer-audit-93.log`: `0307a4390f50cb426a76cbe5473fd5481f69ff5778f46ad224019ab736b5ea81`.

The independent peer review checked source snapshots, paired and refreshed build records and first paths, the rebuilt provider chain and twelve direct plus two extra provider associations, 11-object probe pins, common reports and registrations, and external tactic scope. It verified the commit and parent against both tested snapshots.
