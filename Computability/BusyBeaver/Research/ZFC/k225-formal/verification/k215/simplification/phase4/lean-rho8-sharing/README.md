This checkpoint shortens the guarded Lean proof of `DomRho8.rho8_all` by sharing already proved formula schemas and removing unreachable private lemmas. The generated module falls from 35,185 bytes / 614 lines to 30,114 bytes / 517 lines. The public `DomImp`, arithmetic bounds, substitution operation, and arbitrary-natural-code endpoint are unchanged.

The bootstrap identifies `b32` with `b19`, `b34` with `b20`, and the truth conclusion `b11` with `h.truth`. Eleven used guarded-template conclusions also equal existing unconditional bootstrap schemas. Reusing those proofs and following only their actual dependencies reduces the bootstrap from 61 to 58 declarations and the guarded templates from 81 to 59. All 117 retained lemma statements and all eight numerical guards are preserved. The generic proof relation, deduction induction, composition/distribution lemmas, and final `rho8_all` proof remain byte-identical. This is a reduction of this proof presentation, not a claim of global minimality or a new logical basis.

The isolated source plus five explicitly typed API clients passed Lean 4.32.0 in 1.066 seconds, with zero warnings and four reports containing exactly `propext` and `Quot.sound`. The command used one worker, a 120-second deadline, a 12,288 MiB limit, and the shared proof-build lock. The ten project providers leading to `Code254`, compiler, shipped `Init`, source snapshot, log, and object hashes are recorded. The immutable phase3 provider ledger is included as provenance; its embedded earlier 204-module toolchain description is historical. This isolated check selected ten providers from the later 185-module phase3 closure. A full endpoint refresh is recorded separately by the integrating build.

Source `d1a8acc92200d70680eda9c3bda6b76ee965f4674b0cabd1210a2ee2174b6a59` is the checked and selected prefix-form proof. Producer `2ce2960fb16c894230dab4a259bb2721e378a1f1dc9ce84ba06717f095cb7308` originally generated it. Integration removed one trailing space on producer line 407, yielding `143691b8e28ac5fa9cd393ec16a470953e39128a391b03080b8856dc56282210`. The whole Python AST is identical. The original producer and its results remain unchanged in history; separate successor controls reproduce the same source. The optional infix-notation experiment is not part of this checkpoint.

Both producer versions passed five generation modes: default guarded generation, explicit guarded templates, explicit 629-node plan, unplanned 674-node generation, and generic 629-node input. Their output hashes match the existing presentations. Two invalid mode combinations reject before producing a source file. The default output plus the five clients equals the exact kernel-checked snapshot. No producer, optimizer, certificate, or Python checker is trusted for mathematical soundness: the generated typed proofs remain checked by Lean.

The finite inputs are the unchanged Source149 certificate (`3cf18a5f…8452`), its CD230 templates (`c788460c…d087`), and the maintained deterministic 629-node plan/replay for the generic fallback. Complete hashes and copies are inside the text archive. Independent source and saved-record reviews are retained under `peers/` in that archive; the reviewer did not rerun the producer or compiler.

`evidence.tar.gz` contains the selected source and producer, prior sources/producers, exact diffs, actual logs and records, the immutable basis metadata, finite inputs and generated outputs, and independent reviews. Identical byte sequences are stored once; `paths.json` maps the original absolute paths in unchanged records to archive members. No compiled objects or bytecode are included. Historical supervisors retain their actual absolute paths; use the portable generation helper for a new generation-only check.

To verify saved evidence without executing any archived code:

```sh
python3 -B review_saved.py --packet .
```

To rerun the five generation modes and two rejection controls in a new directory, without invoking Lean:

```sh
python3 -B regenerate.py --packet . --out /tmp/domrho8-sharing-regenerated
```

The latter uses the exact archived producer and finite inputs. Kernel reproduction belongs to the maintained serial Lean closure driver after integrating the source; it must continue using the machine-wide proof lock. `summary.json` records this checkpoint's scope and archive pins, while `saved-review.json` records the read-only publication check. These records do not replace the separate full endpoint build or assert a runtime speedup from the proof-size reduction.

The additive `whitespace-successor-review.json` independently checks the whitespace correction and its saved controls. `portable-control.json` and `portable-control.tar.gz` retain the subsequent actual run of the portable generation helper: five matching outputs, two rejections, and no proof-kernel invocation. The packet helpers are source-readable utilities; the independent mathematical peer concerns the proof and producer deltas, not these later packaging utilities.
