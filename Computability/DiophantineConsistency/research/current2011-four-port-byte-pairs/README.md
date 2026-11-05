# Two current-port byte-decoder pairs

The two checked Lean declarations compose the previously checked symbolic byte-recipe decoders at the same current2011 ports:

* `BetaKernelPair.decode_pair` proves that **natural-valued** base-256 decoding, cast to integers, of the beta and K symbolic big-endian byte lists yields ports 0 and 1. The beta source theorem uses integer-valued `Nat.ofDigits`; the checked `Nat.coe_ofDigits` bridge reconciles these conventions without evaluating the long list.
* `MaskPair.decode_pair` proves the corresponding natural-decoder statements for the MC and once-shifted MF symbolic lists at ports 2 and 3.

Both are propositions about Lean list expressions. The independently checked external payload/gzip comparisons in the individual recipe packets are separate; neither pair reads or proves anything about files, gzip, PDF or TeX.

Beta/K attempt03 passed: actual outer session 29018 exit 0, Lean exit 0, `[propext, Classical.choice, Quot.sound]`, 685 stable recorded guard slots, no warnings or `sorryAx`, object `/tmp/current2011-four-port-BetaKernelPair-check03/BetaKernelPair.olean` SHA-256 `a18e7afc1c8a74124f653d06abeab866b3a80df8c66cb29a3a3bb77d51bbe35a`. Attempt01 failed recursion-depth elaboration; attempt02 retained the type distinction between integer-valued and natural-valued `Nat.ofDigits` and failed with a type mismatch. Both failures and actual outer exits are retained. Attempt03 uses the explicit cast bridge and keeps the beta list locally irreducible.

MC/MF attempt01 passed: actual outer session 62025 exit 0, Lean exit 0, the same axiom set, 685 stable slots, no warnings or `sorryAx`, object `/tmp/current2011-four-port-MaskPair-check01/MaskPair.olean` SHA-256 `f863499874eb6583f2d613429651df373f8b61c2bfe6a3fda4917656d1fc1e2d`. Both bounded runners use Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled 3.5-GiB group-RSS and 10-GiB available-memory stops. They recheck the four component producer states/direct guards and their point-in-time inputs; transitive dynamic/package and base ancestry remains inherited.

| Artifact | SHA-256 |
| --- | --- |
| `BetaKernelPair.lean` | `80ca7c881b25f341ba84c06bd6f2a670a3719feba57fd44ef7056ad36425b02d` |
| `BetaKernelPair-check03.py` | `9f7315c3531959d1567f1c08ef3abed9b85cd111e04b238275155179322beb4e` |
| `BetaKernelPair-attempt03/result.json` | `5d566ad6d858b1075b0ac378df307fbc23f63f7cb0f0ed9d3250e811754bc735` |
| `MaskPair.lean` | `770db4d3a08d9f072f4ae198e5ad89c1f3f64177ef0db8c0091de1e64ccde661` |
| `MaskPair-check01.py` | `0cb8f11e6b106c942260f2e3b37daa38de23ad31be2a90d1c669df223103931d` |
| `MaskPair-attempt01/result.json` | `25239858e03f9eacf4c1f72bcecdfb61d29e420c8fabf93e7558a8294a8940f7` |
