# Generic 71/60 versus 67/94 ring zero equivalence

`OrdinarySphere7160Generic.lean` proves `zero_iff94`: over a commutative strictly ordered ring with the explicitly supplied `FreshCarrierSpheres.Facts` (discreteness, a mod-four homomorphism, and the two specified Pell-norm exclusions), with positive beta and all 14 coordinates positive, the ordinary 71/60 sphere value is zero iff `Carrier94Value.value94` is zero at the same coordinates. It separately proves that the ordinary strong unit `1+I²−Delta*(f²−1)` is not `−1` by mod-four analysis. No model, literal-graph or iPRA endpoint is asserted by this packet alone.

The nonzero first and auxiliary norms make their squares at least one; a zero of the four-square sphere therefore forces both to be unit squares and both residual squares to vanish. At strong residual zero the auxiliary coefficient becomes `I²`, giving the established negative-unit exclusion; the other named norm exclusions force all five ordinary factors to `+1`. The reverse direction first extracts the strong factor's `+1` value from the product and its mod-four exclusion, then the other unit factors.

Attempt01 failed after Lean elaboration due to conflicting order instances from unnecessary Foundation namespace opens, plus an unused-section-variable warning; its source, log and receipt are retained. Attempt02 removed those opens and omitted the unused variables. Lean and actual outer session 51812 both exited 0, with no warnings or `sorryAx`, two expected `[propext, Classical.choice, Quot.sound]` reports, 298 stable guard slots and no stop. Its object is `/tmp/current2011-ordinary71-60-generic-check02/OrdinarySphere7160Generic.olean`, SHA-256 `73a022ff49f38e554c0ece51601aba36cd11931fceb2e020493fb5dd09127c2b`.

The guard uses Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled group RSS stop at 3.5 GiB and available-memory stop at 10 GiB. It authenticates the direct `FreshCarrierSpheres` and `Carrier94Value` providers and recorded supporting slots; this is not a transitive dynamic-load trace or an independent rebuild of their inherited base.

| Artifact | SHA-256 |
| --- | --- |
| `OrdinarySphere7160Generic.lean` | `5808bcc7f662ff319ad6c64811260e216739888a7d4a8d89c68390d2561f9bae` |
| `check02.py` | `4424a2f434a9dfb42837367854ffdcfc646b3fa72ab6102c777aa9afd0fd2271` |
| `attempt02/result.json` | `f528cbbcd0f7bca3b4f54e4ca7dfaded857eb662a7a586791d6935cfc96bb003` |
| `attempt02/compile.log` | `e1a7d9d4633a1f3b32f62977eeb0d2349375d500f9e9d17402acec697a49bf77` |
| `attempt02/outer-observation.json` | `13ede8a4c9f8db03b7d586047001dfdbb2a7f61be6d6f3c1482f49f8434dea12` |
