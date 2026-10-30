# HA proof of the 87-gate equation rewrite

`AdaptiveFactor87HA.ha_proves_equivalence` is an actual HA derivation of
both implications between the exact parent and 87-gate arithmetic no-zero
sentences. The two sentences represent the positive-shifted 13-variable
expressions. This theorem proves neither sentence nor the equivalence of
either sentence with `Con(ZFC)`.

The proof first establishes equivalence in every IΣ₀ model, including
nonstandard tuples, using the complete split-expression identity. Completeness
produces an actual IΣ₀ proof, which is weakened to PA. The existing
Gödel–Gentzen translation supplies an HA proof of the translated implication
in each direction, and the existing no-zero translation lemmas convert both
targets to the ordinary arithmetic sentences. Lean's classical metatheory
constructs proof existence; the HA proof system remains intuitionistic.

The 23-module HA/negative-translation prerequisite chain was rebuilt twice
against the separately replayed literal providers. Both complete 25-module
builds passed with matching source, object and full-log hashes at
`/tmp/adaptive-factor87-ha-build-j1uxavxw` and
`/tmp/adaptive-factor87-ha-build-g_tun74o`. Their final two client modules
were then strengthened from IΣ₁ to IΣ₀ and rebuilt independently against the
matching prerequisite chains at `/tmp/adaptive-factor87-ha-isigma0-kf2qx33e`
and `/tmp/adaptive-factor87-ha-isigma0-7le8zg8f`; source, object and full-log
hashes again matched. The 23 prerequisite records remain valid; the two older
client records in the prerequisite states describe the preceding IΣ₁
snapshot. [States, complete logs and the prerequisite rebuild driver](adaptive-factor87-ha-replay/)
are retained. The driver uses inherited guarded literal, Foundation and
Mathlib boundaries; it records the six historical source changes and rebuilds
the affected local HA syntax chain. Its 356 canonical guards and local source
snapshots were checked before and after each full run.

The final main source SHA-256 is
`6fd7ed57dd26c346261f1bbadf38278939c534e396cc61f9e17c9209a0b8a902`, object
SHA-256 `0f6186d39ac11adcafb60980b463d9712ed81fd6459558f04d2bcd615dfb57b5`;
the check source is
`ce16ed4ffcb3015666f0ef16f0f6350826e782f3b55f11fc9fa7e138c21151dc`, object
`12e576b41db13016f1c7a04089f1f8da4b688b7e760f60b79824adccf3dd605f`.
All four reported theorem axiom sets contain only `propext`, `Classical.choice`
and `Quot.sound`. An independent source reviewer checked the theorem's exact
scope and the use of completeness and negative translation.
