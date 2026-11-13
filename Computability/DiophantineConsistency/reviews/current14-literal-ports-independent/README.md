# Independent source review of the current14 literal-port assembly

On 2026-11-04 an independent reviewer compared
[`Current14LiteralPorts.lean`](../../research/current14-literal-port-assembly/Current14LiteralPorts.lean)
with the fixed-constant section of [`equation.tex`](../../equation.tex).
The four displayed arithmetic formulas agree with the source definitions:
the base and exponent in `beta`, all four subtractions in `mu`, the extra
`beta` shift and all geometric/marker terms in `omega`, and the three base
powers plus the `2 rho^1005 Phi(1/rho)` term in `K`. The two control blocks
of `phi` have the displayed exponents, factors, and lengths. The equality for
`K` is in the rationals, matching the printed rational intermediate; the
endpoint port itself is the cast of a natural number.

The review traced the referenced selector and rank data to
`WangTiles942TableData.lean` and `WangTiles942Core.lean`. Their stated
selector weight and `physicalPosition_eq_printed` have the shape of the
printed `chi` and rank formulas, and `rank_numerator_nonnegative` addresses
the difference between natural truncated subtraction and the printed floor
numerator. The action cache is connected to the decimal decoder by the
referenced `action_eq_decoder` theorem; the reviewer inspected the table and
decoder definitions at the source level. This is a review of those definitions
and theorem statements, not an independent replay of their whole proofs or
an exhaustive new derivation of the printed tile table.

The assembly proves equality with these Lean definitions and the selected
four endpoint ports. It does not parse TeX, interpret PDF rendering, or by
itself bind the whole displayed polynomial and positive-domain semantics to
the iPRA theorem. The remaining external source-to-display transcription and
the imported sources' build ancestry should not be attributed to this one
assembly theorem. No second Lean build or new kernel check was run as part
of this review; any compiler result is the author's separately recorded run.

Reviewed source SHA-256:
`b19dfc3f5ea1639dcd6003613cd587992d3ab64f707cbe7c9fb61a466092f8b0`.
The reviewed TeX SHA-256 was
`94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635`;
the current PDF SHA-256 was
`23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6`.
The source review is tied to these bytes, not future revisions.
