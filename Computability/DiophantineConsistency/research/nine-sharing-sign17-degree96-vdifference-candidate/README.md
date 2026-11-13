# 17-witness degree-96 conditional signed-elimination candidate

This external candidate removes coordinate 18 and the sign18 residual
`V2minusY2 = v18 - ((v13+1)^2 - v17^2)`. Coordinates 0 through 17 retain
their old numbers; input coordinate 0 remains fixed at one, and the 17 natural
witnesses are coordinates 1 through 17. Substitute the integer expression
`D = (v13+1)^2 - v17^2` for the removed coordinate in the eight remaining
residuals. The candidate remains a sum of their squares.

The replacement is signed, so its natural-valued lift needs a hypothesis and
an argument. Let `F = v13+1`. The retained Na residual has exactly the form
`F² - S²*D - 1`, with `S=(v6+1)*R*(R+2)`. Here `R` is the **unshifted**
root expression produced by the preceding elimination, not `R+1`. It is a
sum of natural-valued terms including `beta*(v1+1)`, so `beta>0` implies
`R≥1`, hence `S≥1`, for natural coordinates. If the retained Na residual is
zero and `D<0`, then `F²=1+S²*D≤0`, contradicting `F≥1`. Thus `D≥0`, and a
natural lift can be represented by the natural difference `F² - v17²`.
Conversely, an old zero has `v18=D` by the deleted residual. This argument uses
the retained Na equation, so it is not circular with the deleted residual.
It is an ordinary arithmetic argument for positive beta, **not** a Lean proof
of the desired model bridge or internal iPRA equivalence. If `S=0`, the bare
Na implication can fail (e.g. F=1, V=2); no beta=0 claim is made.

The checker validates the exact Na/S/root AST shapes, the nonnegative syntax
of R and its beta summand, every substituted residual, and the unchanged port
binding. Every residual has syntactic degree at most 48. Set coordinates
1–16 to t and coordinate 17 to 0; Na does not use input 0, and its coefficient
of t^48 is `-16*beta^28` in `Z[t,beta]`. The fixed-port sum of squares has
t^96 coefficient at least `256*beta^56` and therefore exact external degree
96 when beta is nonzero. The retained beta bytes decode as positive and all
four port gzip/raw hashes are checked. These are not Lean/JSON/port-byte
binding theorems. Finite controls do not establish model or iPRA claims.

Run `python3 -I -S -B build.py --check` and `python3 -I -S -B check.py` from
this directory. The author checker exited 0 and wrote `result.json`. Source
sign18 seed SHA-256:
`d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb`;
new seed SHA-256:
`0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac`;
builder SHA-256:
`9e7b63bb18b776864348b161f144839212c5c8c34948c96764b535a5129915c6`;
checker SHA-256:
`a78dca4d46b28e1fc07e920d2737666891d5ceba87c01899e559516881b12584`;
result SHA-256:
`7011c7e00102c665a1b06e9c927c9ad94ccbc39d102d37959375cad1862f8a6a`.
Independent review is requested.

The [independent external audit](../../reviews/nine-sharing-sign17-external-independent/README.md)
passed; the candidate packet is frozen. The audit does not establish a Lean
model bridge or iPRA endpoint.
