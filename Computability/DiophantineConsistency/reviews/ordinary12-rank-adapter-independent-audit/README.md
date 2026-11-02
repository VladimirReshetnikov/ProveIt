# Independent audit of the conditional free-J rank adapter

The independent artifact audit actually exited 0; its receipt SHA-256 is
`212fa3881f1dd7e514429c8e6273543e5b25be6d3f6000e780dff16b11774b42`.
A fresh bounded Lean replay in separate temporary paths actually exited 0 in
session 24130. Its full replay and nested free-J receipts are retained here,
with hashes and observed exits in `terminal-observation.json`. The original
saved replay is pinned. The fresh and original adapter source, object and
successful diagnostic log match by hash; all direct Lean inputs are re-queried
and hashed. The two named reports have only the recorded Lean metatheory
axioms, and optimized Python is deliberately rejected.

The exact theorem quantifies arbitrary model elements `q,Y,X,t,R,J` in an
`IΣ₁` ordered-ring model. Its first conclusion `q^4 ∣ t` explicitly assumes
`0 < q`, `q^3 ∣ Y`, and `q^5 ∣ (3+4Y(X+1))t`. The checked proof branch uses
only those hypotheses and the historical `cancel_factor_three` lemma; it
does not use the later Mersenne or `q ∣ 3·2^R` assumptions. A numerical
sanity example satisfies this branch with `3 ∣ q`, so no coprimality premise
is being silently inserted.

The second conclusion `q ∣ 2^R` separately assumes the model-internal
Mersenne equality `q=(2^590069−1)J+1` and `q ∣ 3·2^R`; its checked proof
uses the historical `cancel_three` lemma and the explicit exponent bound.
The combined theorem also assumes internal zero of the free-J literal and
conjoins the independently checked factor-unit result with those conditional
cancellations. Its quantified `q,Y,X,t,R,J` are **not linked** to the graph
valuation or its four ports, and neither divisibility premise nor the
Mersenne equality is derived from the zero hypothesis here. In particular,
the second cancellation's premise is not used to establish the early branch.
Five statement/branch mutations were rejected.

The audit independently recomputed the two historical import roots' 62-module
source-declared closure and checked their snapshot sources, parent objects and
logs. Both replay overlays bind all 62 parent object links and all 558 expected
absent companion paths to the independently audited parent. The nested free-J
source and object match the separately audited free-J result; direct adapter
imports, provider receipt, `Init` and Lean toolchain are pinned and hashed.

This remains a conditional, single-author historical model result, not a
matched full-project replay or a package-transitive/dynamic dependency audit.
It does not establish graph-to-carrier bindings, the divisibility hypotheses,
model evaluation of the actual compact44 port, rank or norm recovery, checker
calibration, consistency equivalence, or an internal iPRA derivation. The
Foundation provider's unobserved outer wrapper exit and between-observation
mutation remain outside its guards.
