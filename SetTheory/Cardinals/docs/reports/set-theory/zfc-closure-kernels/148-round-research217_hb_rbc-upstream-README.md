# Membership fourth inputs together with A, C, truth and falsity

The existing five-value matrix validates **one calculus containing all**
membership-fourth rho8 instances and all four additional families `U=A`,
`U=C`, `U=truth` and `U=F`. Keep native truth, MP, theorem-only GEN,
rho1–rho6, merged G and the full gated C222 bundle. The ordinary
[proof](proof.md) extends the [parent model](../README.md): native-code
recursion and induction on finite derivations prove consistency in PA.
Assuming ZFC is consistent, this enlarged calculus therefore cannot have
consistency provably equivalent to Con(ZFC) in ZFC. This is not a new
proof-assistant theorem or a machine construction.

The single common valuation is essential: the families may be used together
in the same derivation. The result covers arbitrary membership labels and
builders because every membership code has value 2. It does **not** include
`U=B`, K, explosion, or arbitrary other nonmembership fourth inputs.

The [original finite check](results/original.json) evaluates all 125 carrier
triples for each named family. There are no failures for membership, A, C,
truth or F; there are five failures for B. The concrete native input codes
`(A,B,C)=(10,3,10)` realize one B failure. Model failure does not prove
calibration or inconsistency of that remaining proposal.

Opening's [independent review](independent-peer.json) reads the full extension
proof and separately checks its finite table cases. It relies on the
parent packet's retained-row and full-bundle proof, rather than claiming a
new audit of that entire foundation. The proof and original result preserve
their contemporary references to Opening's then-pending three-value model;
that separate [K + RAB + QS obstruction](../../../k218-k-membership-obstruction/README.md)
has since been validated and published. Its comparison rows here are
diagnostics, not the basis of this five-value theorem.

From the repository root, reproduce the cheap extension check with a new
output path:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/finite-matrix/mixed-union/check.py \
  --output /tmp/mixed-fourth-new.json
```

The [portable adapter diff](history/portable.diff) adds input/output arguments,
the exact existing model identity and an expected-result assertion. Its
[publication replay](results/portable-replay.json) has the same result bytes
as the original. Neither invocation runs submitted code. The all-natural
claim follows from the written induction, not from sampling formula codes.

The remaining `R(A,B)` plus `U=B` union has only
[bounded diagnostics](u-b/README.md) here: five rounds of exact constructor
schema search and eight short heuristic matrix searches found neither a
listed generic proof target nor a model. These negatives are not exhaustive
results. No search was repeated for publication.

Attribution: Source 147 supplied the five-value matrix; `root` independently
checked its original rows and extended its membership coverage;
`review_upstream_reflection` proved this mixed-union extension, wrote the
finite comparison check, and adapted Opening's two bounded search programs.
`opening_encoder` independently reviewed this extension. Exact source and
evidence identities are in [publication.json](publication.json).

