# Unit sphere: 13 positive unknowns, 75 operations, degree 96

The equation is `(PQ)^2+U^2+Z^2-3=0`, with the same complete factors,
thirteen positive coordinates and four current2011 coefficients as the
accepted shared76 equation. The integer three-square lemma forces each
factor square to equal one. Existing negative-unit exclusions then force
`PQ=U=Z=1`, recovering exactly the accepted positive zero set, by identity
witness maps in both directions. The new polynomial is different from its
parent; no polynomial-equality claim is used.

The complete literal graph uses42 multiplications,18 additions and15
subtractions. Degree remains exactly96, with the same135-term highest
homogeneous form. Whole coefficient sizes remain47,313 raw and4,230 gzip
bytes. This improves the operation count at unchanged degree and domain;
it makes no global minimality claim.

- [Ordinary proof](PROOF.md): full formula, entire positive-zero equivalence,
  sign sequencing, operation changes and degree calculation.
- [Complete graph](polynomial.json): all75 live paid binary operations.
- [Finite auditor](audit.py) and [certificate](CERTIFICATE.json): all69
  unchanged rows, exact new graph/formula identity and difference from
  parent, complete all-gate leaders and whole coefficients, actual
  dependence/nonidentity witnesses and corruption controls.
- [Lean proof](../../Lean/DiophantineConsistency/ThirteenUnitSphere96.lean)
  and [checks](../../Lean/DiophantineConsistency/ThirteenUnitSphere96Checks.lean):
  genuine integer sphere lemma, calibrated signs, entire positive-zero
  equivalence and actual external `DiophantineConsistency.ConZFC` endpoint.
- [Author receipt](../../reviews/thirteen-unit-sphere96-author.md): exact
  sources, cache inventory, fresh private commands, logs and axiom reports.

Reproduce the deterministic finite receipt without changing files:

```sh
python3 Computability/DiophantineConsistency/research/thirteen-unit-sphere96/audit.py
python3 -O Computability/DiophantineConsistency/research/thirteen-unit-sphere96/audit.py
```

Both pass with certificate SHA-256
`fd8c02774985bb3b8fef11294a3d9dc8198312b6fc38228a5f651c4d05fd4acc`.
Auditor SHA-256:
`a459434a804f13d0aabd4dbd2fe53bd19846163e4e396076b72c1a01c6e669d0`.
Graph SHA-256:
`48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1`.
Only `--write` regenerates this new packet. No project or incoming program
is imported or executed by the auditor.

Both new Lean leaves passed capped fresh private builds, with thirteen
standard-only axiom reports. The authenticated451-object cache is reused,
not rebuilt; the package and transitive dependency boundary remains
explicit in the receipt. The graph/degree audit is separate from Lean's
zero-set theorem. The maintained display is unchanged. No internal HA,
PA or ZFC derivation is claimed. Independent review is pending at the
initial freeze.
