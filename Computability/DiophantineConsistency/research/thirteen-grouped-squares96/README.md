# Grouped squares: 13 positive unknowns, 77 operations, degree 96

The equation is

\[
(PQ-1)^2+(U-1)^2+(Z-1)^2=0,
\]

where `P,Q,U,Z` are the exact factors of the accepted
[normalized mixed-carrier72 equation](../thirteen-lv-carrier122/README.md).
It has the same entire positive integer zero set, with every coordinate
unchanged. Compared with that parent, five additional operations lower the
degree from 124 to 96. The four current2011 coefficients remain exactly
47,313 raw bytes (4,230 compressed bytes). The maintained one-page display is
unchanged.

- [Ordinary proof](PROOF.md): full formulas, both identity witness maps,
  operation count, leading homogeneous forms, and scope.
- [Complete literal graph](polynomial.json): all 77 paid operations, with no
  hidden square operation or additional unknown.
- [Finite auditor](audit.py) and [certificate](CERTIFICATE.json): whole graph,
  formal tail identities, all gate leaders, exact degree, whole coefficient
  reconstruction, dependence witnesses, and corruption controls.
- [Lean proof](../../Lean/DiophantineConsistency/ThirteenGroupedSquares96.lean)
  and [focused checks](../../Lean/DiophantineConsistency/ThirteenGroupedSquares96Checks.lean):
  complete positive zero-set equivalence and the actual external
  `DiophantineConsistency.ConZFC` endpoint.
- [Author replay receipt](../../reviews/thirteen-grouped-squares96-author.md):
  exact sources, private objects, commands, cache boundary, and axiom reports.

The retained 69-row prefix computes `PQ`, `U`, and `Z`. The new eight-row
tail computes their three residuals, squares each, and adds them. Counts are
42 multiplications, 18 additions, and 17 subtractions. The residual-square
degrees are 80, 96, and 72. The degree-96 leading form has 135 terms, and its
coefficient of `J^48*eta^8*s^12*w^8*f^12*T^8` is `256*beta^48>0`.

Reproduce the finite receipt without writing:

```sh
python3 Computability/DiophantineConsistency/research/thirteen-grouped-squares96/audit.py
python3 -O Computability/DiophantineConsistency/research/thirteen-grouped-squares96/audit.py
```

Both commands pass with certificate SHA-256
`9f224ce9b83e9f2900238131df536e9b0034bb0daf5a65adbabb0c72357ea923`.
The auditor is SHA-256
`2b656fd647f284edceb22068748c08020b6a5bab4ef0af0469104f0be8795801`;
the complete graph is SHA-256
`05710557a8029ebdb378a6ac156f25e79b848eb10e673c01008acb415fc3e39d`.
`--write` regenerates only this packet's graph, coefficient copies, and
certificate. No project or incoming program is imported or executed.

Both new Lean leaves freshly compile under `-M6000 -j1 -DElab.async=false`.
All nine printed axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. This leaf replay reuses the accepted frozen LV parent
objects; it is not a new transitive source-closure validation. The finite
degree check is separate from Lean's zero-set proof. Neither result claims
an internal HA/PA/ZFC consistency equivalence or a global minimum. Independent
review is pending at this packet's initial freeze.
