# First-norm correction:13 positive unknowns,84 operations,degree92

Replace the accepted sphere's auxiliary factor U by
`Uc=U−16*b²*f²*T²*V²*G²*(P−1)`, keeping the equation
`(P*Q)²+Uc²+Z²−3=0`. Either the new or the old equation forces P=1 before
the correction is removed, so the entire positive zero sets coincide with
identity witness maps. No sign property of Uc is assumed.

This new frontier point trades nine operations for four degrees against
13/75/96. It retains the complete current2011 fixed tuple:47,313 raw bytes
and4,230 gzip bytes. The literal graph has49 multiplications,18 additions,
and17 subtractions; all84 rows, all13 coordinates, and all4 ports are live.
The exact degree92 leader has900 terms, with a coefficient1024*beta^42 that
stays nonzero after actual coefficient specialization.

- [Ordinary proof](PROOF.md): complete formula, generic noncircular zero-set
  argument, paid operations, exact factored leader, and proof boundaries.
- [Literal graph](polynomial.json), [finite auditor](audit.py), and
  [certificate](CERTIFICATE.json): exact parent changes, complete formula
  identity and nonidentity, every gate leader, all whole coefficient bytes,
  dependence witnesses, and structural/algebraic corruption controls.
- [Lean leaf](../../Lean/DiophantineConsistency/ThirteenFirstNormCorrection92.lean)
  and [focused checks](../../Lean/DiophantineConsistency/ThirteenFirstNormCorrection92Checks.lean):
  arbitrary integer correction lemma, entire positive-zero equivalence,
  identity maps, and actual external ConZFC endpoint.
- [Author receipt](../../reviews/thirteen-first-norm-correction92-author.md):
  source/object/cache pins, exact fresh commands, prior failure, and scope.

Reproduce the finite audit without changing files:

```sh
python3 Computability/DiophantineConsistency/research/thirteen-first-norm-correction92/audit.py
python3 -O Computability/DiophantineConsistency/research/thirteen-first-norm-correction92/audit.py
```

Both reproduce certificate
`1ee2029bcbb60d378f7f70a547ef6d64bb966e094799a1b4d02ada578e2f05b7`.
Graph SHA-256:
`a214fc19ea776e4e3880e13a7cd92260e76e71588c8c6b391669007a180ab3be`.
Only `--write` regenerates this new packet. No project or incoming Python
program is imported or executed.

The two new Lean leaves passed fresh capped private builds using369
source-authenticated current dependency objects; these cached dependencies
were not rebuilt by this packet. All eight focused axiom reports contain
only propext, Classical.choice, and Quot.sound. Independent review is
pending at this initial freeze. The maintained page is unchanged. No
internal HA/PA/ZFC proof, new machine calibration, or global minimum is
claimed. The accepted parent and fourteen-variable tradeoffs are retained.
