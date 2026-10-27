# Two further first-norm corrections: 13/92/90 and 13/97/88

This packet adds two operation/degree tradeoffs with the same thirteen
positive unknowns and the complete current2011 coefficient tuple. Both
replace U by `U-A*(P-1)` in the accepted sphere
`(P*Q)^2+U^2+Z^2-3=0`. Either sphere zero independently forces P=1, so the
entire positive solution sets agree with identity witness maps. No sign
assumption is made about the corrected auxiliary.

| Graph | Multiplications | Additions | Subtractions | Total | Exact degree |
|---|---:|---:|---:|---:|---:|
| [polynomial90.json](polynomial90.json) |55|19|18|92|90|
| [polynomial88.json](polynomial88.json) |59|19|19|97|88|

Each graph retains all thirteen coordinates and four ports as genuine
polynomial dependencies, checked at the actual whole coefficients. The
fixed tuple is unchanged:47,313 raw bytes and4,230 gzip bytes, with MF
shifted by beta exactly once. The maintained page and all accepted parent
packets remain unchanged.

- [Ordinary proof](PROOF.md): complete formulas, noncircular zero-set proof,
  identity witnesses, fully paid schedules and exact-degree argument.
- [Finite auditor](audit.py) and [certificate](CERTIFICATE.json): all rows,
  complete cut-polynomial identities, all gate leaders, actual whole ports,
  arithmetic/structural corruption controls and dependence witnesses.
- [Lean leaf](../../Lean/DiophantineConsistency/ThirteenSecondFirstNormCorrections.lean)
  and [checks](../../Lean/DiophantineConsistency/ThirteenSecondFirstNormCorrectionsChecks.lean):
  coefficient refactoring, ring-map/evaluation identities, both entire
  positive-zero equivalences and the actual external ConZFC endpoints.
  Boolean false selects92/90; true selects97/88.
- [Author replay receipt](../../reviews/thirteen-second-first-norm-corrections-author.md):
  exact source/object/cache pins, commands, first failed attempt and scope.

Reproduce the deterministic finite audit without changing files:

```sh
python3 Computability/DiophantineConsistency/research/thirteen-second-first-norm-corrections/audit.py
python3 -O Computability/DiophantineConsistency/research/thirteen-second-first-norm-corrections/audit.py
```

Both reproduce certificate
`b05205f7a5e40dcddf78d77fd6a170a79c4e0df45c3ba23c9bc8b68c3f44d3e5`.
Only `--write` materializes this new packet. The auditor is stdlib-only and
executes no imported project or incoming program.

The exact degree90/88 leaders have639/7,112 terms. Their selected coefficients
are1024*beta^40 and1024*beta^38, with no other symbolic-port contribution to
the selected unknown monomials. The certificate records all gate leaders
and the complete auxiliary leaders; it does not expand either whole
polynomial. Actual all-ones positive inputs give old/new90/new88 outputs
330734/361093/576772 modulo1000003, explicitly distinguishing polynomial
identity from the proved zero-set equivalences.

Both new Lean leaves passed fresh bounded private builds with ten
standard-only axiom reports. They reuse370 authenticated current dependency
objects, including the root's freshly checked84/92 leaf; those prerequisites
were not rebuilt by this packet. Independent review is pending at this
initial freeze. No internal HA/PA/ZFC derivation, new machine calibration,
minimum-size claim or display change is made. The user's internal HA goal
remains separate and active.
