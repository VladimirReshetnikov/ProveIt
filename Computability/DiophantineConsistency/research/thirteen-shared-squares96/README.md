# Shared residual: 13 positive unknowns, 76 operations, degree 96

The graph evaluates exactly the same polynomial as the accepted
[grouped77 equation](../thirteen-grouped-squares96/README.md), with one fewer
subtraction. Set `h=f²−1` once, use `Delta*h` in the auxiliary factor, and use
`h−Delta*(b*i*c²)²` as the strong residual. All thirteen coordinates and all
four current2011 integer coefficients stay identical.

The complete count is 42 multiplications, 18 additions, and 16 subtractions.
The exact degree is 96. The four coefficients occupy 47,313 raw bytes and
4,230 compressed bytes. This is an operation reduction at unchanged degree
and coefficient size; it makes no global minimality claim.

- [Ordinary proof](PROOF.md): full formula, exact ring identity, identity
  witness maps, literal four-row to three-row replacement, and degree proof.
- [Complete graph](polynomial.json): all 76 live binary operations.
- [Finite auditor](audit.py) and [certificate](CERTIFICATE.json): all 73
  unchanged rows, complete polynomial identity, every gate leader, all four
  whole coefficients, actual dependence witnesses, and corruption controls.
- [Lean identity](../../Lean/DiophantineConsistency/ThirteenSharedSquares96.lean)
  and [focused checks](../../Lean/DiophantineConsistency/ThirteenSharedSquares96Checks.lean):
  arbitrary-commutative-ring equality, multivariate-polynomial equality, and
  inherited actual external `DiophantineConsistency.ConZFC` endpoint.
- [Author receipt](../../reviews/thirteen-shared-squares96-author.md): exact
  source/object/cache pins, private commands, finite logs, and axiom reports.

Reproduce the deterministic finite receipt without changing files:

```sh
python3 Computability/DiophantineConsistency/research/thirteen-shared-squares96/audit.py
python3 -O Computability/DiophantineConsistency/research/thirteen-shared-squares96/audit.py
```

Both pass with certificate SHA-256
`08029f80ca848fe0519c4ddbc8736285e3ae3ed17b39e2e06cc5ea9bc138990e`.
The auditor SHA-256 is
`d36462014abc8f28ee9bd8242fb56e2d1edb458c7b029dcbea15df2d75b32359`;
the graph SHA-256 is
`3de1d43a810e694cb2f87fb15330e1decc6f5944c2302a18088cb8d3cfd15b36`.
Only `--write` regenerates this new packet. No project program or incoming
code is imported or executed by the auditor.

Both Lean leaves passed their first fresh `-M6000 -j1 -DElab.async=false`
builds, with eleven standard-only axiom reports. The replay reuses 447
source/object-authenticated root prerequisites plus the two accepted fresh
grouped-square leaves; it is not a new transitive closure validation. The
operation/degree audit is separate from Lean's polynomial-identity theorem.
The current display is unchanged. No internal HA, PA, or ZFC derivation is
claimed; independent review of this packet is pending at initial freeze.
