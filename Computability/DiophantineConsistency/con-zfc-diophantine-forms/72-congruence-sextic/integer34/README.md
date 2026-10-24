# A 34-integer sextic for syntactic ZFC consistency

The new polynomial is the sum of squares of the 19 literal residuals in
`sextic34.json`. Its 34 variables range over **all integers**. The four
coefficient ports are fully bound to the included authentic source34
payloads; they are not unknowns. Its exact total degree is six.

The proof in `PROOF_SEXTIC34.md` establishes an explicit integer-polynomial
bijection between its zeros and those of package64's Q41. Composed with
that construction's named native/Pell/refutation calibration, ordinary
mathematics formalizable in ZFC proves that absence of zeros is equivalent
to Con(ZFC). No new end-to-end proof-assistant or object-language ZFC
certificate is claimed.

This improves the inspected wave-nine 35-integer sextic by one variable
and one residual (20 to 19). It is a concrete finite-catalogue improvement,
not a global minimum or a major breakthrough in Diophantine representation.

The mechanism is a degree-aware use of a retained square register.
Keeping `F2=f^2`, eliminate `V=fo-c` and replace the otherwise quartic
expression `(fo-c)^2` by the cubic `F2*o^2-2foc+c^2`. The difference is
exactly `o^2*(F2-f^2)`, a multiple of a retained equation. Two simultaneous
triangular root shifts allow seven total register eliminations while
leaving every residual cubic or quadratic.

## Reproduction

Python 3 standard library suffices, without network access:

```
python3 build_sextic34.py
python3 verify_sextic34.py
```

Both programs also work with `python3 -O`; acceptance uses explicit
exceptions, not removable assertions. The first checks exact polynomial
restoration identities and writes the polynomial. The second independently
checks the readable formulas, authenticates all retained upstream files,
reconstructs all four million-bit coefficient numerals from the literal
943-tile list, and emits the exact 368-term symbolic-port expansion.
These are finite algebraic and data checks, not an unbounded consistency
test.

The `tau,D` variable names denote new coordinates; the old roots restore
as `tau_old=tau+E(c-eta)` and `D_old=D+ac`. This distinction is required
when comparing tuples or transplanting the equation into another source.

## Files

- `sextic34.json`: the fixed polynomial specification, variable/domain
  declaration, full restorations and row-operation ledger.
- `sextic34_expanded.json`: exact expansion with the four fixed numerals
  kept symbolic; its binding is the same complete coefficient tuple.
- `PROOF_SEXTIC34.md`: full new proof and the 19 readable residuals.
- `build_sextic34.py`, `verify_sextic34.py`: finite replay programs.
- `SEXTIC34_CHECKS.json`, `SEXTIC34_VERIFICATION.json`: verification receipts.
- `coefficients/`: four actual compressed integer payloads.
- `upstream/`: unchanged source polynomial, named inherited proofs,
  coefficient-generation input and exact polynomial-arithmetic helper.
- `UPSTREAM_FILES.json`: pinned source paths, Git blob hashes and SHA-256.
- `licenses/`: retained upstream licensing and attribution.

The research snapshot is ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`, including packages 60-67.
This contribution makes no changes to the repository's checked baseline.
