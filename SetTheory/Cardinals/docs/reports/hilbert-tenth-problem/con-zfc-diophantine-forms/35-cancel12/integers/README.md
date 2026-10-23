# Compact sixteen- and seventeen-integer consistency polynomials

This component specifies two ordinary fixed-integer-coefficient polynomials.
Their lack of unrestricted-integer solutions is provably equivalent in ZFC
to Con(ZFC), by the ordinary proofs in `signed_section.tex` and the explicitly
identified upstream compiler and Jones theorems. No new end-to-end Lean/Rocq
certificate or consistency proof is claimed.

| Artifact | Integer variables | Equations | Exact degree | Binary operations |
|---|---:|---:|---|---:|
| `generated/signed16.json` | 16 | 1 | `813056*5^32+10024` | 1865 |
| `generated/signed17.json` | 17 | 1 | `406528*5^32+27512` | 1874 |

All arithmetic nodes are binary addition, subtraction, or multiplication.
Squaring and multiplication by constants are charged; shared results are
reused freely. Coefficient construction is outside the variable-evaluation
count. Intermediate named nodes are abbreviations, not extra unknowns.

## Reproduce

From any working directory, run `python3 path/to/integers/build_signed.py`.
Only Python's standard library is required. Run without `python -O`, which
would disable the diagnostic assertions. The program reads the frozen source
files under `upstream/` and all four raw coefficient files in
`../coefficients/`. It writes only its own `generated/` directory.

The complete four-port binding is `../coefficients/COEFFICIENT_BINDING.json`;
`MF_source` is the shifted high mask. Never splice ports from different
bindings. `generated/INDEX_CONSTANTS.json` defines all 402 weighted quartic
coefficients, the index `z=2^4269855`, the unused semantic index `y`, and the
new fixed radix scale `b_scale=2^(4269856*(5^32+1))`. Those are fixed integers,
not quantified variables. The sixteen-integer circuit has no `y_index` leaf.

The new idea sets the Jones coding base to `b=b_scale*radix_root^2` and merges
`radix_root != 0` into the existing divisibility/nonvanishing condition.
This makes the old epsilon guard unnecessary. Completeness is preserved
because the source coding construction works at every sufficiently large
power-of-two base, including the required parity class of exponents.
The new signed separator uses `Cstar` itself in place of `1+Cstar^2`.
The full source-use audit and reconstruction order appear in the TeX section.

`SOURCE_PINS.json` records exact SHA-256 and Git blob identifiers for all
upstream files at ProveIt revision
`8c6eec9d19ef80538c8e61ff6e0180040583446a`. Upstream programs are included as
reference text and are never executed by this generator.

The generated check receipts contain an exact leading-term degree certificate,
actual-coefficient modular comparisons, independent norm calculations in a
free radical algebra allowing negative radicands, source-expression checks,
and finite diagnostics for the elementary lemmas. These checks support the
definitions; the mathematical proofs supply the unbounded equivalence.

For use in a differently arranged archive, keep this directory's files
together, place the authenticated upstream tree at `upstream/`, and put the
four binary coefficient files in the sibling `coefficients/` directory.
