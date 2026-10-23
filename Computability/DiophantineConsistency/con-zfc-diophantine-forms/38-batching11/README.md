# Quadratic batching, index absorption, and smaller consistency equations

This research package supplies explicit integer polynomials whose lack of
solutions is provably equivalent, in ordinary mathematics formalizable in
ZFC, to `Con(ZFC)`. It develops three compatible improvements over ProveIt
at commit **22e75dd6b87b1b199bb08c778d7cf075ae5aae08**:

1. Direct simultaneous testing of 22 quadratic residuals with a finite
   Sidon-position code, avoiding the quartic sum-of-squares positional code.
2. Absorption of an index quotient into an existing norm carrier, followed
   by a short-range Pell-index argument that reconstructs the quotient.
3. Complemented whole-label clauses in the native compiler, reducing the
   four-port coefficient payload by approximately 33%.

Read **report.pdf** for the complete manuscript. Its editable source is
**report.tex** with the files in **sections/**.

## Results

Here N includes zero; positive means strictly positive. Every other named
quantity in a formula is a circuit register, not an additional unknown.

| Form | Unknowns and domain | Equations | Exact degree(s) | Binary operations |
|---|---|---:|---:|---:|
| Quadratic batching | 9 in N | 1 | 166,177,600 | 868 |
| Positive translation | 9 positive | 1 | 166,177,600 | 864 |
| Sun companion | 10 unrestricted integers | 1 | 449,607,016 | 773 |
| Main index absorption | 11 positive | 1 | 1154 | 123 |
| Main system | 11 positive | 2 | 2, 1152 | 119 |
| Main shifted system | 11 positive | 2 | 2, 1152 | 118 |
| Optional translated product | 11 positive | 1 | 1140 | 129 |
| Optional translated system | 11 positive | 2 | 2, 1138 | 125 |
| Optional translated shifted system | 11 positive | 2 | 2, 1138 | 124 |

The operation model charges each binary addition, subtraction and
multiplication, including scalar multiplications and squarings. Shared
registers and fixed coefficient leaves are free. Fixed powers are expanded
into multiplications. This is not a count of all monomials after full expansion.

The nine-variable degree improves the pinned degree
`92324*5^32+296` by a factor of about `1.294e19`. The ten-integer degree
improves `126496*5^31+27064` by about `1.310e18`. The new positive nine-variable
evaluator has 864 operations versus the separate historical 1473-operation
evaluator; the degree-optimized package 37 evaluator had 1500 operations.
The ten-integer evaluator improves 1442 operations to 773.

The eleven-variable family is a new moderate-degree tradeoff. It does not
improve the twelve-positive degree 1022 record or the historical 67-operation
single equation. No claim of a globally minimal number of variables,
globally minimal degree, optimal Sidon set, or first use of Sidon sets
throughout the Diophantine literature is made.

## The exact logical assertion

For each delivered form F on its stated domain D,

    ZFC proves: (there is no x in D with F(x)=0) iff Con(ZFC).

For a system, replace `F(x)=0` by simultaneous satisfaction of both equations.
The proof passes through the inherited calibrated equivalence

    finite syntactic ZFC refutation
    iff literal K215 halts on blank input
    iff the positive quadratic compiler source has a solution.

The new reductions are proved in the manuscript and companion proof files.
The compiler/native/Pell calibration remains an identified inherited
mathematical dependency. The ten-unrestricted-integer form additionally
uses specified results in Sun's 2026 preprint and 2021 paper. The
nine-variable and eleven-positive forms do not use the 2026 preprint.

This package does **not** prove Con(ZFC), search for a refutation, assert
that a finite test proves the unbounded equivalence, or supply a new
end-to-end Lean/Rocq formalization. The work and independent local reviews
are AI-assisted; no independent human review is asserted. Included Lean
files identify source endpoints and require the upstream development to build.

## Coefficients: one active complete tuple

The active native binding is `compiler/COEFFICIENT_BINDING.json`:

    B_native = 2^678139
    beta = B_native - 1
    K0 = K = DC + B_native*DR
    MC = the new current mask
    MF = MF_source = MF_native + B_native - 1

All four ports must be used together. MF is already shifted. The compiler
generator and independent auditor reconstruct all four full integers from
the literal finite data. Their total raw size is 339,476 bytes, down from
506,664 bytes; the largest has 681,374 bits.

The additional source constants are `kappa=2^1359525` for nine variables and
`beta_sun=2^1359528` for ten integers. They are fixed numbers with compressed
binary payloads and exact bounds. The sixteen other derived fixed leaves
have explicit signed recipes and hashes. No enumeration index or
consistency-dependent constant is left unspecified.

Historical parent-source JSON and inherited code are retained byte-exact
with their source notices. **Their old default-binding metadata is inactive.**
Use only this package's active manifests and sibling compiler tuple.

## Reproduce

Python 3.10 or later, standard library only:

```sh
python3 reproduce.py
```

This regenerates and checks all finite artifacts in dependency order and
writes the root `VERIFICATION.json` receipt. It does not need a network
connection or the ProveIt checkout. Individual directories also have
independent builders and checkers.

For the PDF, install a normal TeX distribution with pdflatex, Latin Modern,
amsmath/amsthm/amssymb, mathrsfs, geometry, microtype, booktabs, longtable,
enumitem, fancyhdr and hyperref, then run:

```sh
make pdf
```

`python3 reproduce.py --pdf` runs both. `MANIFEST.sha256` records the
delivered files. Regeneration may update verification receipts; a newly
compiled PDF can differ in metadata while retaining the same content.

## Layout and integration

- `compiler/`: whole-label compiler, literal tile/machine data, full native
  ports, independent audit, rank-controller proof, inherited proof sources.
- `nine/`: literal quadratic parent, Sidon list, kernel recipes, native
  binding, natural and positive circuits, exact cancellation/degree
  certificate, source and signed-bootstrap checks.
- `signed10/`: unrestricted-integer companion, precise Sun interface,
  complete final polynomial, inherited finalizer, finite certificates.
- `eleven/`: main and optional translated equations/systems, full proofs,
  generators, checkers and independent mathematical review.
- `provenance/`: pinned K215 endpoint and literal machine snapshots, source
  URLs and hashes, and a precise statement of what remains inherited.
- `review/`: additional independent local proof review.
- `sections/`, `report.tex`, `report.pdf`: complete manuscript.

A suggested repository destination is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/38-quadratic-batching/`
if that next numbered slot is still available when integrating. Keep the
three arithmetic directories next to `compiler/`; their paths are relative.
No existing repository files were changed by preparation of this archive.

The root license is MIT-0, following the surrounding report family.
Upstream source and machine notices remain in their respective directories.

## Main finite evidence

The receipts distinguish exact identities from diagnostic examples:

- All 528 Sidon pair sums and all 136 source coefficient records verified.
- Nine-variable exact degree certificate keeps every fixed leaf symbolic
  and ends with the nonzero diagonal coefficient `2^196*kappa^83088652`.
- Actual fixed coefficient payload hashes, strict source bounds, and
  literal-formula/circuit/domain-shift agreement verified.
- Eleven-variable independent formal norm products, rational carrier
  identities, positive-domain bounds, parity, and full univariate degree
  calculations verified, including cases with `k<=E`.
- Compiler auditor independently reconstructs the ports and verifies
  66,062 native-basis identities, mask populations, carries, and the
  actual-rank controller residues. The builder additionally checks
  1,157,632 whole-label decoder cases.

These are finite certificates for the data and implementation. The
unbounded arguments are the proofs in the manuscript and the explicitly
identified inherited theorem chain.
