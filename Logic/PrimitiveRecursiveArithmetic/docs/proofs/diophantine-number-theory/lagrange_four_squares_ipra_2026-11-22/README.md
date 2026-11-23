# Lagrange's four-square theorem in intuitionistic PRA

**The mathematical proof is complete. The supplied Lean sources are an
uncompiled formalization outline, with explicit remaining obligations.**

This packet constructs four primitive recursive functions `W0,...,W3` and gives
a fully developed proof, using intuitionistic logic and quantifier-free
induction, that their squares sum to the input. In particular,

```text
iPRA proves: forall n, exists a,b,c,d <= n, n = a*a+b*b+c*c+d*d.
```

The proof uses a bounded modular seed for primes, exact parity halving for even
multipliers, centered-residue Euler descent for odd multipliers, a fixed `p`-step
prime loop, and a fixed `n`-step trial-factor loop. No unbounded minimization,
induction on an existential representation predicate, or classical choice is
needed. Signed integer and tuple notation is explicitly reduced to primitive
recursive natural coding in the report's appendix.

## Start here

- `report.pdf`: the complete mathematical report, including the logical audit.
- `report.tex` and `sections/*.tex`: editable LaTeX sources.
- `code/four_squares.py`: an exact-integer reference implementation.
- `code/validate.py`: reproducible symbolic and finite checks.
- `validation/results.json`: actual recorded test scope and results.
- `validation/prime_traces.json`: worked prime-descent traces.
- `lean/FourSquares.lean`: total program definitions, invariant/rank definitions,
  and conditional correctness assembly from six named arithmetic contracts.
- `lean/ProveItTarget.lean`: the exact closed object-language sentence, a
  witnessed object goal, and a proposed Euler-identity fragment.
- `lean/OBLIGATIONS.md`: the 31-step formalization ledger.
- `references/proveit/`: pinned source references and provenance, not a portable
  dependency closure.
- `validation/proof_audit.txt` and `validation/code_review.txt`: independent
  proof and implementation review notes with their original scope.
- `SHA256SUMS`: hashes of the distributed packet files other than this manifest.

## Reproduce the computation

The constructor needs only Python 3.10 or newer and its standard library:

```bash
python3 code/four_squares.py 2026
python3 code/four_squares.py 31 --prime-trace
python3 code/four_squares.py 128 --literal-clock
```

For symbolic validation, install the optional validation dependency in your
preferred Python environment and run:

```bash
python3 -m pip install -r requirements-validation.txt
python3 code/validate.py
```

Validation was run with Python 3.12.14 and SymPy 1.14.0. It checked Euler and
halving identities by symbolic expansion; all 19,992 signed descent states for
primes at most 13; all inputs 0 through 1,000; all 168 primes at most 1,000;
literal-clock agreement on the stated smaller ranges; and selected larger
examples. These checks corroborate the code. They are not a proof of the
universal theorem and are not Lean compilation.

The default program skips already absorbing iterations. `--literal-clock`
executes the prescribed loop counts. The mathematical proof uses those fixed
counts, with quantifier-free norm and rank invariants.

## Rebuild the PDF

Run `make pdf` from this directory with a standard TeX Live installation and
`pdflatex`. This runs two LaTeX passes for references and the table of contents.
The package requires standard AMS, Latin Modern, geometry, microtype, listings,
hyperref, bookmark, booktabs, enumitem, and fancyhdr packages.

## Lean status and completion path

No Lean compiler was available in the producing environment. **Neither Lean file
was elaborated, compiled, or kernel checked.** `ArithmeticContracts` has no
asserted instance, so `lagrange_from_contracts` is explicitly conditional. The
local arithmetic proofs, natural-code correspondence, and complete `PRAAx`
derivation remain to be implemented and checked.

`FourSquares.lean` can be attempted in a Lean 4 environment without Mathlib.
`ProveItTarget.lean` requires the full ProveIt root workspace pinned below.
`lean/README.md` explains the two formalization layers. A host Lean theorem
about `Nat` does not by itself establish derivability in iPRA.

## Sources and provenance

The ProveIt review uses commit
`3a521d0265941f9e9d4ad450818365a78a6c9a73`, inspected November 22, 2026.
The root toolchain specifies Lean `v4.32.0`. Individual Git blob hashes, exact
paths, URLs and SHA-256 hashes appear in the source manifest. Copied sources
retain the repository's MIT-0 license; they are source references only. The
packet does not claim to have independently recompiled upstream modules.

Mathlib's existing `Nat.sum_four_squares` was inspected for comparison; it is
not a premise of the constructive iPRA proof. The report cites the source and
explains this distinction.

No remote repository was modified while preparing this packet.
