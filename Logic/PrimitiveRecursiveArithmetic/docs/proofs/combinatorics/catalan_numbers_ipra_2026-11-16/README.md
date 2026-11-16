# Catalan numbers in intuitionistic primitive recursive arithmetic

This package develops a constructive, iPRA-oriented proof of a broad set of
claims from:

- <https://en.wikipedia.org/wiki/Catalan_number>
- <https://mathworld.wolfram.com/CatalanNumber.html>

It reuses the checked Catalan identity in Vladimir Reshetnikov's ProveIt
repository at snapshot:

`00bbe871268c453903499fb6afe07519e87d9631`

## Main deliverables

- `catalan_numbers_ipra.pdf` - convenient top-level copy of the complete 39-page research report.
- `paper/catalan_ipra.pdf` - the same compiled report beside its LaTeX sources.
- `paper/*.tex` - complete LaTeX source, split by section.
- `lean/CatalanExecutable.lean` - executable finite specification and small
  checks, with no `sorry`.
- `lean/CatalanProveItBlueprint.lean` - exact ProveIt import and object-language
  target scaffold, with no `sorry` or added axioms.
- `code/verify_catalan.py` - exact independent transcription checks.
- `verification/certificate.json` - machine-readable PASS certificate.
- `reference/claim_map.csv` - source-claim coverage ledger.
- `reference/source_audit.md` - source and repository audit.

## Formal-status warning

The existing ProveIt theorem
`LeanProofs.IPRA.Combinatorics.BinomialIdentities.catalan` is reported as
kernel checked by the repository and was inspected at the snapshot above. The
new Lean files in this package were not compiled because the build environment
contained no Lean installation. They are intentionally scaffolds and
executable specifications, not a claim of completed formal verification.

## Mathematical highlights

The report gives constructive proofs of:

- all principal explicit forms, recurrences, MathWorld sums (8)-(13), the
  terminating hypergeometric identity, and constructive versions of all six
  formula proofs displayed on Wikipedia;
- the main Catalan bijections listed on the pages;
- ordinary and exponential generating functions, Bessel identities, exact
  boundary sums, integrals, and random-walk probabilities;
- prime valuations, parity, the base-five final-digit criterion, and the
  classification of prime Catalan numbers;
- both unit Hankel determinants, the determinant `n+1` starting at `C_2`, and
  uniqueness from the first two determinant sequences;
- ballot, rational, Fuss, super-Catalan, generalized Jonah, and k-fold
  convolution claims;
- an effective leading asymptotic and a rigorous remainder for the first three
  terms printed by MathWorld, plus the decimal-digit ratio.

The few exclusions and three source-page corrections are explicit in
`reference/claim_map.csv`.  In particular, the Coxeter paragraph is audited
with finite counterexamples and corrected type-A formulas.  Remaining exclusions include: specialized
frieze/flexagon conventions, the general Coxeter classification theorem, the
open general combinatorial interpretation of super-Catalan numbers, historical
claims, and graphical complex-plane statements.

## Verification

Run:

```bash
python code/verify_catalan.py
```

The current certificate reports 15 assertion families and 29,220 tested cases.
All core checks use exact integers or `fractions.Fraction`; the asymptotic
calculation is clearly labeled as a high-precision diagnostic.

Build the report with:

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error catalan_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error catalan_ipra.tex
```

See `BUILD.md` for validation commands.
