# Finite Distribution Modules, Spectral Jets, and Cyclotomic Trace Identities

A research contribution for the ProveIt polylogarithm project, dated 9 October 2026.

The article proves the canonical uniform distribution-rank statement underlying the manuscript's finite experiments, strengthens it to independent polynomial prime weights and all finite jets, and gives explicit coefficient and determinant formulas. It also derives cyclotomic polylogarithm trace identities, supplies an exact proof-search obstruction for the existing S4 conjecture, and proposes corrections to two manuscript discussions.

## Start here

The complete article is `article/distribution_jets.pdf`; its self-contained LaTeX source is `article/distribution_jets.tex`. `RESULTS.md` maps the principal results. `AUDIT.md` distinguishes corrections, strengthened results, and remaining conjectures. The `integration/` directory contains proposed manuscript replacement/addition text, not automatic changes to the repository.

The source baseline is commit `29d9344771b41df39ff9b7890c76b1f152572dde`. Paths and inspected blob hashes are in `provenance.json`. No remote repository writes were performed.

## Mathematical claims

Over a characteristic-zero character splitting field, the finite weighted distribution quotient is free of rank phi(q), for all prime weights, including zero and resonant weights. Fixing the endpoint leaves phi(q)-1 coordinates. The complete order-N jet quotient has dimension (N+1)phi(q). These are formal quotient dimensions, not numerical independence claims.

A conductor-indexed polynomial basis is valid everywhere. The primitive-grid basis has an explicitly factored determinant and computable local jet defects. Rational primitive-grid reductions have exact support and sign rules; negative spectral orders use finite rational continuation, not a divergent infinite series.

The principal primitive level-30 polylogarithm trace has zero value and zero first order derivative at s=1, with second order derivative -2 log(2) log(3) log(5). The article proves general principal and nonprincipal character families.

The S4 evaluation remains conjectural here. An exact eight-entry annihilator proves that its target row is outside the span of the declared 96-row weight-five shuffle/stuffle presentation. This is NOT a disproof of the identity and NOT an obstruction to all functional equations. Its independent integral comparison agrees at 55-digit working precision.

Classical antecedents are credited. In particular, ordinary universal-distribution rank is classical, and the cubic log-gamma formula in Tornheim-Witten derivatives is due to Bailey–Borwein–Borwein. Global novelty, numerical transcendence, proof-assistant verification, and external peer review are not asserted.

## Reproduction

Python 3.10 or later is needed. The executed environment used Python 3.13, SymPy 1.14.0, and mpmath 1.3.0; full version information is in `provenance.json`.

```bash
python -m pip install -r requirements.txt
./test.sh
./build.sh
```

The exact distribution tests and S4 certificate replay need only the standard library:

```bash
python code/verify_exact.py --max-q 60
python code/replay_certificate.py
```

The character and symbolic row generators use SymPy. Numerical diagnostics use mpmath and can be run independently:

```bash
python code/verify_characters.py --max-q 60
python code/verify_s4_presentation.py
python code/verify_numeric.py --group traces --dps 55
python code/verify_numeric.py --group stieltjes --dps 55
python code/verify_numeric.py --group s4 --dps 55
```

`build.sh` requires a LaTeX installation providing pdflatex, amsmath/amsthm, lmodern, geometry, microtype, hyperref, bookmark, etoolbox, fancyhdr, booktabs, and xurl. It runs three passes in a temporary directory and replaces only the local companion PDF. It does not require BibTeX or a bibliography database.

## Verification outputs included

Exact tests were executed for every 2 <= q <= 60: 295 weight-pattern cases and 295 positive/negative integer-order normal-form cases. They check ranks, anchoring, parity, all divisor rows, primitive submatrices, support, signs, and endpoint coefficients. Exact rational character phases verify conductor counts, determinant factors, and central jet-rank profiles over the same range.

The S4 certificate includes all 96 rows, the coordinate legend, target, witness, and law parameters. `replay_certificate.py` independently verifies 96 annihilations, rank 20, augmented rank 21, and target pairing 768 using `fractions.Fraction`.

Numerical JSON files record the actual working precision and residuals. They are floating-point diagnostics, not rigorous interval enclosures. Uniform theorems are proved in the article, not inferred from these finite checks.

A checksum manifest covers the delivered files. Test reruns may change recorded timing fields, and PDF rebuilding may change metadata, so regenerate the manifest after intentional local changes.
