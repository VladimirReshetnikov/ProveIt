# Bring radicals and quintic equations in iPRA

This archive develops a large constructive fragment of the mathematical claims on:

- Wikipedia, **Bring radical**
- Wikipedia, **Quintic equation**
- MathWorld, **Quintic Equation**

The main document is `bring_quintic_ipra.pdf`; its LaTeX source is `bring_quintic_ipra.tex` plus the `chapters/` directory.

## Main results

The report gives fully developed finite or effective arguments for:

- existence and uniqueness of the real Bring radical by exact rational bisection;
- oddness, strict decrease, unboundedness, a sharp 1-Lipschitz estimate, a residual error certificate, differentiability, and an explicit fifth-root asymptotic bound;
- the Lagrange-inversion coefficient formula, hypergeometric form, exact convergence radius, boundary convergence, four branch points, and the trinomial discriminant;
- the Cockle–Harley fourth-order differential resolvent;
- exact depression of a general quintic and a quadratic Tschirnhaus reduction to principal form;
- a primitive-recursive resultant certificate for the universal Bring–Jerrard step, plus the scaling formula for `x^5+p*x+q`;
- the generic Abel–Ruffini obstruction through `S5`, and explicit `S5` certificates for `x^5-x+1` and `x^5+x+3`;
- the de Moivre quintic, MathWorld’s four-resolvent identity, explicit radical/cyclotomic examples, and the `AGL(1,5)` criterion for solvable irreducible quintics;
- the exact quintic obtained from the collinear Lagrange-point equation.

The global Hermite theta-function formula, Klein’s icosahedral continuation, the full published Spearman–Williams substitution, and the universal expanded Bring–Jerrard witness are given precise certificate/formalization interfaces but are not claimed as completed Lean proofs.

## Repository baseline

The report was prepared against:

- `https://github.com/VladimirReshetnikov/ProveIt`
- inspected head: `b73ff58ad10e9c446fa997777c5f502844249929`

It reuses the existing ProveIt architecture for iPRA, the checked factorization identities through quartic degree, the Lagrange-inversion packet, and the Abel–Ruffini packet. The exact checked/unverified boundary is stated in the paper.

## Exact verifier

Run:

```bash
python3 code/verify.py --json certificates/verification_report.json
```

The script requires Python 3 and SymPy. In the generation environment it passed **17/17** independent exact check families, including:

- polynomial SOS, scaling, depression, discriminant, and formal-series identities;
- the differential resolvent;
- de Moivre and four-resolvent cyclotomic products;
- explicit radical and cyclotomic examples;
- finite-field factorizations, Frobenius remainder chains, and discriminants;
- all 156 subgroups of `S5`, the solvable-transitive classification, and derived series;
- the celestial-mechanics denominator clearing;
- exact rational bisection for `BR(3)`.

The script is a certificate/regression checker, not a replacement for the human proof or the intended object-theory Lean derivation.

## Lean status

- `Lean/BringQuinticBlueprint.lean` is an **uncompiled blueprint**.
- `Lean/LEAN_ROADMAP.md` gives the dependency order and completion criteria.
- No new file in this archive is claimed to be kernel-checked.
- The blueprint uses no `sorry`, `admit`, or declared axiom and supplies no inhabitant of its proof-obligation record.

## PDF build

From the archive root:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error bring_quintic_ipra.tex
```

The generated PDF was also rendered page-by-page during validation; see `validation/`.

## File map

- `bring_quintic_ipra.pdf` — main report
- `bring_quintic_ipra.tex`, `chapters/*.tex` — LaTeX source
- `STATEMENT_AUDIT.md` — concise coverage/status map
- `Lean/` — Lean blueprint and completion roadmap
- `code/verify.py` — exact symbolic and finite checker
- `certificates/verification_report.json` — machine-readable check results
- `validation/verification_output.txt` — checker transcript
- `SOURCES.md` — source and reuse notes
- `MANIFEST.sha256` — archive file hashes
