# From finite presentations to explicit witnesses in iPRA

Research package prepared for Vladimir Reshetnikov, 15 November 2026.

Read **ipra_presentations_to_witnesses.pdf** for the complete human arguments.
The LaTeX entry point is **paper.tex**, with included files in **paper/**.
The source audit is pinned to ProveIt commit
`b0f6f535ffc16324683fef2c263260a88ae03755`.

## Main results

1. **Proof-preserving finite simulation.** A local object-iPRA derivation of
   `h(f(x)) = g(h(x))` gives a derivation through every finite iteration.
   A second theorem handles any explicitly quantifier-free binary relation.
   Repeated-squaring transport is a concrete application.
2. **Complete rational enumeration from finite action data.** A checked
   unit-and-multiplication certificate gives rational matrices `M_k`.
   For `A_k = Delta_k M_k` integral and `R_k` its maximum absolute column
   sum, every rational zero has coordinate `z_k / Delta_k`, `|z_k| <= R_k`.
   Exhaustive exact filtering of the finite grid gives the complete list.
   No basis independence or matrix commutativity is required.
3. **Certificate production.** Separated monic annihilator identities give
   rectangular monomial certificates by an explicit finite constructor.
   A nonzero norm for a monic plane equation and a section also constructs
   a finite action certificate, or an explicit inconsistency identity.
4. **Complete section lists.** Nonzero polynomial norms give a separate
   rational-root/fiber enumeration algorithm, an explicit height bound,
   and composition with supplied global finite section covers.

These strengthen the existing finite-algebra and norm **counting**
interfaces. They do not infer height bounds from arbitrary count bounds,
produce unknown global covers, or prove general Siegel, Faltings,
Mordell–Weil, or the unresolved analytic prime-distribution estimates.
A full-coordinate polynomial certificate requires a finite-dimensional
quotient algebra; finiteness of the rational point set alone is insufficient.

## Proof status

| Component | Status |
|---|---|
| New algebraic, norm, constructor and finite-cover arguments | Complete human proofs, with explicit PR operations and QF invariant audit |
| Fusion, relational simulation, squaring transport, successor instance | Compiled Lean results concluding the actual `Prf PRAAx` judgment |
| Integer eigenvalue integrality and column bound | Compiled host Lean theorems |
| Full rational enumeration | Complete human proof; fully defined Lean programs and exact remaining targets |
| Complete `Prf PRAAx` enumeration derivation | Not completed; dependency-by-dependency path is supplied |
| Reference Python calculations | Exact finite implementation checks, not a formal arithmetic proof checker |

The Lean build is standalone and uses verbatim bodies of three pinned
ConciseIPRA modules after import-only adaptation. The full repository was
not rebuilt. See **lean/README.md** and **lean/FORMALIZATION.md** for the
precise boundaries, axiom audit, integration route and upstream provenance.
The new modules contain no custom axioms, opaque placeholders or `sorry`.

## Contents

| Path | Purpose |
|---|---|
| `paper.tex`, `paper/` | Complete editable LaTeX source |
| `ipra_presentations_to_witnesses.pdf` | Compiled research paper |
| `python/certified_points.py` | Sparse rational polynomial checker and complete grid enumeration |
| `python/verify_points.py` | Independent known-solution examples, rejection checks and grid checks |
| `python/annihilator_code.py` | General separated-annihilator certificate constructor and checks |
| `python/norm_intersections.py` | Norm/fiber enumeration, norm-to-module constructor and checks |
| `examples/` | Exact JSON certificates for the featured examples |
| `lean/` | Compiled source modules, complete targets, proof plan and pinned upstream sources |
| `provenance/` | Source audit and source identities |
| `validation/` | Actual arithmetic runs, mathematical reviews, PDF build and layout checks |
| `SHA256SUMS.txt` | SHA-256 checksums for the delivered files |

## Reproduce

Python needs only the standard library:

```sh
python3 python/verify_points.py
python3 python/annihilator_code.py
python3 python/norm_intersections.py validation/norm_checks.json
python3 python/certified_points.py examples/elliptic_section.json
```

The first three commands record their results under `validation/`.
The last prints the grid data and complete four-point solution list.

Build the paper with a TeX Live installation, `latexmk`, and standard
AMS/Latin Modern packages:

```sh
bash build_pdf.sh
```

The script includes a local format/font-map fallback for a minimal Debian
TeX installation. Temporary outputs go to `.build/`.

For Lean, use version 4.32.0:

```sh
bash lean/build.sh
python3 lean/verify_provenance.py
```

If the executable is not named `lean` on your path, set `LEAN_BIN` to its
absolute location. The build only needs Lean's standard library and writes
its `.olean` files under `lean/.build/`.

## Key worked example

For `F1 = 4y^2 - 4x^3 + x - 4` and `F2 = 2x^2 - x`, the basis
`(1,x,y,xy)` has `Delta = (2,1)` and `R = (2,1)`. Fifteen grid candidates
give exactly `(0,±1)` and `(1/2,±1)`. Both Python and Lean independently
evaluate this example. The paper lists every nonzero residual identity.

The programs also check a deliberately redundant certificate with
noncommuting matrices and a localization that removes an infinite component.

## Source and licensing

The bundled upstream Lean sources retain the original ProveIt license in
`lean/LICENSE-ProveIt.txt`. The new prose and code were prepared for this
request. External literature is cited for context; the new human proofs
do not require access to it to follow the argument.
