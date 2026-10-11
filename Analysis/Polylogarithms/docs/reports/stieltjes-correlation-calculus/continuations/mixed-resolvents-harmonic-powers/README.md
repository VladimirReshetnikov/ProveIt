# Mixed Resolvent Products, Higher Digamma Powers, and Stieltjes Collisions

**Exact identities and normalized finite parts.** Research continuation
for ProveIt, 11 October 2026, version 1.0.

## Read the article

`Mixed_Resolvents_Harmonic_Powers_Stieltjes_Collisions.pdf` is the complete
article. The corresponding `.tex` is a flattened, independently compilable
source. For editing and integration, use `article.tex`, `preamble.tex`,
`references.tex`, and the files in `sections/`.

The source baseline is ProveIt revision
`9035bb0eaaf70f3398711b489733093dcc52e946`.
The main results are:

1. Fourier and Hurwitz transforms of arbitrary finite products of cotangent
   resolvents with independent complex powers, including opposite half-planes.
2. Full local completion at total-exponent resonances, with path-dependent
   uncompleted examples and exact logarithmic moment families.
3. A finite depth-two formula for two opposite logarithmic resolvents at
   every Stieltjes index and argument-derivative order.
4. A terminating harmonic reduction and a normalized antiderivative for
   every digamma power.
5. An explicit fifth finite-part moment, with every ordinary correction,
   a depth-four Laurent coefficient, and a convergent depth-two derivative
   coordinate; plus an exact cancellation of the inherited height-one data.
6. Higher-index Stieltjes collision counterterms for arbitrary ordinary
   derivatives and analytic local weights, without assumptions on gap ratios.
7. Three exact mixed cubic collision anomalies, and a proposed research agenda.

The article includes proofs, convention and branch definitions, source
attribution, numerical evidence, and the remaining open scope.
It does not prove the frozen Gaussian S6 or revised S8 conjecture, establish
arithmetic independence of retained constants, or claim global priority
for every specialization. The finite checks are not proof-assistant
certificates.

## Build

A normal TeX Live installation with pdfLaTeX, Latin Modern, AMS packages,
`microtype`, `xurl`, `hyperref`, `bookmark`, and `fancyhdr` is sufficient.

```sh
python3 build.py
```

This regenerates the flattened source, compiles the modular article three
times, checks for unresolved references and overfull boxes, and writes the
named PDF. To additionally confirm that the flattened source compiles by
itself in an empty temporary directory:

```sh
python3 build.py --check-standalone
```

Alternatively, run `pdflatex` on the flattened `.tex` three times.
No ProveIt checkout, source archives, bibliography server, or network
connection is required.

## Reproduce the computations

The recorded environment is Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0.
Install the two Python dependencies from `requirements.txt` in your
preferred environment.

```sh
python3 run_checks.py
python3 run_checks.py --all
```

The default run performs the exact harmonic compiler and its sixty finite
checks. The full run also executes all numerical diagnostics, including
fifteen independent circle quadratures; runtime depends on the machine.
Individual commands and the meaning of the records are documented in
`verification/README.md`. All scripts are self-contained.

## Package contents

- `sections/`: the article's modular mathematical text.
- `verification/`: exact compiler, independent numerical implementations,
  raw JSON results, and replay records.
- `integration/CLAIM_LEDGER.csv`: source questions, theorem labels, and
  proposed status updates.
- `integration/README.md`: integration recommendations and scope.
- `integration/SOURCE_SNAPSHOT.json`: source revision and SHA-256 hashes.
- `SHA256SUMS`: hashes of every other file in this package.

The source repository was inspected read-only. This package is prepared
for later integration; it does not apply edits to the ProveIt repository.
