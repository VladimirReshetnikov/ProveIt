# Quantum mechanics in intuitionistic primitive recursive arithmetic

Open `quantum_ipra.pdf` for the report. The LaTeX entry point is `quantum_ipra.tex`. All files loaded by `\input` are alongside it.

The treatment concerns nonrelativistic, separable quantum mechanics with explicitly presented data. It develops finite states, instruments, entanglement, enriched infinite-dimensional Hilbert and trace-class presentations, the continuous spectral calculus, both directions of a quantitative Stone theorem, a Fourier model of a particle on the line, identical particles, and finite-dimensional Lindblad dynamics. Sharp spectral cuts and the domain inputs for unbounded operations receive separate treatment. The closing section lists the five checked iPRA sentences and a module-by-module path for the handwritten analytic proofs.

## Reproduce the calculations

Both programs require only Python 3 and its standard library. Their arithmetic uses integers or fractions throughout.

```sh
python3 code/examples.py
python3 code/band_evolution.py
python3 code/band_evolution.py --time 1/2 --coupling 1/4 --bits 18
```

The second program certifies a probability in an infinite anharmonic ladder. It prints outward-rounded probability bounds, the finite cutoff and the Taylor degree. `examples-output.txt` records the default outputs.

## Rebuild the article

Run `latexmk -pdf -interaction=nonstopmode -halt-on-error quantum_ipra.tex` from this directory, or run `pdflatex` three times. A standard TeX Live distribution with Latin Modern, AMS-LaTeX, titlesec, booktabs, hyperref and the packages in the preamble suffices.

## Replay the Lean checks

Use a checkout of [ProveIt at 84192061db7eb09e923bd4ded5199f23d30c6e83](https://github.com/VladimirReshetnikov/ProveIt/tree/84192061db7eb09e923bd4ded5199f23d30c6e83) and its pinned Lean 4.32.0 toolchain and Lake dependencies. From the extracted archive run the script with the path to the checkout.

```sh
sh check-lean.sh /absolute/path/to/ProveIt
```

`QuantumNames.lean` implements object formulas for regular vector names and their equality. `QuantumIdentities.lean` gives the Hadamard, spinor and Lagrange identities. `BornStability.lean` proves the roundoff bound for one complex amplitude. `ResolventTail.lean` proves the denominator-cleared geometric bound by object induction. The five closed results have type `[] ⊢[PRAAx] φ`. `lean-check.txt` records the checks. `provider-hashes.json` records the Git blob identifiers of the ProveIt source modules rebuilt for verification. The supplied Lean files contain no placeholders. The Hilbert-space, spectral, Stone, Fourier and Lindblad theorems have handwritten proofs and a Lean implementation plan.
