# How often can two products of Dirichlet L-functions agree locally?

The paper gives sharp maximum agreement densities for all sizes and ranks for characters of orders dividing 3 and 5, an equality criterion for every odd prime order, and separate sharp results for primitive characters of a common conductor.

## Contents

- `odd_order_euler_factors.pdf` is the 13-page paper.
- `odd_order_euler_factors.tex` is its self-contained LaTeX source, including references.
- `verify.py` computes exact projection histograms, extremal examples and prime counts using Python's standard library. Python 3.10 or later is recommended.
- `checks.json` is the recorded output.

## Reproduce

Run these commands in the extracted directory.

```sh
pdflatex -interaction=nonstopmode -halt-on-error odd_order_euler_factors.tex
pdflatex -interaction=nonstopmode -halt-on-error odd_order_euler_factors.tex
python3 verify.py > reproduced.json
cmp checks.json reproduced.json
```

The first two commands use a standard LaTeX installation with Latin Modern. The finite checks use no network or external data. The ten unrestricted enumerations account for 220,813,980 unordered pairs. Eight additional enumerations check the primitive cubic formula, and twelve explicit primitive constructions test its odd-prime large-size analogue. The two arithmetic examples check every reduced residue class of moduli 13981 and 1247.

## Repository snapshot

ProveIt commit `2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6` supplies the article and the vendored Lean statements. The vendored readable edition matches the upstream `grh/` tree at commit `72fead102f663d5c7a407964a13dc0cf9d977207`. Clickable pinned references are in the paper. Section 6 applies the supplied Dirichlet GRH theorem. The finite geometry, density theorems and computations are independent of GRH. The new results are written proofs, and the upstream kernel checks were not rerun in making this archive.
