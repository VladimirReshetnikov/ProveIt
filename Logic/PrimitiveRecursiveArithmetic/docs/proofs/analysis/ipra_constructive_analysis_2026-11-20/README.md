# Finite queries in constructive analysis

Start with **report.pdf**. The LaTeX entry point is **report.tex**. It includes six source sections and two vector figures.

The first three sections construct and analyze finite bit-query programs. They derive the least prefix for a finite observation, check dyadic overlaps, convert to and from ordinary regular interval names, and compute integral and extremal values from the same terminal rows. A graph version glues interval charts at their endpoints. Section 4 treats approximate intermediate values and gives a multivalued root algorithm for monic polynomials with named real coefficients. Section 5 gives an entropy-order-optimal catalog for the bounded Lipschitz class on a cube of fixed dimension. Section 6 records the remaining object-iPRA formalization obligations and further research questions.

## Verification status

- `object/ObjectReplay.lean` generates genuine ProveIt judgments of the form `Γ ⊢[PRAAx] φ` for fixed decision trees. Its closed example and two-input replay theorem were kernel-checked against the pinned ProveIt sources.
- `lean/` contains twelve checked host Lean modules, including the exact least-prefix algorithm, sparse carry test, depth-denominator integration identity, numerical interval lift, monic finite-difference bound and ternary rounding/encoding. The host statements quantify over Lean data and functions. Their object-language counterparts are identified in the report.
- The complete interval representation theorem, Riemann and graph interpretation, polynomial root algorithm and entropy bounds have human proofs. The report identifies the bridge lemmas still needed to obtain complete object-iPRA derivations. In particular, the host cell-geometry and binary-prefix libraries still need a formal identification of the concrete rational bit reader with their cell labels.
- `code/` contains the exact-rational reference implementation and independent finite validation. `verification/` records the toolchain, checks, and immutable GitHub source paths.

## Reproduce

Run these commands from the extracted directory. The numerical checks use only Python's standard library.

~~~sh
./check_examples.sh
~~~

Rebuild the PDF with a usual TeX Live installation.

~~~sh
latexmk -pdf -halt-on-error report.tex
~~~

The plotted PDFs are included. To regenerate them, use Python with Matplotlib and NumPy and run `python3 figures/make_figures.py`.

The standard-library Lean modules can be replayed with a Lean 4.32.0 executable on the path. The script also accepts the absolute path to the compiler in the environment variable LEAN.

~~~sh
./lean/check-core.sh
~~~

The additional Lean checks require the existing ProveIt Lake workspace and its Mathlib dependencies. The inspected revision is **b2341af5370cd8a43f72ebb2341c0d7d7395b634** of VladimirReshetnikov/ProveIt, with Mathlib revision **81a5d257c8e410db227a6665ed08f64fea08e997**. From a checkout of that revision with its Lake dependencies set up, the following script builds the required imports and checks the three Mathlib modules and the object proof generator. If the Mathlib cache is not present, run `lake exe cache get` in the checkout first.

~~~sh
./check_proveit.sh /absolute/path/to/ProveIt
~~~

The checksums cover all archive members except the checksum list itself. From the extracted directory, run `sha256sum -c SHA256SUMS`.
