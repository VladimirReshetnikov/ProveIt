# Localized Spectral Response and the Full Subcritical Pressure Law

**Moving zeros, a polyhedral cusp, and finite-size scaling for digital products**

Research draft prepared with ChatGPT for Vladimir Reshetnikov, 29 September 2026.

## Main contribution

For the base-b digital mask

    m_b(x) = |sin(pi*b*x) / (b*sin(pi*x))|,

with its removable values, the article proves, for every fixed 0 < s < 1
and 0 < alpha < s,

    P_{b,s}(c) = (1-s)*log(b)
                 + (b-1)*pi*s*tan(pi*s/2)*|c|
                 + O(|c|^(1+s-alpha)).

The pressure uses the unnormalized b-branch transfer operator. It is the
cylinder pressure of the products of m_b(b^j*x-c)^s. In the binary
squared-mask convention, the pressure order is q=s/2.

This closes the interval 0 < s <= 1/2 explicitly left untreated in the
repository's Critical Cusps in Digital-Product Pressure manuscript.
The article also proves an independent-zero extension: for the fixed
leading-coefficient polynomial whose b-1 roots move along the unit circle
by displacements epsilon_j, the first pressure increment is

    pi*s*tan(pi*s/2) * sum_j |epsilon_j|.

The key new estimate is a weak O(delta) bound after pairing the
perturbation with the atomic left eigenfunctional. Combining it with a
strong O(delta^(s-alpha)) bound makes the nonlinear error o(delta)
throughout the subcritical interval. Additional results include a weak
Dirac-plus-principal-value expansion, a sharp total-variation logarithmic
loss, an explicit spectral gap, and a finite-size operator and moment law.

## Contents

- `article.pdf`: the complete research article.
- `article.tex`: standalone main LaTeX source; bibliography is embedded.
- `data/pressure_table.tex`, `data/finite_size_table.tex`: table fragments
  used by the main source.
- `code/verify.py`: reproducible numerical diagnostics.
- `data/verification.json`: complete structured output of the full run.
- `data/run.log`: full console output, including a quadrature warning.
- `requirements.txt`: Python dependencies.
- `SOURCES_AND_CLAIMS.md`: repository provenance and validation boundaries.
- `build.sh`: PDF build command for a POSIX shell.
- The submitted checksum ledger `SHA256SUMS` was verified in full (11/11) on
  filing (batch 54 of `docs/incoming/`) and not kept; the delivered archive
  remains in the repository history (see `docs/incoming/README.md`, batch 54
  row).

## Build the PDF

Use a TeX installation with pdfLaTeX, latexmk, Libertinus, and the standard
packages listed in the source. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The included tables are sufficient: the numerical code does not have to
be run to build the PDF. `sh build.sh` runs the same build.

## Reproduce the diagnostics

Python 3 with NumPy, SciPy, and mpmath is required.

```sh
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python code/verify.py --full
```

On Windows, set the environment variable using the shell's equivalent
syntax, or omit it. A run without `--full` uses smaller meshes. Re-running
writes the JSON output and table fragments to `recomputed/` unless
`--output-dir` is given (editorial amendment below; the delivered script
rewrote `data/` in place). The full run uses meshes of
262144 and 524288 points and is a floating-point diagnostic, not an
interval-arithmetic certificate. Library versions are recorded in JSON.

## Status

The article contains ordinary mathematical proofs, not Lean/Rocq proofs.
No formal-verification claim is made. Numerical evidence is separate from
the proof dependency chain. An adaptive-quadrature roundoff warning is
retained in the output and explained in the article. The claims are local
at the atomic phase and uniform only on compact subintervals of 0<s<1;
global phase regularity and joint endpoint limits are not claimed.
Independent correctness and priority review remain appropriate. No
unverified repository theorem is used as an axiom.

## Editorial amendments (ProveIt, 2026-09-29)

This package was filed whole in batch 54 of the repository-level
`docs/incoming/` drop zone (see `docs/incoming/README.md`) and amended in
the editorial pass that followed.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style, and one
  note follows the paragraph "The present article resolves this exact
  obstruction" (Section 1.1). It says that the article answers the research
  question "The remaining subcritical interval" of
  `../Thue_Morse_Critical_Pressure/` at the atomic phase for every
  `0 < s <= 1/2`, sharpens that article's `o(|c|)` remainder on
  `1/2 < s < 1`, and leaves nonzero phases open; it cites the previously
  uncited bibliography entry `Repo`, and it records the new default output
  directory of `code/verify.py`. Both changes are marked `% ed.` in the
  source. The title's "Full" means the full exponent range `0 < s < 1`; the
  result is local at the atomic phase `c = 0`.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX pdfTeX): 20 pages, as delivered;
  790,192 bytes; no error, undefined reference, rerun request, duplicate
  destination or overfull box; no Type 3 font.
- `code/verify.py`: a new option `--output-dir` (default `recomputed/`
  beside `data/`) replaces the delivered in-place rewrite of `data/`, and
  the script refuses to write into `data/` without `--full`, because a
  default run would replace the two tables that `article.tex` inputs with
  coarser-mesh values (the text states 262,144 and 524,288 points). All
  three outputs are written as UTF-8 with LF line endings (the delivered
  script wrote CRLF on Windows). Changes are marked `# ed.`.
- Rerun on a copy (2026-09-29), `OPENBLAS_NUM_THREADS=1 uv run --no-project
  --python 3.13.5 --with numpy==2.3.5 --with scipy==1.17.0 --with
  mpmath==1.3.0 python code/verify.py --full` (about two minutes): both
  table fragments are byte-identical to the filed `data/` files, and
  `verification.json` differs only in floating-point noise (largest
  relative difference 3e-3, on matrix residuals of size 1e-13; the scaled
  pressure increments agree to 5e-13 relative). The same quadrature warning
  as in `data/run.log` is emitted. `requirements.txt` gives unpinned
  ranges; the tested versions are those recorded in `data/verification.json`.
  Use `py` or `uv run` where bare `python` does not resolve.
- `data/run.log` is the delivered console capture; its second line carries
  the packager's sandbox path.
- `SHA256SUMS`: see Contents (retired on filing).
