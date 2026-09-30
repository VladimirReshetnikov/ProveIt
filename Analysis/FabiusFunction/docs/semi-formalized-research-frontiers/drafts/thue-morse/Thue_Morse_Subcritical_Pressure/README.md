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
- `SHA256SUMS`: checksums of the distributed files other than itself.

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
rewrites the JSON output and table fragments. The full run uses meshes of
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
