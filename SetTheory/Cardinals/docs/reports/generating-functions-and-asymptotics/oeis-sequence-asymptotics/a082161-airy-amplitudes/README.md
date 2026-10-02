# A082161 Airy asymptotics: reproducibility package

This self-contained package checks the finite algebra underlying the proposed
forward expansion and its inverse, and reproduces numerical evidence. It does
not certify the analytic proof, an enclosure for the positive amplitude gamma,
or effective finite-index error constants.

The article and its editable LaTeX source are included under `article/`. The
manifest binds all supplied input files; runtime outputs remain separate.

## Article and PDF rebuild

- `article/relaxed-binary-trees.pdf`: the complete 23-page article
- `article/relaxed-binary-trees.tex`: editable standalone LaTeX source
- `article/build_pdf.sh`: local PDF rebuild with no installation or downloads

A TeX distribution with pdfLaTeX and the standard packages used by the source
is needed only to rebuild the PDF. Run:

```sh
bash article/build_pdf.sh
```

The result and compilation logs are written under `output/article/`; supplied
article files are not changed. On minimal read-only TeX images, the script can
create missing format/font-map caches inside that output directory. The
packaged PDF has already been built and visually checked on every page.

PDF binaries can differ in timestamps and document IDs after rebuilding. The
clean release replay checks equal extracted article text and equal rendered
page hashes, rather than treating metadata changes as a content defect.

## Environment

Tested using CPython 3.12.14 and the following installed packages:

- NumPy 2.3.5
- SciPy 1.17.0
- SymPy 1.14.0
- mpmath 1.3.0

Exact version pins are in `requirements.txt`. Install those packages in a local
Python environment if necessary. Replay itself never installs or downloads
anything and makes no network calls. A compatible Python 3.10+ interpreter may
work, but the tested versions above are the reproducibility reference. Do not
run Python with `-O`: these programs use exact assertions and reject optimized
mode explicitly.

All scripts use only the standard library and the four listed packages. They
need no prior workspace, hidden files, parent-project imports, or external data.
The first Airy zero and diagnostics are computed locally by SciPy/mpmath.

## Full advertised replay

From this directory, run:

```sh
python replay.py --max-n 20000
```

This command verifies `SHA256SUMS` before executing **each** of the following
five checks, runs them in separate Python processes, checks their results against
`fixtures/expected.json`, and verifies the manifest again afterward:

1. `exact_recurrence.py`: exact integer/rational triangle-to-d recurrence,
   sequence prefix, squared gauge identities including legal endpoints, and
   the half-line adjacency row-norm/Catalan identity
2. `frozen_quasimode.py`: exact cancellation through epsilon^5 and boundary
   cancellation, plus floating-point spectral diagnostics for N=80,...,2560
3. `coefficients.py --order 8`: exact nonautonomous recurrence cancellation,
   boundary/derivative normalization, and mod-3 grading through epsilon^8;
   five forward logarithmic and relative corrections
4. `inverse_checks.py`: exact inverse cancellation through x^(-1), conversion
   of the first relative coefficients to logarithmic coefficients, the
   Stirling contribution, and 180-digit synthetic-model numerical checks
5. `forward_evidence.py --max-n 20000`: normalized float64 recurrence and
   three-correction amplitude estimates at the stated sample indices

The expected exit status is zero, followed by `Replay passed`. Main results:

- `output/replay_results.json`: status, dependency versions, parameters,
  per-test manifest checks, commands, timings, fixture outcomes, and output hashes
- `output/exact_recurrence.json`
- `output/frozen_quasimode.json`
- `output/coefficients.json`
- `output/inverse_checks.json`
- `output/forward_evidence.json`
- `output/*.stdout.log` and `output/*.stderr.log`

Every generated result is under `output/` by default. Existing runtime result
files there are replaced. To retain separate runs, use an output subdirectory:

```sh
python replay.py --max-n 20000 --output-dir output/run-2
```

For a faster diagnostic, `--max-n 1000` reduces only the floating-point forward
run. It is not a substitute for the advertised 20000 run. Timings depend on the
machine; the forward recurrence performs O(max_n^2) work with O(max_n) storage.

## Individual commands

These are the same five tests executed by replay; all accept `--output`:

```sh
python exact_recurrence.py --output output/exact_recurrence.json
python frozen_quasimode.py --output output/frozen_quasimode.json
python coefficients.py --order 8 --output output/coefficients.json
python inverse_checks.py --output output/inverse_checks.json
python forward_evidence.py --max-n 20000 --output output/forward_evidence.json
```

The replay command is preferred because it also verifies inputs and fixtures.
No outputs are written beside the scripts when using the commands above.
Relative output arguments are resolved from the current working directory;
omitted output arguments default to this package's `output/` directory.

## Meaning of the coefficient-generator order

`--order M` is an arbitrary requested finite integer at least 4. It cancels the
nonautonomous epsilon recurrence through degree M and generates s_2,...,s_M,
profiles G_1,...,G_(M-2), and the forward logarithmic/relative corrections through
n^(-(M-3)/3). It is not a promise of convergence of an infinite expansion.

For example, the stable command referenced by the article is:

```sh
python coefficients.py --order 8 --output output/coefficients.json
```

Higher orders use exactly the same algorithm; there is no hardcoded maximum
order or table of later profile solutions. Runtime and expression size grow
rapidly. The default replay uses order 8; a different finite order can also be
passed to replay with `--order M`.

The profiles are represented as P(x)F(x)+Q(x)F'(x), with
F''=2(x+a)F. The polynomial step solves

    TQ = -Q'''/2 + 4(x+a)Q' + 2Q

by descending degree, using its nonzero diagonal 4d+2. The ratio coefficient
enforces Q(0)=0; the integration constant enforces P(0)+Q'(0)=0. Exact residuals,
boundary conditions, derivative conditions, and mod-3 monomial weights are
checked at every order. Finite amplitude-log coefficients are obtained from
the exact formal ratio equation, not fitted to numerical data. The endpoint
is calculated from the ODE's rational power series. The mod-3 grading makes
the change a=2^(-1/3)z, N=2n land in Q[z].

The first three forward logarithmic outputs must be symbolically equal to:

- L1 = 53 z^2 / 90
- L2 = 44 z / 27
- L3 = 141/140 - 1304 z^3 / 42525

The first sequence values must be
1, 1, 3, 16, 127, 1363, 18628, 311250, 6173791, 142190703.
The order-8 formal run also gives
L4 = -422 z^2/1215 and
L5 = z(717281 z^3-298772235)/344452500.
These later coefficients are formal outputs under the same conditional
forward-asymptotic interpretation.

## Numerical expectations and limitations

The n=20000 float64 run gives approximately:

- raw amplitude: 187.01754328009
- divided by three relative corrections: 166.95063854245
- corrected using three logarithmic corrections: 166.95152887374

Their difference is expected at finite n. Neither is a certified value of
gamma. The fixtures permit an absolute numerical regression tolerance of 1e-7
for the displayed relative-correction estimates; this tolerance is a software
regression check, not a rigorous mathematical error bound. Very large max_n
can exhaust time or suffer endpoint underflow. The script raises an error if
an inspected endpoint becomes zero.

Spectral diagnostics use floating-point eigenvectors and eigenvalues. Their
apparently bounded scaled residuals are sanity checks, not proofs of uniform
bounds. The exact frozen residual only verifies the displayed algebraic
cancellations; it does not prove a norm remainder estimate.

Inverse numerical tests solve a smooth truncated model whose exact root is
chosen in advance. They use the illustrative gamma=166.95063854245. They do not
validate the exact sequence remainder, integer rounding near a threshold,
or a gamma enclosure. Exact symbolic cancellation is checked separately.

## Manifest and clean-copy reproducibility

`SHA256SUMS` covers every packaged input, including scripts, this README,
requirements, fixtures, and any subsequently included article files. Runtime
`output/` and Python cache directories are excluded. Replay rejects missing,
unlisted, modified, or symlinked input files. SHA256 provides integrity checking
against the supplied manifest, not independent authorship/authenticity.

To test relocation, copy this directory without `output/` or `__pycache__/`
into a fresh scratch directory, change into it, and execute the full advertised
replay command. No path changes should be needed.

For maintainers preparing a new input set, the following utility writes only
a candidate manifest beneath output:

```sh
python make_manifest.py --output output/SHA256SUMS.candidate
```

Review it, then deliberately replace the release's `SHA256SUMS` with that
candidate. This is a release-maintenance step, not a mathematical test. Do not
regenerate a manifest merely to bypass an unexplained replay mismatch. Adding
the final article files requires deliberate manifest regeneration and another
clean replay before freezing an archive.
