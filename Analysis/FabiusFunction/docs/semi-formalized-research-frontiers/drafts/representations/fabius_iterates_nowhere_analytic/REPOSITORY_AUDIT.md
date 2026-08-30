# Repository audit

This note records checks performed by the ProveIt repository after the quick
archival intake.  It is not part of the submitted report and does not promote
any manuscript result to Lean-proved status.

The claim-level review was made against repository commit
`7235ec2926f735ae2cde1a3c26766e93b0457716`.  It found no fatal mathematical
gap, but it repaired three points of exposition in the TeX source:

- the weighted partition-defect argument now gives a uniform exponential
  estimate, rather than only an asymptotic comparison of logarithms;
- the two-spine lemma assumes that the outer function is smooth near its
  evaluation point `h(x)`, not near `x`;
- the finite tie set is indexed so that the empty case `n = 1` is literal.

The source map was also corrected from the nonexistent
`StrictMonotonicity.lean` to `Monotonicity.lean`.  At that intake checkpoint,
three direct `pdflatex` passes rebuilt the 19-page PDF without warnings,
overfull boxes, or unresolved references, and every rebuilt page was rendered
and visually inspected.

A later source-only repository normalization replaced the bespoke preamble by
the primary exposition's canonical A4, 27 mm, Libertinus preamble, corrected
the PDF author metadata to match the title-page attribution, and removed an
unsupported claim of symbolic verification.  It also moved the two
quarantined statements into warning environments.  The report now contains 14
nonconjectural labelled manuscript results, one live conjecture, and two
explicit quarantine warnings.  The proposed Taylor-series trichotomy is
nonexclusive at an `n = 1` interior dyadic point unless its third class
excludes eventually-zero polynomial series.  The former tie-cancellation
conjecture follows at manuscript level from the canonical quarter-point facts
and the report's binary-transition lemma, so it is no longer presented as
open.  The positive-iterate theorem for `n >= 2`, its finite-spine machinery,
and its partition estimates remain to be formalized in Lean.

The normalized source was then rebuilt from this directory with exactly these
three serial passes:

```text
pdflatex -interaction=nonstopmode -halt-on-error fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_iterates_nowhere_analytic.tex
```

The resulting 20-page PDF is A4, has embedded and subset Libertinus prose fonts
and no Type 3 font, and has no overfull box, unresolved reference, rerun request,
or TeX error.  The title/status page, contents continuation, both quarantine
warnings, and final reference page were rendered and inspected.  Generated
`.aux`, `.log`, `.out`, and `.toc` files were removed after that audit.

## Exact numerical replay

The submitted numerical parameters through order 22 were replayed in an
isolated environment.  The repaired command also names the synchronized figure
directory explicitly:

```text
MPLBACKEND=Agg python numerical_experiments.py \
  --output-dir numerical_output --figure-dir figures \
  --x0 0.437123456789 --iterate-count 4 --max-order 22
```

Before repository newline normalization, all six submitted generated files
reproduced byte-for-byte under:

- Ubuntu 22.04.5 LTS, x86_64, glibc 2.35;
- uv 0.11.6 and CPython 3.12.13;
- `MPLBACKEND=Agg`;
- contourpy 1.3.3, cycler 0.12.1, fonttools 4.63.0,
  kiwisolver 1.5.1, Matplotlib 3.10.8, NumPy 2.3.5, packaging 26.3,
  Pillow 12.3.0, pyparsing 3.3.2, python-dateutil 2.9.0.post0,
  SciPy 1.16.3, and six 1.17.0.

The tracked generated artifacts currently have these SHA-256 values:

| Generated file | SHA-256 |
| --- | --- |
| `fabius_iterates.png` | `133f853875a46795bcc515b4e4be81d43e45d344a7287fafe59457007f8616f2` |
| `numerical_metadata.txt` | `a96520afbceb02c0bd3700cc31a8dcd702e282e56cbcae1fa70217ccb4b5710d` |
| `spine_comparison.png` | `1ab5e26247c83d7f8dbb55a6140b663854a5f79991157ce071ab88294587027b` |
| `spine_diagnostic.csv` | `cc314e0241f53f328637f6a2f0aa3b074a790e4ee28e94e8e6598df4d7721635` |
| `spine_remainder.png` | `f9492cf024a6547964cc45e3715842cfe47200befd434687fd5f610833e9bca1` |
| `taylor_root_diagnostic.png` | `972c21aa3852d11210c347714cae9837a977b7ee8c0f1bb81c262447fc40358a` |

The four copies under `figures/` have the same hashes as their
`numerical_output/` counterparts.

The submitted CSV used CRLF records and had SHA-256
`4143d2f9dc5c466dc387758d160be2782f6b6f24c6cc668141c6b6e9fb8b905a`.
Repository normalization changed only those record terminators, producing the
tracked LF hash `cc314e0241f53f328637f6a2f0aa3b074a790e4ee28e94e8e6598df4d7721635`.
The script now gives `csv.DictWriter` an explicit `lineterminator="\n"`, so
future output uses LF independently of host defaults.  This source-only repair
did not overwrite the tracked outputs; a fresh pinned replay is a separate
integration check.

This is strong provenance evidence for the delivered figures and table; it is
not proof of the asymptotic theorem.  The diagnostics stop at order 22 and
construct the full derivative and spine approximation from the same numerical
Fabius atlas.

## Figure synchronization and reproducibility limitations

The submitted README gives no platform record or dependency lock.  Using the
same top-level versions on Windows and CPython 3.12.13 reproduced all rows and
scientifically stable values, but not all bytes.  The largest non-near-zero
relative derivative drift was about `1.45e-8`, and an analytically zero
order-two residual rounded to zero rather than about `1.13e-16`, changing the
semilog remainder plot's scale.  Exact byte reproduction therefore depends on
the Linux platform and full transitive environment above.

The repaired script writes the four PNGs to `numerical_output/` and then copies
them byte-for-byte into the requested `--figure-dir` (normally `figures/`).
TeX reads the latter directory.  The explicit synchronization step removes the
possibility that a numerical replay silently leaves the embedded figures
stale.

The remaining limitations are:

- `taylor_root_diagnostic.png` is synchronized into both directories as a
  supplementary diagnostic but is not included by TeX;
- only `up(0)` and `F(1/2)` are tolerance-checked in code; the other three
  printed anchor values are diagnostic records, not enforced assertions;
- CSV field `relative_gap` uses
  `|D-S| / max(|D|, |S|)`, whereas the paper's table and remainder plot use
  `|D-S| / (Q_m H_n^m)`;
- the floating-point/FFT replay is neither a computer-algebra certificate nor
  independent symbolic verification of the manuscript proof.

These are documentation and reproducibility debts, not evidence against the
reported finite-order computations.
