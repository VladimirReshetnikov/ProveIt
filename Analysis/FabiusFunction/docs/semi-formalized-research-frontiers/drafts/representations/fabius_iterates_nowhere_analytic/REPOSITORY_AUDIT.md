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
`StrictMonotonicity.lean` to `Monotonicity.lean`.  The merged report retains
15 nonconjectural labelled manuscript results, two numbered warning
quarantines, and one live conjecture.  Former Conjecture 14.1 is nonexclusive
as submitted: at an `n = 1` interior dyadic point, the eventually-zero Taylor
polynomial also has positive radius without representing the function locally.
No replacement zero-radius/eventually-zero classification is asserted.

Former Conjecture 14.2 is also not live.  The manuscript's exact tie
proposition identifies the tied orbit points as `1/4` or `3/4` followed by
`5/72` or `67/72`; along `m = 6ℓ + 4`, the earlier spine vanishes and the later
one has amplitude exactly `Up(1/9) ≥ 1/2`.  The finite-spine expansion then
gives a full-derivative lower bound with constant `A_(k+1,n)/4` and zero Taylor
radius at every tie point.  The exact Lean anchors are
`fabius_deriv_quarter`, `deriv_fabiusReal_one_sub`, `fabiusReal_quarter`, and
`fabiusReal_three_quarters`; the tie proposition, finite-spine argument, and
iterate conclusion remain manuscript proofs.

The exact positive-list arithmetic of the partition defect--including its
pairwise and triangular forms, zero-defect classification, sharp fixed-block
minimum, equality profile, and first positive shell--is formalized in
`PartitionDefect.lean`.  The module has three public definitions and thirty-
three public theorems, exhaustively crosswalked in the TeX.  It does not supply
the bridge from finite set partitions, the quadratic-scale factorization,
weighted-defect decay, two-spine reduction, finite-spine expansion,
orbit-weight analysis, analytic conclusion, or the positive-iterate theorem
for `n >= 2`.

## Final merged-document validation

The final TeX was frozen at 1,566 lines and 63,630 bytes with SHA-256
`e46584803c86359e977f404ea4d9b7f515c5579cf392f10d87f2ceaeb8b3c835`.
Starting from clean auxiliary state, exactly three strict serial `pdflatex`
passes produced a 22-page, 785,347-byte A4 PDF with SHA-256
`eed9b151ab43ba846e9d6d945a4e815d0ed11b9ecf530cee27711c26fb11bcf6`.
The final log has no warning, TeX error, unresolved reference or citation,
rerun request, duplicate destination, or overfull/underfull box.  All 22 font
rows are embedded and subset Type 1 fonts, five are Libertinus, and none is
Type 3 or Latin Modern.  Every page has extractable text and A4/zero-rotation
geometry.  All 22 rendered pages were visually inspected, including the
status boundary, exhaustive Lean crosswalk, exact tie proposition, warning
quarantines, sole live conjecture, numerical figures, and source map.

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
