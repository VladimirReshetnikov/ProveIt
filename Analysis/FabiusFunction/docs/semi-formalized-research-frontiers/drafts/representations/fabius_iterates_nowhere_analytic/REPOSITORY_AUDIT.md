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
`StrictMonotonicity.lean` to `Monotonicity.lean`.  A second proof pass raises
the revised report to 15 nonconjectural labelled manuscript results and leaves
two conjecture environments.  After those edits, three direct `pdflatex`
passes rebuilt the 20-page PDF without warnings, overfull boxes, or unresolved
references.  Every rebuilt page was rendered and visually inspected.  The exhaustive
Taylor-series alternatives are now stated disjointly: the positive-radius
class explicitly requires infinitely many nonzero coefficients, while the
genuine conjecture is the zero-radius/eventually-zero dichotomy.  The former
tie-cancellation conjecture is now a proved manuscript proposition.  At a tie,
the earlier maximal orbit point is `1/4` or `3/4`, its successor is `5/72` or
`67/72`, and along the explicit orders `m = 6ℓ + 4` the earlier spine vanishes
while the later one has amplitude exactly `Up(1/9) ≥ 1/2`.  The finite-spine
expansion then gives the full derivative lower bound with constant
`A_(k+1,n)/4` and zero Taylor radius at every tie point.  The supporting exact
Lean anchors are `fabius_deriv_quarter`, `deriv_fabiusReal_one_sub`,
`fabiusReal_quarter`, and `fabiusReal_three_quarters`; the tie proposition and
its finite-spine conclusion are manuscript proofs, not Lean proofs.  The
positive-iterate theorem for `n >= 2`, the quadratic-scale factorization,
weighted-defect decay, two-spine reduction, finite-spine expansion,
orbit-weight analysis, and analytic conclusion remain to be formalized in
Lean.  The exact arithmetic of the partition defect--including its pairwise
and triangular forms, zero-defect classification, sharp fixed-block minimum,
equality profile, and first positive shell--is now formalized in
`PartitionDefect.lean` for arbitrary positive block-size lists.  A bridge from
finite set partitions to those lists is not yet present.

## Exact numerical replay

The submitted numerical command through order 22 was replayed in an isolated
environment:

```text
python numerical_experiments.py --output-dir numerical_output \
  --x0 0.437123456789 --iterate-count 4 --max-order 22
```

All six generated files reproduced byte-for-byte under:

- Ubuntu 22.04.5 LTS, x86_64, glibc 2.35;
- uv 0.11.6 and CPython 3.12.13;
- `MPLBACKEND=Agg`;
- contourpy 1.3.3, cycler 0.12.1, fonttools 4.63.0,
  kiwisolver 1.5.1, Matplotlib 3.10.8, NumPy 2.3.5, packaging 26.3,
  Pillow 12.3.0, pyparsing 3.3.2, python-dateutil 2.9.0.post0,
  SciPy 1.16.3, and six 1.17.0.

The exact reproduced SHA-256 values are:

| Generated file | SHA-256 |
| --- | --- |
| `fabius_iterates.png` | `133f853875a46795bcc515b4e4be81d43e45d344a7287fafe59457007f8616f2` |
| `numerical_metadata.txt` | `a96520afbceb02c0bd3700cc31a8dcd702e282e56cbcae1fa70217ccb4b5710d` |
| `spine_comparison.png` | `1ab5e26247c83d7f8dbb55a6140b663854a5f79991157ce071ab88294587027b` |
| `spine_diagnostic.csv` | `4143d2f9dc5c466dc387758d160be2782f6b6f24c6cc668141c6b6e9fb8b905a` |
| `spine_remainder.png` | `f9492cf024a6547964cc45e3715842cfe47200befd434687fd5f610833e9bca1` |
| `taylor_root_diagnostic.png` | `972c21aa3852d11210c347714cae9837a977b7ee8c0f1bb81c262447fc40358a` |

The four copies under `figures/` have the same hashes as their
`numerical_output/` counterparts.

This is strong provenance evidence for the delivered figures and table; it is
not proof of the asymptotic theorem.  The diagnostics stop at order 22 and
construct the full derivative and spine approximation from the same numerical
Fabius atlas.

## Reproducibility limitations

The submitted README gives no platform record or dependency lock.  Using the
same top-level versions on Windows and CPython 3.12.13 reproduced all rows and
scientifically stable values, but not all bytes.  The largest non-near-zero
relative derivative drift was about `1.45e-8`, and an analytically zero
order-two residual rounded to zero rather than about `1.13e-16`, changing the
semilog remainder plot's scale.  Exact byte reproduction therefore depends on
the Linux platform and full transitive environment above.

Other limitations retained from the submitted experiment are:

- the script writes figures only to `numerical_output/`, whereas TeX reads
  `figures/`; there is no synchronization step;
- `taylor_root_diagnostic.png` is delivered twice but is not included by TeX;
- only `up(0)` and `F(1/2)` are tolerance-checked in code, despite the README's
  broader description of anchor checks;
- CSV field `relative_gap` uses
  `|D-S| / max(|D|, |S|)`, whereas the paper's table and remainder plot use
  `|D-S| / (Q_m H_n^m)`.

These are documentation and reproducibility debts, not evidence against the
reported finite-order computations.
