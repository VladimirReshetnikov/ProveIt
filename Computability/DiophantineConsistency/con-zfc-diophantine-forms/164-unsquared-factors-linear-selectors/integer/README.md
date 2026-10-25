# Linear binomial radius and mod-four radix: direct Con(ZFC) quartics

All unknowns range **independently over the integers**. Every equation is the
sum of squares of its complete quadratic residual list; every collected
quartic coefficient is provided. The ordinary theorem is that ZFC proves
integer nonsolvability equivalent to Con(ZFC), using the retained C222/ZF/ZFC
finite-refutation calibration. This does not prove either side separately.

## Selected exact endpoints

| Directory | Variables | Rows | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| `integer239` | 239 | 175 | 4 | 12,658 | 6,144 |
| `integer240_balanced` | 240 | 176 | 4 | 5,232 | 4,096 |
| `integer240_sparse` | 240 | 176 | 4 | 4,927 | 7,596 |

Each has maximum residual coefficient 64. The 239-coordinate endpoint
improves variables, rows and support over the incoming Shared Factorial
Error 240-coordinate endpoint, with its same height 6,144. These are
achieved finite profiles, not global minima. The sparse and low-height
240-coordinate alternatives trade support against height.

## Arithmetic changes

The factorial-free source uses F=[2(t+1)]^t at t=16+h², a binomial
B=binom(R+t,t), and an odd-square radix q. We replace R=F² by R=F:
the classical lcm bound lcm(1,...,t)≤4^t implies F>lcm(1,...,t)²,
which is precisely sufficient for the inherited two-sided binomial
prime-power selector lemma. We also replace q=(2z+1)² by q=4z+1.
This permits an initially negative radix but excludes q=0,-1; q=1 is
excluded by an acyclic power/beta argument, and the signed binomial digit
then forces B>0 and q>0. Canonical completeness still supplies odd-square q.

`PROOF.md` and `report_section.tex` give the complete new arithmetic proof,
including elementary lcm proof, signed bootstrap, late y=F exclusion,
label multiplicities, and constructive completeness. `inherited_factorial_free/`
retains the complete 4.1 MB immediate source package, ordinary predecessor
proofs, exact compiler certificates, calibration interfaces and licenses.
The authoritative sharpened selector theorem is its `report/main.tex`,
not the older review note with the weaker factorial-square threshold.

The semantic edits preserve **zero existence**, not every individual
predecessor witness tuple. The subsequent affine projection and row-basis
maps have exact inverses. `RESTORATION.json` restores the **edited source**,
not the original odd-square source. Actual q=stored_q−1, so the correct
restoration is stored_q=4z+2.

## Reproduction (Python standard library, offline)

```sh
python3 -B verify_all.py
python3 -B -O verify_all.py
```

This replays the frozen construction in a fresh temporary destination,
checks source-interface bindings and inherited manifest, checks all
source edits, every restored coordinate and pulled-back row, all forward
and inverse row-basis steps, complete quartic collection, liveness,
metrics and readable exports. Deliberate corruptions must be rejected.
No search heuristic or bounded arithmetic regression is a proof premise.
The inherited package has its own `verify.py` for its full prior replay;
our manifest and interface audit do not pretend to reprove its unbounded
arithmetic or recompile all formal dependencies.

`linear_integer239/240` are exact unoptimized source-edit endpoints;
`mod4_integer240/241` isolate the radix edit with the square radius retained.
`certificates/` contains the selected frozen row operations. Search logs,
unselected search outcomes, and duplicate PDF/PNG quality-control files are
not part of this clean release. The selected equations reconstruct without
rerunning any optimizer. The four semantic-stage controls remain because
they are the exact replay inputs and separate the two arithmetic changes.

For each endpoint: `equation.json` is the literal residual specification,
`expanded_polynomial.json` is the complete collected quartic,
`residuals.txt/.tex` are readable literals, `variables.tsv` lists every
coordinate, and `METRICS.json` contains the exact measured costs.
Historical variable names record provenance, not unchanged semantic values.

No publication, repository commit, or external state change is part of this
component. No global optimality, consistency proof, or fresh end-to-end
Lean/Rocq formalization is claimed.
