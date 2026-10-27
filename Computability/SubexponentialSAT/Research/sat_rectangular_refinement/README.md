# Certified contraction refinements for 3-SAT

Research prepared for Vladimir Reshetnikov, 26 October 2026 (Pacific time).

## Outcome

The completed result improves the explicit coefficient in a generic exact
contraction bound used by the reviewed 3-SAT algorithms. It does **not** improve
the logarithmic order for unrestricted 3-SAT.

All coefficients below multiply
s / sqrt(ceil(log2(s))) in a base-two exponent, where s is the normalized
wire budget, not the number of SAT variables. A fixed polynomial factor in
the input description length and a lower-order exponent are suppressed.

| Construction | Time coefficient | Space coefficient |
| --- | ---: | ---: |
| Strongest reviewed incoming time point | 29.81160894538347… | 29.81160894538347… |
| New triple certificate; same old backend and schedule | 29.77681894508374699… | 29.77681894508374699… |
| New backend, certificates, and fully charged schedule | 28.43373937834166914… | 28.30578003029975687… |
| Safe eventual bounds for the last row | **28.434** | **28.306** |

The independent incoming point 30.2570356115 / 25.9890677187 remains
preferable when its smaller memory exponent matters. No universal
time-space domination or practical speed claim is made.

The report states the inherited analytic interface explicitly and proves the
new finite certificate, arithmetic transfer, and recursive accounting.
The larger improvement imports the characteristic-zero rectangular
matrix-multiplication theorem at
<https://arxiv.org/html/2610.10494v2>. The same-backend result does not.

The general 3-SAT exponent order remains
n log(log(n)) / sqrt(log(n)); at fixed clause density it remains
n / sqrt(log(n)). The paper explains why the reported per-wire constants
are not universal per-variable constants and why no comparison with the
unspecified constants of the independent Anthropic algorithm follows.

## Read first

- **report.pdf**: complete paper, proofs, comparisons, and limitations.
- **report.tex** and **sections/**: complete editable LaTeX source.
- **CLAIMS.json**: explicit proof and dependency status.
- **data/certificate.json**: literal plans, weights, rational schedule, and
  expected exact coefficients.
- **results/**: delivered exact certificate outputs and finite experiments.
- **provenance/**: pinned sources, review inventory, incoming audit, and
  independent audit notes.

## Reproduce the finite certificates

Use Python 3.10 or newer. The core checks require only its standard library.

~~~sh
python3 code/verify_manifest.py
python3 code/run_checks.py
~~~

The second command reconstructs all support vectors from the literal ordered
plans. It evaluates the complete 84 * 72^3 = 31,352,832 root triples for
each backend, checks the later menus, and verifies all rational schedule
gates and rigorous coefficient intervals. It also runs an independent
reconstruction of the new coefficients and the supplementary quadratic
certificate. Each runs normally and under Python's optimized mode;
acceptance checks remain active in both modes. Negative controls test
malformed plans, omitted input/output costs, a false 28.43 time bound, and
an invalid logarithm gate.

Fresh outputs go to **replay_results/**; delivered outputs remain unchanged.
These are finite certificate checks, not an end-to-end implementation of
the SAT contractor, the analytic identities, or the asymptotic matrix
algorithms. Expect the exact enumeration to take a few minutes, depending
on the machine.

## Reproduce the operator experiments

The optional operator probe requires NumPy in the selected Python environment:

~~~sh
python3 code/run_checks.py --full
~~~

This additionally reconstructs the actual Appendix B crossing operators
modulo 1000003, checks their sum for h = 1,...,6, and checks the central
piece's row and column ranks for h = 1,...,8. It uses all partition labels.
It establishes finite modular facts only: it does not prove a new
asymptotic rank bound or a statement about every binary-label submatrix.
The scripts never install packages or access the network.

## Rebuild the paper

Use a conventional TeX installation providing pdflatex, Latin Modern,
AMS packages, mathtools, booktabs, geometry, microtype, xcolor,
enumitem, xurl, hyperref, and fancyhdr:

~~~sh
python3 code/build_report.py
~~~

This invokes pdflatex three times with shell escape disabled, writes
**replay_build/report.pdf**, and checks the log for unresolved references and
overfull boxes. PDF byte-for-byte reproducibility is not promised because
TeX engines may add timestamps and identifiers.

## Source snapshot and closing check

The main review is frozen at ProveIt commit
8e76d515063c4b9fbd8743a846b457e3a01bc039: 29 indexed packets plus five
new incoming archives. The Anthropic development is inspected at the exact
requested commit 1a6eee293b9e00cb432eef6018a21f523623a9af.

During completion, commit 324f3d9b009ab0323f33be65cd6577867c9c4338
filed the five incoming archives into the project. All 213 placed files
match the reviewed ZIP members by Git blob identity; no mathematical
change was found. The closing observed main revision is
0cf10036e6ad732c27f13e6058f4acd9b3d78415.
Full review depth and source identities are recorded in **provenance/**.

The exact-commit upstream Anthropic CI acceptance was observed; the Lean
development was not rebuilt locally. Neither its verification status nor
the OpenAI formalization's status is claimed for this report.

No remote repository was modified. The archive omits upstream papers,
large intermediate data, and local build byproducts. **SHA256SUMS** identifies
the delivered files.
