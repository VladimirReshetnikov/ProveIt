COMPOSED CONTRACTION BOUNDS AND QUADRATIC-TIME CAUCHY TABLES
Research packet for Vladimir Reshetnikov. October 26, 2026 (Pacific).

Read report.pdf; report.tex and sections/ contain the complete article.

RESULTS
* Generic normalized tensor contraction: coefficient 63.8574094711...
  in s/sqrt(log2 s), polynomial space. Exact safe eventual coefficient 64.
* Root degree <= s^(3/5): coefficient 31.9287047356..., safe 32, polynomial space.
* Root degree <= s^(1/12): coefficient 26.9023275131..., safe 27, polynomial space.
* Optional generic cached contraction: time coefficient 38.4844959057...,
  space coefficient 34.2748030050..., safe eventual coefficients 39 and 35.
* Full Cauchy feature-table construction: quadratic rather than cubic ring
  work, using one unit inversion. Recorded identical-output kernel timings
  and all raw samples are in results/benchmark_results.json.

SCOPE
These constants are per normalized tensor wire budget, not per SAT variable.
The mathematical contraction results retain explicitly identified source
interfaces; they are not new formal verification of the original ETH result.
The stronger conditional n/log n targets remain unproved. No smaller global
logarithmic order or end-to-end practical SAT speedup is claimed. The separate
Claude manuscript has unspecified constants and a different reduction/model;
its numerical runtime is not shown to be dominated. The new kernel is exact
in (Z/2^p Z)[U]/(U^2+U+1), not a full tensor or SAT engine.

OFFLINE REPRODUCTION (Python standard library)
  python3 code/run_all.py
This runs all exact checks normally and under python -O, using the bundled
historical reference. Fresh outputs go to reproduced/. The finite parameter
checks are diagnostics; they do not certify practical SAT thresholds.

BENCHMARK
  python3 code/benchmark.py --historical vendor/joint_cauchy.py
All preparation and both complete output tables are timed. The matched
modular baseline shares the arithmetic/cache and isolates prefix reuse.
The historical reference uses exact rational arithmetic, including conversion
to the same output residues. Machine details and every sample are recorded.

PDF
  make pdf
Requires a standard LaTeX distribution with the packages named in report.tex.
The vector benchmark figure is already included. To regenerate it and the
numeric tables from the recorded JSON, additionally install Matplotlib and run:
  python3 code/make_exhibits.py

PROVENANCE
Pinned ProveIt snapshot: 474ddba696a5d385c091c23fb2995f69edd13e00.
The review covers seven first-round and eight second-round research packets, plus the
primary OpenAI and Claude manuscripts. source_manifest.json records immutable
commit and file identities. vendor/joint_cauchy.py is the unmodified historical
prototype from the joint-Cauchy archive; vendor/LICENSE.ProveIt is the pinned
repository MIT No Attribution license. No remote repository changes were made.

FILES
  report.tex, report.pdf, sections/    Complete mathematical article
  code/fast_cauchy.py                 New modular quadratic-work kernel
  code/verify_kernel.py               Exact modular and historical checks
  code/verify_variable_arity.py       Generic polynomial-space certificate
  code/verify_degree_corollaries.py   Degree-sensitive certificates
  code/check_cache_composition.py     Cached time-space certificate
  code/benchmark.py                  Reproducible measurements
  code/run_all.py                     One-command offline checks
  code/make_exhibits.py               Scientific plot and table generator
  results/                           All recorded checks and timing samples
  figures/                           Vector PDF and PNG benchmark figure
  vendor/                            Historical baseline and license
  source_manifest.json               Source pins and hashes
  PROOF_STATUS.json                  Exact scope of each claim
  MANIFEST.sha256                     Checksums of the delivered files
