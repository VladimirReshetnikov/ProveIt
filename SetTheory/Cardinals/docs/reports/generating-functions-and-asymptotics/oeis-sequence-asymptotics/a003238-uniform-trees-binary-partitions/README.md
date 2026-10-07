Report215
Uniform rooted trees and binary partitions
4 October 2026

Contents and main result
------------------------
Report215.pdf is the self-contained mathematical report; Report215.tex is its
editable source. Neither A003238(n+1)/A018819(n) nor A003318(n+1)/A000123(n)
converges. The computer-assisted proof uses a full exact 2^24-coefficient sieve,
a positive operator with every analytic tail bounded, and positive Abelian
averaging. A separate proof gives all fixed inverse-logarithmic coefficient
and summatory expansions, and relative inverse estimates.

The two numerical intervals in the nonconvergence certificate constrain one
hypothetical common constant. They are not actual profile-value enclosures,
and their gap itself is not claimed as an oscillation bound. A separate
midpoint/operator corollary proves actual profile oscillation greater than
0.00001839189788 and the same lower bound for each sequence ratio's
limit-superior minus limit-inferior; its extra argument and portable exact
checker are included.

Erdos and Loxton (1979) already proved periodic leading summatory asymptotics
and binary-prefix approximations, and explicitly asked the summatory ratio
question on page 328. SOURCES.txt records the bounded source comparison.
No worldwide priority claim is made.

Requirements
------------
Python 3.8 or newer, standard library only, for all mathematical computations.
The complete PDF/ZIP replay also needs pdftex, pdflatex, kpsewhich, and the
usual LaTeX packages used by Report215.tex, with Latin Modern fonts. The
reference build used pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian).
The runner creates a private format and explicit font map, so it does not
need a writable user TeX configuration directory. No network is used.

Allow at least 2 GiB available memory. The radial step used roughly 1.6 GiB
and took about 140 seconds in development; the operator step took about
90 seconds. Times are estimates. Do not run two heavy replays concurrently.

Full normal replay
------------------
From this directory, run:

  python3 -B reproduce.py --out /absolute/new/normal-output

The output must be a new directory outside the source directory, with an
existing parent. The runner checks the source/receipt/PDF manifest, makes
an isolated copy, freshly runs the full arithmetic once, checks every
receipt, runs lightweight tests in both normal and optimized modes, and
rebuilds the PDF and ZIP. The original package is not modified.

Full optimized replay
---------------------
After the normal replay finishes, run:

  python3 -B -O reproduce.py --out /absolute/new/optimized-output

The full heavy certificate executes once in the selected outer mode.
Lightweight guard and finite-algebra checks execute in both modes within
each full replay. The same semantic receipts are required in both modes.

To compare the actual complete archive as well as every member, add:

  --reference-zip /absolute/path/Report215-reproducibility.zip

The new output contains Report215/ with the rebuilt public package,
Report215-reproducibility.zip, reproduction.json, and local logs. Only the
package and ZIP are distributable deliverables; logs are excluded from the
archive. PDF and complete ZIP byte equality require the same TeX/font
toolchain. Python mathematical receipts have no elapsed-time, memory-use,
absolute-path, or optimization-mode metadata.

Direct arithmetic replay
------------------------
For a direct replay use a separate copy if you wish to retain the supplied
receipts. In code/, run in this order:

  python3 -B certify_global_bound.py
  python3 -B operator_constants.py
  python3 -B certify_radial_values.py
  python3 -B certify_operator.py
  python3 -B combine_certificate.py

The full runner additionally executes verify_finite_models.py,
verify_exact.py, verify_saddle_engine.py, verify_arithmetic.py,
test_certificate_guards.py, verify_oscillation.py, and test_package_guards.py,
with explicit guards
active under python -O. Direct script stdout is not necessarily normalized
like the runner's supplemental JSON receipts; the mathematical values agree.

Certificate contents
--------------------
GLOBAL_BOUND_CERTIFICATE.json certifies 0<G(t)<14 for every t>0.
OPERATOR_CONSTANTS_CERTIFICATE.json bounds all power-majorant constants.
RADIAL_VALUE_CERTIFICATE.json encloses both full radial values, including
the coefficient tail beyond 2^24. It retains the final exact coefficient,
not the entire coefficient array.
OPERATOR_VALUE_CERTIFICATE.json encloses T1, T^2 1, T^3 1, their truncation
tails, the positive denominator S3, the fourth-order error, and exterior
forcing error at both test points.
NONCONSTANCY_CERTIFICATE.json combines the regenerated intervals, includes
their exact 256-bit endpoints and dependency hashes, and checks disjointness.
OSCILLATION_BOUND_CERTIFICATE.json independently reconstructs the endpoint
algebra and certifies the separate midpoint/operator oscillation corollary.

Saddle API
----------
code/saddle_engine.py implements the finite correction functional in the
report. Inputs must be Python int (excluding bool) or fractions.Fraction;
integers are converted to Fraction before any division. Unsupported input
types, negative/noninteger order, insufficient jets, and nonpositive
variance are explicitly rejected. It is not a floating-point saddle solver.
verify_saddle_engine.py supplies a structurally different exact formal
exponential/Gaussian oracle through order four. These checks establish
finite algebra, not the analytic asymptotic remainder.

Fixture and source limitations
------------------------------
The two b003xxx.txt files each contain only 48 displayed OEIS terms,
transcribed and explicitly labeled. They are not complete downloaded b-files.
The four inline model fixtures comprise 207 displayed terms. No 10,000-term
external b-file check is claimed; the 10,000-term check compares independent
recurrence implementations. Third-party papers, private review materials,
large coefficient arrays, and floating-point diagnostics are not included.

Asymptotic constants and sufficiently-large ranges in the all-order and
inverse theorems are existential. The inverse error is relative and its
absolute width need not shrink. The report supplies no exact eventual
ceiling formula, growing-order theorem, infinite-series convergence claim,
or effective asymptotic onset.

Integrity and build details
---------------------------
SOURCE_FILES.txt is the complete input inventory, including semantic receipt
baselines. MANIFEST.json hashes every input and the PDF; the manifest itself
is excluded from its own hash list and included in the ZIP. ZIP member order,
timestamps, permissions, and compression choice are fixed. The runner
rejects unsafe paths, missing/unlisted sources, symbolic links, duplicate
JSON keys, tampered hashes, removable assertions, and unsafe output targets.
The --initialize option is for authoring a first PDF/manifest baseline only;
it still compares fresh arithmetic to supplied semantic receipt baselines.
Ordinary verification must not use --initialize.
