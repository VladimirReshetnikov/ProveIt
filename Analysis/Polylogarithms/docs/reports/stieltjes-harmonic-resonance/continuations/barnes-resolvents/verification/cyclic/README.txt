FIFTH CYCLIC TORNHEIM JETS: PORTABLE VERIFICATION
11 October 2026 (UTC)

This directory accompanies the article's convergent symmetric Tornheim
generator, normalized mixed coefficient chi, and cyclic fifth-derivative
formula. It contains the exact calculations and the original completed
numerical diagnostics, together with the evaluator used for those diagnostics.

REPLAY

Tested with Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0. From this
directory, run:

    python3 -m pip install -r requirements.txt
    python3 verify_fifth_exact.py
    python3 verify_fifth_numeric.py

To print and save the expanded elementary correction separately:

    python3 derive_fifth_correction.py

Every command also works from an unrelated working directory by giving the
absolute path to its script. For example:

    python3 /path/to/package_verification/verify_fifth_exact.py

Imports and output paths resolve relative to the scripts. No repository
checkout, network access, external data, or development directory is needed
after installing the two dependencies. Run without Python's -O option,
which disables assertions used by the checks.

The exact verification took about 0.5 seconds in the packaging replay. The
recorded numerical suite took 68.6 seconds in the original environment;
runtime varies with hardware and Python. The numerical suite prints progress
after evaluating chi, after the diagonal fifth derivative, and after each
cyclic comparison. Its full computation was not repeated during packaging.

OUTPUT AND EVIDENCE

recorded_results/fifth_exact.json
    The unchanged result of 10 exact symbolic checks: the finite elementary
    correction, the preceding AAB normalization, three local subtraction
    coefficients, the general fifth cyclic formula, its asymmetric example,
    the diagonal coefficient relation, the mixed-derivative normalization,
    and the rectangular local-kernel identity.

recorded_results/fifth_numeric.json
    The unchanged 70-decimal-digit diagnostic record. It evaluates chi by
    integrated local and exponential series and compares three cyclic ray
    sums with independent Mellin evaluations of T. The tested triples are
    (1,2,3), (1,1,2), and (1,-2,3). Their absolute discrepancies were between
    5.52e-31 and 5.94e-30; each was below the script's 1e-28 threshold.

recorded_results/fifth_correction.txt
    The unchanged expanded elementary correction in plain text and LaTeX.

Reruns write generated_results/ beside the scripts. They preserve all files
in recorded_results/. The numerical JSON's K=65 is the cutoff used for chi;
the independent Tornheim evaluator uses K=62. Both exponential tails use
N=155, and both local Mellin splits are fixed at x=1. The numerical derivative
extraction uses eight interpolation nodes in h^2 with h=0.0015/2^j.

The exact checks verify finite algebra. The accompanying article supplies
the analytic proofs of continuation, normal convergence, and interchange of
derivatives and integrals. The numerical results use ordinary mpmath
arithmetic, finite truncations, and extrapolation: they are uncertified
diagnostics, not interval enclosures or proofs of the displayed digits.

COPIED EVALUATOR AND ATTRIBUTION

tornheim_mellin.py is copied byte-for-byte from the ProveIt incoming archive
docs/incoming/ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11.zip, at repository
commit 7bd45777a8a127e5dc69aff8887ca36a79a3059d. Its exact ZIP member is:

    ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11/verification/tornheim_mellin.py

The original attribution docstring is retained. That source describes its
adaptation from verify_rays.py in the preceding ProveIt coincident-directional
report. It evaluates T by Jonquiere and incomplete-Gamma expansions, without
using the new fifth cyclic identity or a finite-part correlation formula.

SOURCE_PROVENANCE.json contains the pinned URL, archive Git blob, archive and
member SHA-256 hashes, exact member path, and the upstream report's own source
revision. The copied member was compared directly with the decoded original
ZIP and with its published package manifest.

PACKAGING_CHECK.json records the successful exact replay from an unrelated
working directory, its byte-identical result, and syntax/control-character
checks for all four Python files. The mathematical algorithms and numerical
truncations were preserved. MANIFEST.json records delivered file hashes and
sizes; it excludes itself and outputs produced by later reruns.
