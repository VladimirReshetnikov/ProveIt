RECTANGULAR TREE PORTFOLIOS AND FACTORIZED EXACT KERNELS
Research iteration for Vladimir Reshetnikov, 27 October 2026

Start with report.pdf (30 pages). report.tex is the standalone editable source.

MAIN RESULTS: NORMALIZED CONTRACTION EXPONENT COEFFICIENTS
All coefficients multiply s/sqrt(log2 s), not the SAT variable count directly.
They are ordinary proof/certificate refinements relative to inherited inputs.
* Four-plan rectangular/tree portfolio: time 30.491276..., space 28.853020...;
  safe eventual coefficients 30.492 and 28.854. Both improve the comparable
  incoming 30.891019/30.753913 certificate. The coefficient norm check covers
  73,298,242 tuples, with a separate reconstructed integer audit.
* Generic polynomial space: 46.071078..., safe 46.072, versus 46.184846.
* Root degree <=s^.51: polynomial-space 21.139416..., safe 21.14; alternatively
  cached time/space 14.502837..., safe 14.503.
* Root degree <=s^(1/12): cached time/space 12.015609..., safe 12.016.

PRACTICAL COMPONENTS
* Matching-potential factorization reduces maintained-dense arithmetic
  O(M Q^2+V Q) to O(M Q+V Q). A positive-support successor keeps only O(K+M)
  rational potential entries, excluding graph input, requested traces and
  dense Q^2 output. All exact label choices, ties and potentials are preserved.
  Against the stronger array-factorized reference, random-fixture wall gains
  are 1.91--3.87x; the fully filled 64-cell control gains 1.58x. Tiny regressions
  and raw samples are retained. This is not an end-to-end SAT benchmark and
  is not a universal comparison to other, differently specified packers.
* Mixed 3/5 projective filtering implements an EXISTING general identity in a
  fixed rank-four quotient ring. Classical precision-doubling root preparation
  is charged in both fresh-root comparisons. Six mixed-even fixtures give
  1.34--4.67x versus fresh common roots and 1.005--1.68x versus strong anisotropic
  half-grid extraction. The first latter result is effectively a tie; an
  eight-ones profile is about 24x slower and is explicitly not recommended.

PUBLIC FORMALIZATION UPDATE
The user's linked anthropics/formal-math PR 31 revision
1a6eee293b9e00cb432eef6018a21f523623a9af is now public and merged.
Published CI logs report Lean and independent nanoda acceptance of both
theorems under the standard-axiom allowlist. The checked CI tree is identical
to the requested revision. This is UPSTREAM CI evidence, not a local Lean
rebuild in this work. The released paper retains the same main theorem and
printed Lean definitions; reporting and editorial material changed.
The old description "unpublished formalization" is superseded.
Formal statement/paper correspondence still requires mathematical review.
None of our new refinements is thereby automatically formally verified.

SCOPE AND LIMITS
No smaller global SAT logarithmic exponent is proved. No full fast SAT solver,
global optimum over all unreported combinations, or comparable numerical
dominance over the separate Claude architecture is claimed. Time/space and
degree premises must not be mixed. Component timings use exact-output matched
authored references, shared preparation/output policy and five raw repeats;
wall time is machine dependent. No incoming packet program was executed.

SOURCE PINS
Initial ProveIt:73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d.
Closing ProveIt:7de9d09fecd17de776d712835ecb2011205c531d.
Nine arrival archives were authenticated; 443 filed Git blobs match their
arrival bytes after relocation. docs/incoming was empty at the closing check.
Source review also uses earlier pinned packets and the OpenAI manuscript.
Selected snapshots and hashes are in sources/, incoming/manifest.json and
closing_*json. Anthropics evidence and twelve selected source files are in
anthropic_snapshot/. The full external Lean project is NOT repackaged or run.

REPLAY (Python 3.10+ STANDARD LIBRARY)
From the extracted bundle:
  python3 code/verify_bundle.py
  python3 matrix_checks/verify_four_plan.py
  python3 tree_checks/audit_four_plan.py
  python3 matrix_checks/verify_degree_051_cached.py
  python3 tree_checks/check_schedule_combinations.py
  python3 tree_checks/check_matching_factorized.py
  python3 code/check_mixed_projective.py
  python3 qa/check_components_independent.py
  python3 qa/check_degree051_independent.py
Repeat with python3 -O. Checks use explicit failures, not removable asserts.
For complete extracted-ZIP replay:
  python3 code/replay_archive.py PATH_TO_RELEASE.zip /tmp/replay.json
Use a suitable temporary path and python on Windows. The replay validates
historical timing records but does not retime benchmarks, access the network,
execute imported code, or build Lean. It includes three negative integrity
controls. Exact exhaustive checks may take a few minutes.

BENCHMARKS
See the scripts and report for options. Authoritative final ledgers:
  tree_checks/matching_factorized_benchmarks.json
  results/mixed_projective_benchmark.json
Both bind implementation and benchmark source hashes. Superseded ledgers are
historical only; do not use them for final speedup claims.

PDF BUILD
  sh build_report.sh
Requires a configured pdfLaTeX installation with the report's named packages.
No software is downloaded or installed by the build or check scripts.

INTEGRITY / TRUST
SHA256SUMS seals every other packaged file. These hashes prove byte consistency,
not mathematical correctness or authorship. Compare the ZIP SHA-256 against
the independently delivered release identity before executing any script.
No GitHub branch, file, issue, comment or pull request was changed/published.
