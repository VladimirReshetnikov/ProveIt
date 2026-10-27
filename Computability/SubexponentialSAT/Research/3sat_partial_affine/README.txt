PARTIAL AFFINE-PLANE DOUBLING FOR 3-SAT
Research packet, 27 October 2026 (UTC)

START HERE

  report.pdf       Complete research report with proofs and source references.
  report.tex       Main LaTeX source; included sections are in sections/.
  PROOF_STATUS.json
                   Exact claims, inherited premises, and verification limits.

RESULT

For a normalized 3-CNF with L literal occurrences (L <= 3m), relative to
the reviewed exact contraction interface, the main algorithm has

  time  poly(n,m) * 2^((C_T + o(1)) L / sqrt(log_2 L)),
  space poly(n,m) * 2^((C_S + o(1)) L / sqrt(log_2 L)),

  C_T = (pi/ln 2) sqrt(32012591492467 / 5556600000000)
      = 10.87878166668154...,
  C_S = (pi/ln 2) sqrt(32012591492467 / 6417873000000)
      = 10.12253456921954....

Its root has fifteen groups, made by duplicating six points of F_3^2;
its complete recursive schedule is 15 -> 10 -> 7 -> 4 -> 4 -> ... .

A second, fully doubled eighteen-group construction gives the alternative
time/space pair approximately (11.07682383502, 9.97733739358).
These are separate algorithms: the faster time and the smaller space
must not be combined into one claimed pair.

The strongest compatible prior-ingredient composition constructed in this
review has coefficient 11.26420175559485..., so the new main time bound
improves that coefficient by about 3.42 percent. This does not establish
global optimality over all prior compositions. It improves a leading
exponential coefficient, not the logarithmic exponent order. No new
unrestricted variable-only order improvement was proved.

SOURCE SNAPSHOT AND CREDIT

  ProveIt:
  324f3d9b009ab0323f33be65cd6577867c9c4338

  Anthropic formal-math:
  1a6eee293b9e00cb432eef6018a21f523623a9af

The closing project-affecting commit check still returned the ProveIt
snapshot above. It contains 34 refinement packets. The five latest
packets already contain affine-nine menus, coupled-pair certificates,
rectangular backends and joint time/storage selection. Those are prior
ingredients. The new contributions are the partial and full duplication
menus, their exact finite certificates, and their completed low-degree
time/space compositions.

audit/source_ledger.json records immutable source paths, Git blob IDs and
retrieval hashes. All 144 fetched report-source files and 41 fifth-round
code files matched their expected Git blobs. This is an integrity check,
not proof verification. The full source corpus is not duplicated here.

REPRODUCE

Run these commands from the extracted packet directory:

  python3 verify_manifest.py
  python3 run_checks.py
  python3 run_checks.py --optimized
  python3 build_report.py

The seven exact checkers and their helpers use only the Python standard
library. All mathematical checks use explicit exceptions and remain active
under python -O. Normal and optimized replay produce identical result
files. Main certificates were also reconstructed independently.

Building the report requires pdfLaTeX and its standard listed packages.
Shell escape is disabled. The build checks unresolved references and
overflowing boxes. PDF metadata may differ across TeX environments, so
verify the original manifest before rebuilding. Replay rewrites results/.

CHECKERS

  code/audit_round5_new15.py
    Independently reconstructs the 15-group time certificate, checks all
    82,134 pairs, and certifies the paid schedule and rational constants.

  code/check_partial_affine_joint.py
    A separate reconstruction: 82,134 time pairs, 4,374 boundary pairs,
    37,908 mixed pairs, executable integer joint selector, and full schedule.

  code/round5_affine_certificate.py
    Eighteen- and nine-group rectangular certificates, exact r18 local
    witness in the entropy relaxation, and complete 18 -> 9 time schedule.

  code/check_rectangular_joint.py
    Independent r18 joint certificate: 124,416 time pairs, 6,534 boundary
    pairs, 57,024 mixed pairs, and executable integer selection.

  code/audit_round5_baseline.py
    Reconstructs the compatible cyclic13 certificate and prior-only
    13 -> 10 -> 7 -> 6 -> 4 schedule. Use its stronger_five_stage result.

  code/check_tensor_regrouping.py
    36 small ring fixtures, 144 full plan contractions, and 24,192 literal
    index assignments; both new integer selectors are exercised.

  code/verify_occurrence_bridge.py
    483 formula cases and 1,293 exact counting comparisons, including
    constant clauses, unused variables, and occurrence-preserving branches.

AUDIT AND LIMITS

  audit/independent_schedule_audit.md gives a second readable proof and
  precise immutable anchors for every imported tail coefficient.

  audit/formal_audit.md records the external formalization review and
  algebraic barriers, with its closing fifth-round qualification.

  audit/exploratory_*.json contains a finite nearby-menu search record.
  These numerical observations are not optimality proofs and are not
  dependencies of either new theorem.

The package does not implement the complete fast SAT algorithm or the
asymptotic matrix backend. It does not rebuild Lean, machine-check the
imported contraction theorem, or claim a practical SAT speedup. The new
proofs and finite checks are explicitly relative to the source interfaces.
