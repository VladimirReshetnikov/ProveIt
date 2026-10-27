ADAPTIVE FOUR-BLOCK CONTRACTION FOR SUBEXPONENTIAL SAT
Research prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific time)

START HERE
  report.pdf   Complete mathematical report, review, proofs and limitations.
  report.tex   Master LaTeX source; includes k4_certificate.tex.

RESULT
  This iteration improves explicit leading coefficients in the normalized
  tensor-contraction upper bound. It does not improve the logarithmic order
  of the general SAT exponent.

  Common interface: s Boolean wires, maximum degree ceil(s^0.9), initial
  precision and coefficient truncation at most s, and the imported admissible
  entry-oracle / immutable creation-precision conventions.

  Cached algorithm, with the same 12/5 matrix backend as the prior packet:
    Time  poly(s+description) * 2^[(32.9158138649243+o(1))*s/sqrt(log2 s)]
    Space poly(s+description) * 2^[(31.6617067861940+o(1))*s/sqrt(log2 s)]
    Safe eventual coefficients: 33 time / 32 space.

  Optional 19/8 matrix backend:
    Time coefficient 32.8563452760064; space coefficient 31.4674831880977.

  Polynomial-space algorithm:
    Time coefficient 50.3937257005048; safe eventual coefficient 51.

  The new local cached inequality is sharp for its three-matching cost model:
    min_matching max_merge_cost <= sqrt(244/75) * ||six edge weights||_2.
  The new streamed four-cluster inequality has squared constant 13/3 on
  undirected weights, or 26/3 on the corresponding directed coordinates.

COMPARISON
  Opening pin: ProveIt main@fa6e904d109b738154db7fe41e7f2777e6d24aee.
  Closing pin: ProveIt main@dde01c4a63b822c25b8eb345299346c36f837b49.
  The review covers 20 refinement packets and 2 primary manuscripts.
  The 5 newest incoming ZIPs were filed during the review by 450252e9d86c.
  Their filed versions were checked against the reviewed archives.

  Best displayed incoming cached pair: 35.3545880584 / 34.2748030050.
  Compatible prior cached composition: 34.8321534202 / 33.9927010637.
  Best displayed incoming polynomial-space coefficient: 55.7094783189.
  Prior fixed trees on our polynomial-space schedule: 54.1282952066.

  Comparisons are between upper-bound certificates, not measured runtimes.
  No global optimality of schedules is claimed. The wire constants are not
  SAT-variable constants. Low-degree promises and conditional n/log n targets
  must be kept separate; their hypotheses are not established here.

WHAT IS INCLUDED
  code/adaptive_four.py                Exact finite cached graph evaluator.
  code/adaptive_separator.py           Exact finite streamed graph evaluator.
  code/verify_k4_certificate.py        All 216 forms and the sharpness witness.
  code/audit_global_schedule.py        Exact interval recurrence/packing audit.
  code/verify_comparisons.py           Prior composition and backend comparison.
  code/verify_adaptive_four.py         Independent direct-sum and oracle tests.
  code/verify_adaptive_separator.py    Four-cluster and nilpotent-ring tests.
  code/replay.py                       One-command offline replay.
  code/build_report.py                 Rebuild the PDF without shell escape.
  results/                            Executed ordinary and optimized checks.
  provenance/                         Source hashes, scope and commit inventory.
  audit/                              Independent proof reviews and derivations.

REPRODUCE
  Python 3.10+ and the standard library suffice:

    python3 code/replay.py

  This checks the delivered file manifest and runs each mathematical checker
  normally and under python -O. Parsed outputs must agree. Replayed results
  go to replay_results/, preserving the original evidence.

  With a normal TeX Live or MiKTeX installation:

    python3 code/build_report.py

  The PDF build uses temporary files and rejects unresolved references and
  overfull boxes. Rebuilding may change the PDF bytes and therefore the
  original manifest; verify the delivered archive before rebuilding.

PROOF AND IMPLEMENTATION BOUNDARY
  The new finite inequalities and resource bounds are proved in the report.
  The deformation, integral basis, packing, recovery, child construction and
  SAT reductions are explicitly imported. No new Lean/Rocq build is claimed.

  The finite cached evaluator uses NAIVE matrix multiplication. It tests the
  exact regrouping and paid child-oracle interface; it is not the asymptotic
  fast backend. The included code is not a complete SAT solver. No practical
  SAT benchmark or measured global runtime improvement is claimed.

  General SAT order remains n loglog(n)/sqrt(log(n)); fixed density remains
  n/sqrt(log(n)). The conditional stronger orders still require a new closed
  representation or summation interface, beyond the results in this packet.
