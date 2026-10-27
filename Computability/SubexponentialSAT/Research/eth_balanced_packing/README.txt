BALANCED COLLISION PACKING FOR EXACT COUNTING
Research report prepared for Vladimir Reshetnikov, October 26, 2026

MAIN RESULT
For the normalized Boolean tensor interface in report.tex:
    time <= poly(s + description_length)
            * 2^((94.74820225953412... + o(1))*s/sqrt(log2(s))),
    space <= poly(s + description_length).
Here s bounds the initial wires, initial coefficient precision and polynomial
truncation; maximum degree is at most ceil(s^(9/10)).
The coefficient is NOT automatically a coefficient in terms of SAT variables.

NEW CONTRIBUTIONS
1. Deterministic two-stage whole-vertex labeling with nearly equal pair-class
   loads under M >= 4 D_arr Delta lambda^4. Row balancing is greedy; column
   labels use exact rational conditional expectations. Parallel edges allowed.
2. An additive logarithmic precision guard replacing the old double taper.
3. An integer capacity schedule attaining the limiting coefficient without
   fixed asymptotic slack.

REUSED INGREDIENTS
The OpenAI deformation, interpolation, and recursive tensor identities;
the previous exact Hermite taper and precision refinement; the previous
factorial Cauchy modes. Full attribution and source pins are in report.tex.

COMPARISON
Prior numerically instantiated normalized certificate: 648.4410666487...
Prior schedule plus separately proposed Cauchy modes: 374.3776243833...
Prior optimized-family boundary plus Cauchy: approximately 368.65401812.
New adaptive certificate: 94.7482022595...
These compare upper-bound coefficients, not measured runtime ratios.
The separate 49-page eth.pdf uses a different method and leaves its leading
constant unspecified; no numerical dominance over it is claimed.
No smaller general 3SAT logarithmic order is established here.

REPRODUCE CHECKS (Python 3.10+, standard library only)
    python3 checks/check_packing.py
    python3 checks/check_analysis.py
    python3 -O checks/check_packing.py
    python3 -O checks/check_analysis.py

BUILD PDF (standard LaTeX distribution)
    make pdf
The PDF build needs pdflatex with amsmath, amssymb, mathtools, microtype,
lmodern, geometry, booktabs, longtable, enumitem, xcolor, fancyhdr,
xurl and hyperref. A precompiled PDF is included.

VERIFY RELEASE FILES
    python3 checks/verify_manifest.py
The manifest records all release files except itself. Results from rerunning
the check scripts may differ in elapsed-time metadata; verify the release
before regenerating those results.

SCOPE
The Python code is an exact packing/schedule prototype, not a complete
subexponential SAT solver. Finite tests do not prove the asymptotic theorem.
No new Lean or Rocq proof was built. The large eventual size thresholds are
not practical performance claims.

SOURCE SNAPSHOT
ProveIt: aa6933442eb936962de79ba6d321cd0391c450bd.
Reviewed intake commits: a505bd768bce347c70e923586c5f72ad3085bf44,
64b3202ee84fc4d71fe69c34d2110c93b7da95cd,
8afdbbea48d67b8d252a99e8926f3eca9649eae3.
All seven ZIPs at that snapshot, original paper.pdf, and distinct eth.pdf.
Later placement, upstream vendoring and summary commits were checked through
45233238aebf0e0a80f5a6cc39dbeaf1b28d9f9d; report source bytes match.
OpenAI math: 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
The source TeX blob hashes are independently checked in source_manifest.json.

INTEGRATION
This directory is suitable for an incoming research packet. Replace the
collision-packing lemma and schedule in the quantitative contraction
appendix, preserving the stated source dependencies and creation-precision
convention. No remote repository changes were made.
