BACKWARD REPLACEMENT IN iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026

STATUS
------
This archive is a verified partial research result, not a claim to have
found an axiomatization below all current checker-size minima.

1. The report proves that the backward crossed replacement rule

       s=t,  Rep_t^s(u)=r   /   r=u

   gives exactly the native kernel's sequents. The existing full first-order
   iPRA bi-interpretation transfers, including both formula round trips and
   identity numerical composites. All primitive rules and syntax are stated.
   The optional exclusion of a literal-zero source is also proved on paper,
   including its combination with the seven-rule presentation.

2. backward/checker.py implements the complete eight-rule presentation with
   strict syntax/scope validation. It is a readable correctness demonstrator:
   1647 tokens / 1807 AST nodes / 7121 normalized UTF-8 bytes. A matched Tr
   control measures 1581 / 1738 / 6971. The new walker adds trusted code.

3. grouped/code/checker_grouped.py implements the existing compact guarded
   calculus with regrouped certificate packets. It measures 250 / 281 / 604,
   against its matched control's 251 / 283 / 605. Only the token coordinate
   improves the prior collected envelope (251 / 275 / 502).
   The compact promised-input contract is retained. A separately measured
   strict companion actually validates the whole certificate alphabet and
   canonical guarded goal; it measures 402 / 451 / 971.

FILES
-----
ipra_backward_replacement.pdf     Compiled research report.
ipra_backward_replacement.tex     Complete report source.
backward/                        Complete new calculus checker, matched
                                 control, generators, fixtures and reviews.
grouped/                         Compact/strict regrouped checkers, controls,
                                 translator, exact simulation proof and tests.
notes/                           Expanded mathematical proof notes.
evidence/                        Combined reproduction results and PDF macros.
PROVENANCE.json                  Pinned source and precise claim status.
SHA256SUMS.txt                    Checksums of the archive contents.
reproduce.py                     Re-runs the delivered executable checks.
build.sh                         Rebuilds the report PDF using latexmk.

REPRODUCE
---------
Use CPython 3.12.14 for the exact normalization counts. The verifier itself
uses Python's standard library. From this directory:

    python3 reproduce.py
    sh build.sh

Or run the individual suites:

    python3 backward/test_checker.py
    python3 backward/independent_audit.py
    python3 backward/compare_checkers.py
    python3 grouped/verify.py

The BRep stdin driver accepts closed theorems only. The verify API also
checks open sequents. See backward/README.txt for its exact grammar.
The grouped checker uses a DIFFERENT certificate encoding; see its README.

EVIDENCE LIMITS
---------------
Finite regression tests and manual source review are not a machine-checked
metatheorem. The new equivalence is proved in the report. The existing native
bridge is imported from the pinned repository; its Lean development was not
rebuilt in this session. No new Lean or Rocq formalization is claimed.
One fixture listed in an upstream manifest was absent at the pinned commit;
grouped/evidence/missing_upstream_fixture.json records that exclusion.

The inspected source commit is:
36d37fc1071fe289371f6bcd7dcfa0eac593a5a6
https://github.com/VladimirReshetnikov/ProveIt

Upstream code and mathematics are attributed in the report, provenance files
and accompanying MIT No Attribution license. The original marker technique,
native kernel, and arithmetic bridge are inherited; the backward orientation
and its completeness proof are the mathematical contribution of this work.
