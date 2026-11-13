EAGER ENTRY THREE-FIELD CHECKER: REPRODUCIBLE VALIDATION

The sound measured program is checker_candidate300.py:
300 significant tokens /346 AST nodes /626 normalized bytes /393 gzip-9 bytes.
See PROTOCOL_REVIEW.txt for the independently reviewed proof obligations.

Run:
    python3 verify.py

The recorded receipt contains236 isolated normal/-O executions:
206 proposed-checker executions over103 cases,28 original-control executions
over14 canonical positive certificates, and2 deliberately invalid diagnostic
executions confirming the necessity of witness validation before the major.
Every result matched its expectation. The diagnostic's acceptance is an
EXPECTED failure of the deliberately invalid ordering, not a candidate failure.
Of the236 runs,62 accepted and174 rejected; the62 include2 diagnostic acceptances.

The verifier creates its invalid diagnostic only in a temporary directory and
deletes it after the run. No invalid checker needs to be shipped as a standalone
program. Do NOT copy the experimental UNSOUND_late_witness.py into a final bundle.

translate.py maps canonical accepted entry304 certificates to this profile by
changing source0 to[] only on nonmatching introduction records. It retains
numerical zero codes, zero-computation sources, and closure-specialization
sources. Its scope simulation is independent readable code and is not imported
by the measured checker. canonical_positives.json contains all14 translated
canonical fixtures; cases.json includes positive and rejection cases.

reference/ supplies the unchanged control and source fixtures, with MIT-0
license. PROVENANCE.json records their original archive entries and hashes.
The same raw sorted public grammar is validated as in the original control;
canonical theorem completeness is claimed, not completeness for every allowed
padding-slot spelling. No raw certificate-language equality is claimed.

Recommended files to copy to the final archive:
    checker_candidate300.py
    translate.py
    verify.py
    PROTOCOL_REVIEW.txt
    README.txt
    PROVENANCE.json
    receipt.json
    canonical_positives.json
    cases.json
    future_witness_capture.json
    reference/ (complete directory)

No further randomized or optional trials are required by this review.
