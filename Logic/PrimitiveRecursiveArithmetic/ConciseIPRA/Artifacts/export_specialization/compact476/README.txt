ONE BYTE BELOW THE CURRENT COMPACT CHECKER
========================================

Result: 274 significant tokens / 306 AST nodes / 476 normalized bytes.
Matched control: 272 / 306 / 477.

This is a composition of two existing implementation techniques. It does
not simplify the mathematical axioms or beat the separate 244-token and
265-AST-node incumbents. PROOF.txt states the exact transfer proof and limits.

Run:

    python3 verify.py
    python3 code/compact476.py < fixtures/compact_context__computation_zero_local.json

The kernel itself imports no file from this package. Only the standard
json module and the Python runtime are external. Every source byte of the
complete acceptance module is measured. Assertions are not used by the kernel.

Its input contract is the compact guarded Eq/D contract, with finite exact
integer/list proof data and final [goal,0] record. The initial zero is part
of that representation. Use the separate native/strict profiles when their
stronger goal/input validation is required; this package does not claim
that compact476 is such a validator.

The exact control is retained under control/. Coordinate-minimum baseline
sources are under baselines/, with their metrics in evidence/metrics.json.
PROVENANCE.json identifies the pinned repository and incoming source paths.
The finite regression receipt is evidence/verification.json.

convert_from_legacy.py is the inherited untrusted converter from the old
four-field stack: it wraps its final goal as [goal,0] and changes only
administrative integer-zero major fields to []. With --wrapped-goal it
preserves an already wrapped goal. Current control477 fixtures need no
conversion. This helper is not imported or trusted by the checker.

The existing MIT-0 license is retained. No repository write or publication
was made by this work.
