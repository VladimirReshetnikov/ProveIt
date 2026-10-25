# Independent arithmetic reviews

These notes record independent review of the new arithmetic steps.
They separate ordinary unbounded proofs from finite checks of their
literal encoded equations. They do not claim a new proof-assistant
formalization of the inherited ZFC calibration or a proof of consistency.

- `AUDIT_COMBINED_241.md` reviews the shared Pell cap, new radix, and
  horizon-12 carry bounds. Its 225-check receipt is
  `AUDIT_COMBINED_241.json`. The portable independent checker lives in
  `../direct/code/audit_combined.py`; `../direct/verify.py` invokes it and
  separately verifies final contraction and coefficients.
- `AUDIT_POSITIVE.md` reviews the 86-operation quotient chart, the
  necessary positive-transport argument, and both exact leading forms.
  The packaged full proof and verifier are in `../positive/`.
- `AUDIT_CENTER246.md` reviews the weighted center, positive completeness,
  and the competing leading terms establishing exact degree 246.
  The literal construction and its finite checker are in `../center246/`.

The root `../verify_all.py` is the reproducible integration entry point.
All relative paths in these notes refer to this archive. Historical
working-copy names and the now-corrected positive metadata warning have
been updated to describe the packaged objects.
