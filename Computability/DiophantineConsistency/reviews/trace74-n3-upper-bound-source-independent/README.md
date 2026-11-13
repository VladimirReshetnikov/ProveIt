# Independent source review: ordered-ring upper endpoint

Source SHA-256 `926746d00bdb89aaa1c6797766ec875f41821d9ffdffddbb9c2b5b049fb63b72`. Source math is consistent; no Lean was run here. Given x≥32 and the strict polynomial inequality k·y<c, assuming the proposed upper bound fails makes u=x−32 and w=2y−(x²+4x+8) nonnegative. The already independently audited shifted-certificate theorem then gives a positive expression. The displayed ring identity rewrites it exactly to k·y−c, contradicting the hypothesis, and concludes `2y<x²+4x+8`. The shift identity and denominator-free polynomial were independently checked in the external obstruction audit.

The theorem is generic ordered-ring arithmetic; it does not assume or establish a Pell recurrence, actual graph zero, fixed ports or an n=3 exclusion. Rewrites into let-expanded expressions, `ring` and `linarith` remain Lean elaboration risks, and selected provider/direct import and full ancestry require separate prelaunch review.
