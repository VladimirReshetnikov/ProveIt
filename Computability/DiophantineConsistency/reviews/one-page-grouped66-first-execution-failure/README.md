# First grouped66 application attempt stopped before rendering

The exact twice-reviewed checkpoint at14e3f3d3d1 was released separately
in3a0626ad98. Command1 produced the four intended source files and passed.
Command2, the normal source-only audit, exited1 without a success receipt:

    ValueError: prose whitelist span is outside all math

Commands3--10 were never started. No PDF or Lean process ran, no retry was
made, and the maintained equation.pdf/TeX remained unchanged. All16 held
core payloads and the external renderer were still byte-identical when
this evidence was preserved. FAILURE.json binds that entire first record.

The newly added mathematical-region regular expression accepts a `\[`
opener beginning at the second slash of the title's `\\[-1pt]` linebreak.
It therefore treats the first ordinary prose as part of an incorrectly
opened display and rejects its whitelist span. The two full static reviews
missed this delimiter interaction. The check fails closed; it does not
change the equation, a coefficient or an accepted page.

The four generated source files have been relocated here without changing
any byte; their hashes equal command1's full receipt. Full stdout, stderr,
the build receipt, original HOLD and source pins are retained. Original
external records remain in /tmp. This avoids discarding the failed attempt
or silently treating a second run as its first success.

A code-only repair must distinguish a display delimiter from an optional
linebreak argument, keep escaped inline dollars outside math, retain every
existing check and control, and freeze fresh pins/HOLD. Fresh full ROOT and
independent static approvals and another separate exact execution release
are required before a retry. The new held commands must use distinct
`/tmp/grouped66-r2-*` receipts. This failure record releases no execution.
