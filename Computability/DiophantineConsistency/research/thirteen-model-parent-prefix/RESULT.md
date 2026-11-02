# Paired 2011 parent-zero prefix result

The reviewed driver completed its sequential 20-module author and peer
builds against the independently audited 70-source parent. Session 98550
actually exited 0 and printed the final line
`PASS_PAIRED_2011_PARENT_PREFIX 4f31021934bd9b9d85d8d734d636fd17b35c953018f2bd13c42dc0236b0e4c42`.
The [terminal observation](terminal-observation.json) records the exact
launch HEAD, observed outer exit, and loader-environment check. The
[pair receipt](pair-receipt.json) records all 40 child compiler and direct
`--deps` exits, sampled leader RSS values, corresponding object/log hashes,
direct companion guards, and before/after parent and source-freezer audits.
The 40 compiler logs are retained under `logs/`; the 48 MiB object trees
remain in `/tmp/ipra-thirteen-parent-prefix-pair-01` for independent rehash.

The Python process started with `LD_PRELOAD`, `LD_LIBRARY_PATH`, and `LD_AUDIT`
absent and all three explicitly removed, using isolated `python3 -I -S`.
The retained parent audit records HEAD
`042c491efa092a8f847971c0d230b8bffe418980` at the final check; the driver's
before/after audit comparison also required the two parent audit outputs to
match. The complete wrapper stdout is not archived as a separate transcript;
the actual final line and exit were observed directly, and child outcomes and
logs are preserved in the receipt. Each side emitted one existing `simp`
linter suggestion from `ArithmeticBinomLegendre`; there were no reported
`sorryAx` or error messages. Corresponding compiled objects and logs match.

This is a **matched dependency prefix**, not yet an independently audited
result, an actual-zero caller theorem, a rank-phase theorem, or an iPRA proof.
The 24 remaining frozen window/rank sources are outside this prefix, as are
all later graph-bridge and fixed-port obligations. Resource checks sampled
leader RSS and free space; they were neither hard quotas nor continuously
enforced reservations. Package-transitive/dynamic ancestry and the original
Foundation wrapper's unobserved exit retain the parent audit's qualifications.
