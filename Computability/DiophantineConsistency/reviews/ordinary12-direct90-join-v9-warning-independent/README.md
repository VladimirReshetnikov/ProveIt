# Independent stage-04 warning-policy review

The v7 attempt compiled the first three stages, then rejected stage 04 because
its stdout contained three unused-simp-argument warnings. Lean exited zero;
stderr was empty. The warnings refer to positions 92:42, 160:26, and 164:26
in the pinned `IPRAStandardTheory.lean` source. Its produced object is
preserved separately as a compiled-but-rejected artifact, not an accepted
join result.

The v9 runner has SHA-256
`117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03`.
For stage 04 it requires the complete stdout to equal the pinned three-warning
baseline after replacing only the source path, and requires empty stderr. It
rejects errors and `sorryAx`; other stages reject both coded and uncoded
warnings. It rechecks compiled and archived source snapshots, and retains the
previously reviewed single-union, provider, companion, receipt, and axiom
guards.

The retained independent test accepted the baseline and rejected changes to
a position, simp argument, source path, warning count, extra warning, tagged
warning, tagged error, `sorryAx`, missing line, and empty log. The read-only
v9 manifest and receipt checks also passed for all 425 producer modules. The
capture exited zero with empty stderr; it invoked no Lean and does not prove
the subsequent join succeeds.
