# Symbolic beta byte pattern: corrected natural-digit retry

This fresh-output sixteen-stage probe replays the prior audited provider and
corrects the failed proof: reorder exponent rewrites, use `Nat.eq_sub_of_add_eq`
after explicitly unfolding the beta definitions, and explicitly decode digits
in `ℕ` before casting to `ℤ` in the current-port statement. The last change
corrects the first attempt's unintended integer-valued `ofDigits` elaboration;
it is a change to that statement, and directly matches the unsigned natural
byte decoder intended here. The general repunit and beta-pattern statements
are unchanged. The [first failure](../nine-sharing-sign17-beta-byte-probe-check/attempt01/README.md)
remains recorded. The attempt retains the same resource limits.

This proposes no Lean statement about filesystem bytes, gzip, hashes, JSON,
the other three ports, or the PDF. The separate external observation and the
binding design are described [here](../nine-sharing-sign17-external-binding-design/README.md).
No new checked theorem is claimed yet.

Author no-Lean preflight exited 0. Runner SHA-256:
`8a7bf9b3dcc072116b02ee74622468c5aff929342c628dc1cd8b9a9809abae1b`;
manifest SHA-256:
`0d07d24d62e7a191e75a08283b1b91c20d2fb33072a962f70786ca43170b8396`;
new source SHA-256:
`d6d360e854dfd365eb832d3c583b433838e19abd6dc313b00e7999ef827ba42d`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-beta-byte-probe-retry-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-beta-byte-probe-retry-terminal-independent/README.md) passed; the packet is frozen.
