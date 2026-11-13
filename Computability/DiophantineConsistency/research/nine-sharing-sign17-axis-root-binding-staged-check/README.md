# Sign17 corrected-axis staged root binding: split diagnostic

This fresh-output diagnostic replays four audited factor modules, then splits
the five binding identities into three sequential modules: low term, two
factor terms, and root/scale. The corrected axis and binding statements are
unchanged. It replaces potentially expansive `ring` tactics with `rfl` after
structural simplification, so a mismatch should be exposed without polynomial
expansion. This is a proposed diagnostic, not a checked binding or lower bound.
The prior [memory failure](../nine-sharing-sign17-axis-root-binding-retry-check/attempt01/README.md)
is frozen; resource limits remain unchanged.

Author no-Lean preflight exited 0. Runner SHA-256:
`61ada8d2dbb265d2c340a56c38dace9a3e33cf9ad33ce6657ddc15fd34562e2e`;
manifest SHA-256:
`a0f740800d27c664e38d9c7e989cf1b0d53da100586bd134d02629b3cd1990e6`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-axis-root-binding-staged-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-axis-root-binding-staged-failure-independent/README.md) passed; the packet is frozen.
