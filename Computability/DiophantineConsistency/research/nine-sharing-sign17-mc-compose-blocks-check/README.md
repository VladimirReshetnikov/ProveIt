# Sign17 MC concrete block decoding composition

This twenty-stage source-only attempt replays the independently audited generic
composition core and proposes a concrete list of 251 aligned eight-digit /
47-byte blocks plus the final three-digit / 18-byte tail. It derives each
block's alignment from the six independently audited chunk identities, then
uses the generic theorem to equate the two decoded lists. The block ordering
corresponds to the separately [externally reviewed reconstruction](../nine-sharing-sign17-mc-block-layout/README.md).

This stage does not yet prove that the digit-block list equals the symbolic
low-mask runs or that the byte list is a Lean representation of a gzip file;
those are separate obligations. The external snapshot check remains Python /
filesystem provenance. No new theorem is claimed until compiled and reviewed.
Provider source/state/outer/audit pins and resource guards are retained.
Author no-Lean preflight exited 0. Runner SHA-256:
`0b079d41b8736c3c01fcda5b35085df7a49c949574096640d55c8f365580fe46`;
manifest SHA-256:
`73805ededa7e05423f51fbe872c5d1e5de6fab373b4e2c3f8888e2e1552d1d05`;
new source SHA-256:
`f594c73b4702743f22d2acc3f5c77cf9c6ea781a53b13a279d49856cce9756df`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-compose-blocks-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-mc-compose-blocks-terminal-independent/README.md) passed; the packet is frozen.
