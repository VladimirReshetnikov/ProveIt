# Sign17 MF source-port concrete digit/byte block composition

This source-only twenty-two-stage attempt replays three audited sources: the
generic aligned-block composition core, the exact symbolic MF radix-digit
representation, and ten MF chunk equalities. It proposes a concrete list of
251 aligned eight-digit/47-byte blocks plus a final four-digit/18-byte tail,
and equality of their radix and base-256 decodings. The source arrangement
corresponds to the separately [externally audited reconstruction](../nine-sharing-sign17-mf-block-layout/README.md).

This stage does not yet prove that the digit blocks equal the symbolic MF
radix list or that the bytes are a Lean theorem about gzip/files. No new
checked theorem, whole-port, JSON or PDF binding is claimed until compiled
and reviewed. Provider source/state/outer/audit pins and resource guards are
retained. Author no-Lean preflight exited 0. Runner SHA-256:
`eab04cca9b6d1dd92eb80cd43341e9aeb72e13041d40e4ba12ee09fa97b3f485`;
manifest SHA-256:
`94847ee6a44de77a7bfafe91d5c5bb1e5e4b0ec8155a6045c5c524f0985f6251`;
new source SHA-256:
`ace9baa382dbeffdb3ed629ddda470a1491c010a65884a647a4adb34b23fe7ef`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mf-compose-blocks-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-mf-compose-blocks-terminal-independent/README.md) passed; the packet is frozen.
