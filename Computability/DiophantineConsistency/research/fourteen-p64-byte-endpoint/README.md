# P64 endpoint on four closed Lean byte recipes: in progress

`P64ByteEndpoint.lean` proposes a direct client of the four closed Lean byte
recipes and the P64 endpoint. It defines the four integer ports by pointwise
`Nat.ofDigits 256`, uses `CompactFourPortByteAssembly2.decode_ports` to
identify them with the symbolic ports, and attempts to restate the native,
standard and equality-only iPRA endpoint statements. **The client is not yet
checked:** both bounded Lean attempts timed out. No byte-endpoint theorem is
claimed here.

## Selected-provider preparation

The byte provider's recorded 631 selected files were hashed against its
manifest. Of those, 609 also occur in the P64 replay overlay, and all 609
matched byte-for-byte; 22 occur only in the byte selection. No foreign
`.olean`, `.ilean`, `.ir`, or recorded companion files were found for the
selected byte modules. The shared `CompactSymbolicPorts.olean` and the flat
`CompactFourPortByteAssembly2.olean` also matched. This is a selected-file
preflight, not an audit of every transitive project, package or dynamic
dependency.

The first preparation stopped without running Lean because it expected the
flat assembly object to be absent; it was already present and had the exact
same hash. The preparer was corrected to accept that overlap only on a hash
match. The subsequent preparation exited 0 with the counts above and created
a fresh symlink overlay. Its guarded plan is retained at
[`observations/attempt01/plan.json`](observations/attempt01/plan.json).

## Lean attempts

Outer tool session 64610 exited 1. Lean did not finish within its 180-second
limit; the captured result records exit 124, no output object, and unchanged
source, Lean binary and two direct-import hashes. The worker was observed
waiting for page I/O for much of the attempt. The exact source, result and log
are retained under [`observations/attempt01/`](observations/attempt01/).
This is a failed attempt, not evidence that the endpoint theorem elaborates.
The first input source SHA-256 was
`7fec84e36daf125568ed00f3b26bbd06095878288a7de0f81ca678802ba4844a`;
its log SHA-256 was
`7040d43177aff4ca7fec38d4a53b1daa53e6e9ece089575286011d3f2143121b`.

[`prepare-retry.py`](prepare-retry.py) prepared a separate fresh overlay;
[`run-retry.py`](run-retry.py) ran the unchanged source with a 360-second
timeout. The retry preparation again passed the 631/609/22 and companion
checks. Outer tool session 73174 exited 1 after that timeout. Its captured
Lean result is exit 124, with no object; the source, Lean binary and two
direct-import hashes remained unchanged at the recorded guard points. Its
separate plan, source, result and log are retained under
[`observations/attempt02/`](observations/attempt02/). The result and log
SHA-256 values are
`d2fc8a288058f5f738607f424f325c408e53f554a33fab71d1a7b307edeaa39e`
and `6fc7680db086c92a3e75ee2d1228558482d3b924328b5dbe747f3a43c5f9b7c4`.
This retry is likewise not evidence that the client elaborates.

The intended conclusion concerns closed Lean byte-list recipes. Filesystem
bytes, gzip decompression and PDF interpretation remain external even if a
later Lean check succeeds.
