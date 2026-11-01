# Fixed-snapshot 258-module comparison

The guarded comparator returned `MATCHED_PASS` for 258 rows and 10,148 guarded
files. Its receipt matches the separately run peer receipt byte for byte, with
SHA-256 `b3e1528894c2c0905a32702f8733955d748eea414b9f81ecda004169aedfa349`.
The durable marker records the comparator subprocess exit; the wrapper's actual
tool-session exit is recorded separately in the terminal-observations packet.

This is proof evidence for the captured sources. Both Lean replays observed no
workspace drift at the start and six changed sources at the end; the comparison
likewise reports that the workspace does not match the snapshot. The inherited
848-module ancestor is author-only, and external package-transitive and dynamic
import ancestry remain as documented in the input packet. The separately planned
current-source successor is not a result of this comparison.
