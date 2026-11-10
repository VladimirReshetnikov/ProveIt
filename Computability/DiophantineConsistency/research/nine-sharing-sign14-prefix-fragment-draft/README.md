# Separate first prefix fragment: source-only draft

This proposes a kernel proof about one 19-byte included chunk, explicitly not a
Lean theorem about the full 689-byte row. The source format and concatenation
are checked separately by the external short-chunk packet. It avoids converting
the whole long String to a list during the kernel proof. No Lean result is
claimed until guarded compilation and independent terminal audit.
