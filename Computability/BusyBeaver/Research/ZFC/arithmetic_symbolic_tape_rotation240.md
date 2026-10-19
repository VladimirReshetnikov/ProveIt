# Internal interpretation of Rotation240 symbolic tapes

[`ArithmeticSymbolicTapeRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicTapeRotation240.lean)
interprets the actual 240-state symbolic syntax in every IΣ₁ model.
Normalization preserves the complete numeric tape for arbitrary internal
gap lengths and suffixes. Removing exterior zero runs is proved only when
the exterior suffix is zero. The actual `isMatch` test therefore implies
equality of the complete numeric configurations, including the head-side
convention and state code.

Boxes remain pure prefix parameters here; their execution is a subsequent
proof obligation. The imported 252-state arithmetic module contributes only
bit-prefix and affine algebra. No 252-state execution contract is used.

The [actual check](results/arithmetic-symbolic-tape-rotation240-verification.json)
passes 10 axiom probes and 12 typed callers with zero warnings and only
standard axioms. Source/audit times are 3.203/2.339 seconds under default proof
limits, sharing 120 seconds with one thread and 4,096 MiB. It uses 44 project
prerequisites, four direct external providers, retained Seq and Init/Omega.
The legacy pure-algebra provider's higher proof limits and missing pre-audit
capture are disclosed; no whole-cache attestation is claimed.

The [publication record](results/arithmetic-symbolic-tape-rotation240-publication.json)
and [history](arithmetic-symbolic-tape-rotation240/history.json.gz) preserve the
source, typed audit, raw logs, provider boundary and direct guard.
The complete internal binary simulation and PA endpoint remain open.
Attribution remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and
the maintained ProveIt work.
