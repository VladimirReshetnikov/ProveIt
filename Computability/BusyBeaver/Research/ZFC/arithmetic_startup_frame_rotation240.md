# The exact Rotation240 startup satisfies the represented frame relation

[`ArithmeticStartupFrameRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticStartupFrameRotation240.lean)
identifies the complete configuration after the checked 409,691-step blank
startup with the numeric entry frame used by the internal simulation. Its
control is 1; the physical register file is `[0,0,0,3,0,0,3,0,0]`; it has
167 value-one spare registers, a 64-cell pointer margin and gap 117.
The state code is 85 and the resulting right prefix has 181 zero bits.

`initialRelated` proves that this exact startup code and the logical seed
belong to the Σ₁ whole-frame relation. `run_related` transports the existing
finite bootstrap theorem into every IΣ₁ model. The long finite tape is
identified through generic codec identities, without evaluating its enormous
numeric code.

The [actual check](results/arithmetic-startup-frame-rotation240-verification.json)
passes 16 axiom probes and 18 typed callers with zero warnings and only
standard axioms. Source and audit took 3.502 and 2.784 seconds at default
proof limits, sharing 120 seconds with one thread and 4,096 MiB. The four
actual parents provide an exact closure of 777 project prerequisites.

The [history](arithmetic-startup-frame-rotation240/history.json.gz) preserves
both failed attempts and all source versions. The repairs keep every public
statement and audit caller unchanged: a generic codec lemma avoids reducing
the concrete tape, and explicit cast identities handle the finite constants.
No recursion or heartbeat limit was raised. The
[publication record](results/arithmetic-startup-frame-rotation240-publication.json)
binds the accepted source, audit, raw logs and guard; `boundary-v3.json` retains
the executed guard's default boundary filename as well as the canonical copy.

Startup identification and the checked arbitrary-entry simulation now have
matching interfaces. Their blank-control composition and the final internal
consistency sentence are recorded separately. Machine and framework attribution
remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt.
