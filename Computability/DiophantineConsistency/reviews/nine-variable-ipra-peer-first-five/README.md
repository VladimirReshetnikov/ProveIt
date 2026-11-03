# Nine-variable peer replay: first five stages

A fresh guarded peer overlay at `/tmp/nine-ipra-guarded-peer-20261102-a`
completed the first five stages of the existing 104-stage nine-variable
incremental plan. Both the author and peer runner ledger checks passed. The
five source hashes and normalized complete compiler outputs agree, as do the
recorded direct dependency and companion guards after normalizing the two
overlay paths and accounting for the exact stage-2 object hash difference
below. Stages 1, 3, 4 and 5 produced byte-identical objects. The peer reused
the author's exact previously registered warning baselines; this is not an
independent assessment of the warnings.

**The stage-2 objects are not byte-identical.** The accepted author
`ModelDifferenceRing.olean` has SHA-256
`59ca56d54f6cdca4a25395e3a2bb0657055174bd0f87783e2ad94538208d81e1`;
the peer has SHA-256
`56d72be784c672032c1e2f69a582cfbc3c1b0709b1542abddb148b19af7f02fa`.
They have equal length, their respective source pathname appears exactly once
at offset 1,008,328, and the three immediately preceding little-endian length
fields describe that pathname. The program [`compare.py`](compare.py)
checks that replacing exactly those three fields and the NUL-padded pathname
region `[1008304,1008424)` transforms the complete author byte sequence into
the peer sequence. In stage 4 the respective stage-2 objects appear as a
direct import; the comparison explicitly accounts for their differing hashes.
This is a precise **byte-level** observation, not a proof of Lean's binary
format or that distinct object files are semantically interchangeable.

The prior warning-rejected author-e object was known to differ from the later
accepted author-h object, with the earlier attempt lacking direct input guards.
[`earlier_path.py`](earlier_path.py) now checks that their complete files have
the same length and differ at exactly one byte: the `e` versus `h` in the
embedded source path. This improves the diagnosis of the observed hash
difference but does not supply the missing historical guards.

[`capture.py`](capture.py) retains the compared source snapshots, receipts,
complete compiler logs, dependency outputs and successful comparison output
in [`observations`](observations/). The first captured comparison, before
generalizing its peer-ledger check to permit later stages, is retained with
its exact source in [`observations-pre-continuation`](observations-pre-continuation/).
The current comparison can be repeated with `python3 -I -S -B compare.py`
while both referenced `/tmp` overlays and their historical providers remain
available. Its checks are sampled and do not establish continuous filesystem
immutability, complete transitive project/package/dynamic ancestry, or either
nine-variable endpoint: only five of 104 stages have been compared here.
