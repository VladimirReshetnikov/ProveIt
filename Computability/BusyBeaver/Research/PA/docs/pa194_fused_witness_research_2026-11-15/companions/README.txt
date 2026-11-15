THREE NEW PHYSICAL COMPANIONS OF SYMMETRIC / FUSED WITNESS MACHINES

The complete main construction is PA194FW (in the main report). This
subpacket supplies three further 194-working-state machines:

  PA194FW_MF
  PA194H5XS_MF
  PA194JH5XS_MF

Each is a deterministic binary machine with one two-way tape, blank-zero
input, head at coordinate zero, dense initial control 0, working controls
0 through 193 and separate terminal label 194. Each table has 388 rows in
the format state read write L/R next. Native initial control is 74, native
terminal control 254. Native 194 remains a counted working control.

The MF transformation is inherited from the immediately prior research
packet. Its application to these three exact parents is new. It combines
two guarded three-to-one physical shortcuts with a separate marker and
history selector. One reader is removed and one control is introduced,
so the total stays 194. No source-calculus axiom or command is changed by
this physical transformation. A full relative argument applies from the
common blank start and proves in iPRA:

  H_parent(t) implies H_child(5t);
  H_child(t) implies H_parent(3t).

Here H is the primitive-recursive absorbing halting-by-time predicate.
Consequently each child has the same blank-halting/nonhalting property
as its exact parent. The new relative theorem makes no PA-consistency
assumption. Its written proof is proof/symmetric_mf_relative.tex.

For H5XS_MF and JH5XS_MF, the absolute PA-consistency calibration is the
explicit written dependency retained in the full upstream symmetric
witness packet. For FW_MF it is the new PA194FW source/physical theorem
in the main report. This subpacket is not a new completed end-to-end Lean
or Rocq calibration proof. Finite replay is supporting evidence for the
uniform written table identities, not an extrapolation to nonhalting.

VERIFIED TABLE IDENTITIES

PA194FW_MF
  ea777e7d339394a6de12f01ebf3c6e9e913cffdee909f6b0f63f81a7ea62f52f
PA194H5XS_MF
  628ddeaab91662d352ab807e5f5ec61bf84d4c18a12fa5a98bf14a55f705f484
PA194JH5XS_MF
  02f53fd4acac7ed2f0d0a635c7548aac5292f06cc5da5389f44b80dcfc2f05af

All three complete blank startups take 57,812 child transitions, against
57,768 in their parents, reaching native state 84, head -2, and the exact
entire inherited source frame. The primary physical register tuple is
(0,0,0,0,0,0,2,0,0), followed by 26 unit spare registers. The checker
reconstructs every one-cell and verifies the zero exterior.

The independent verifier checks 24,832 radius-three state/windows in each
parent and accelerated table, 384 unchanged conjugated rows, 12 acceleration
windows and four history cases with clocks 5, 1, 3, 1. It then verifies
10,000 additional accelerated-parent steps in complete tape synchrony.
This interval uses the 26/1 shortcut ten times and the 301/0 marker case
once, so the changes affect recurring execution.

OFFLINE REPLAY

Python 3.10 or later, standard library only, with assertions enabled:

  python3 -B build.py --output /absolute/path/new-output-directory
  python3 -B verify_independent.py --output /absolute/path/check.json
  python3 -B verify_novelty.py --output /absolute/path/novelty.json

The builder is deterministic. It reads the exact frozen inputs and
regenerates dense/native tables, dense/native bijections, complete seed
tapes and finite receipts. verify_independent.py imports no constructor
and checks the distributed machines. The generic builder and independent
verifier are copied unchanged from the prior MF packet; their two-machine
historical docstrings refer to that original use. The input specification
here deliberately contains all three new companion constructions.

verify_novelty.py checks all stored comparison representatives against
their byte and canonical identities. It compares the primary PA194FW and
all three companions under arbitrary state renaming and root choice,
tape reflection, global symbol exchange, and ignored terminal-entry
write/move decorations. Bit exchange is a stronger structural comparison,
not a claim of zero-blank semantic equivalence. A positive control applies
all these transformations simultaneously. All four new graphs are mutually
distinct. The precise pinned corpus coverage is in the comparison manifest
and the current-corpus report. Search-only and rejected tables are retained
in the comparison corpus and are never counted as proved consistency
machines merely because their row count is 194.

ATTRIBUTION AND CONTENTS

NOTICE.txt and PROVENANCE.json give source pins and attribution.
references/symmetric_witness_parent.zip is the exact complete upstream
parent packet, including its transitive written proof ancestry.
inputs/ contains the exact parents, source sites and seed certificates.
machines/ contains all three children and local proof certificates.
verification/ contains completed independent and novelty receipts.
comparison/ contains the offline structural comparison representatives.
proof/symmetric_mf_relative.tex is the complete new relative proof.
Original licenses are retained in licenses/ and the parent ZIP.
