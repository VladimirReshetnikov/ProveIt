# Expanded compact/iPRA rebuild: stopped at stage 285

Stages 277–284 compiled without warnings, including the re-pinned stage 276
source correction in their prior guarded prefix. Stage 285,
`ZFCinPA.BaseCertificate`, exited 1 in 54.281 seconds with kernel excessive
memory errors on three declarations and subsequent unknown-identifier errors.
The latter arise after those declarations fail; this is not a mathematical
counterexample. No stage 285 object or later receipt was produced. Source and
direct dependency guards remained unchanged.

The failed Lean command used `-M3000`. During this specific stage, eleven
five-second samples saw a maximum RSS of 3,066,928 KiB, at most one Lean
child and minimum MemAvailable of 17,269,148 KiB. Samples can miss short
peaks or overlap. Runner SHA-256 is
`73f9956a01818dc013d55eb43fe22e1d8838a8f2768ff3c3462ea39a18b95918`;
the full error log and terminal receipt are retained. The author prefix through
284 is not an iPRA endpoint, independent replay, or full provider audit.
