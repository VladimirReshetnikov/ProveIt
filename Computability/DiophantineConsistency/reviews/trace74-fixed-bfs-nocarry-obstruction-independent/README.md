# Independent audit: fixed-payload no-carry obstruction

PASS for the exact external bit calculation in `research/trace74-fixed-bfs-nocarry-obstruction/`. We reran its checker, rehashed the retained beta and MC gzip/raw payloads, and matched the preceding scalar assignment J=1, F=3, C=q−3. The payloads give q=2^590069 and `MC mod 2^67 = 2^67−2`; hence `C−1=q−4 ≡ 4 (mod 8)` and `MC*J+1=MC+1 ≡ 7 (mod 8)`. Binary bit 2 is therefore one in both operands, so their natural binary `NoCarry` condition fails for this assignment. This is consistent with the existing `ArithmeticBinaryCarry.NoCarry` definition: at position 2 the two bits sum to 2, exceeding 1.

The assignment satisfies F+C=q and the separately checked scalar facts; no full graph output was evaluated. This calculation does **not** derive `NoCarry(C−1,MC*J+1)` from a positive 74 zero. Thus it does not establish or refute a fixed-port zero, decide the fixed-port guard, or prove 74/75 existence inequivalence. Connection of the retained external payloads to symbolic Lean ports and external JSON/file binding remains separate. No Lean was run.

Checker SHA `60aa48d0493825856a00d34053730e0208c4aff19e74c6e4febd30d1fc0802f8`, observation SHA `502788636f540fcaadbd8a4ca080afc198724eea044deb228ff1cf7334d69087`. Our independent checker and output are alongside.
