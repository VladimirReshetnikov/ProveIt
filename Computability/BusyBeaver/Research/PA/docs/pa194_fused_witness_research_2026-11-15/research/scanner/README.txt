BOUNDED LOCAL SCANNER REUSE SCREEN

Input: original PA194 from the pinned pa194_conpa_2026-11-13 packet.
Native input SHA256:
e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54
It is identical to research/physical/primary194.native.tm;
the physical supplement records the full provenance.

Run python3 -B scanner_reuse.py from any working directory. The program
rewrites receipt.json with the deterministic search result.

For each of six scanner controls it tests all 193 other controls as
bounded substitutes for one old transition. It allows the known right-
hand zero history and all assignments to seven other displayed bits.
Every simulated path must stay within the finite cylinder. Complete
tape, head and successor-state equality is required, with at most 40
local transitions and no reentry into the removed control. No candidate
passes all cases. This proves no universal state lower bound; other
invariants, longer paths, different sources and tape encodings are outside
the screen. The input is not the new fused-witness machine.
