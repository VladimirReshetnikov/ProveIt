# Foundation and frontend findings at the 240-state frontier

The concrete alternative-frontend result is a **946-bit complete finite
equational packet**, with 14 equations, 215 both-side term nodes, 13 symbols,
three local variable slots and four-bit opcodes. It improves the inspected
Source 79 packet's 1,169 complete bits by 223 bits (19.08%). This is a packet
measurement and an ordinary model-theoretic calibration, not a smaller binary
Turing machine. The inherited raw-EPSC/ZFC calibration remains an explicit
dependency, and no new Lean/Rocq or internal PA proof is asserted.

The new structural specialization identifies class NAND `J` with native stack
cons `P`. Applying Source 40's earlier false-class witness-slice technique as
`Pick(x)=W(x,d)`, and the previously reviewed truth fusion `top=d`, crosses
the shared symbol/variable opcode capacity from 19 values down to 16. The
slightly longer equation term is more than offset by four-bit opcodes.

An alternate use of the same slice, `Q(a)=W(a,d)`, gives 950 bits. The slice
cannot be assumed to serve both roles simultaneously. The original longer
derived-Pick term combined with `J=P` and `top=d` gives 970 bits.

## Reproduce

```sh
python3 fuse_stack_packet.py
python3 verify_shared_semantics.py
python3 check_ground_rewrite.py
python3 ground_rewrite.py generated/stack_epsc_explicit_pick_cons_nand_truth_fused_spare_pick.json --max-code 65536
```

Run without `-O`. The first command regenerates ten comparison packets and
their metrics under `generated/`, performs two structurally different prefix
parses, rejects every strict truncation, compares exact decoded equations and
checks all 72 Boolean valuations of each packet's clause groups. It also
reruns Source 79's 2,080 stack and 16,384 formula regressions. The second command
tests the modified cons/NAND compiler, finite selector rules and the specific
spare-witness argument; its status is bounded transcription regression, not
a finite model of EPSC.

The third command verifies concrete ground-rewrite certificate controls.
The fourth is only a bounded experiment. The reference search has a complete
unbounded certificate enumeration mode (`--unbounded`), uses substitutions
for variables on both equation sides and admits arbitrary ground contexts.
Its Python implementation is an abstract semidecision specification, not
a measured binary Turing machine. Finite exhaustion is inconclusive.

Preferred exact files:

- `generated/stack_epsc_explicit_pick_cons_nand_truth_fused_spare_pick.bits`
- `generated/stack_epsc_explicit_pick_cons_nand_truth_fused_spare_pick.equations`
- `generated/stack_epsc_explicit_pick_cons_nand_truth_fused_spare_pick.json`
- `generated/verification.json`

The bit-character SHA256, excluding the terminating file newline, is
`19d0a84437a01f11dc6e53ccbcb5492ce1ca0748a8f8e4b354f36a52e0e8c340`.
All signature arities, equation delimiters and both ground endpoints are
included in the reported 946 bits. No macro definitions are omitted.

The proof and the scope of novelty are in `stack946_note.tex`. The broader
comparison against already-rejected alternatives is in `foundations_review.md`.
`foundations_survey_section.tex` is a compact includable survey for the main
report, with no preamble, bibliography or document environment.
Source snapshots and URLs are listed in `sources.json`; inherited licensing
and attribution are preserved. No repository file was changed.

The 946-bit count is an improvement of the complete equational packet.
Earlier Source 42 already has a 901-bit complete native clause packet, and
Source 44 reports an 881-bit native clause template with external signature
and arities. The companion review compares these accounting boundaries;
no global minimum across all codecs is claimed.
