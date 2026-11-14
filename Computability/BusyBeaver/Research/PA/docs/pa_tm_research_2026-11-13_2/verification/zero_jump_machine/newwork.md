# Forced-zero forward jumps: a positive 196-state result and a failed fold

## 1. Reference machine and conventions

The input is the James Chang PA196 machine imported at ProveIt commit `1fe9b29810bfe3d0e507146d65f6b97692e7444a`. Its original numeric table has SHA-256 `e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`; `Program.lean` has SHA-256 `8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872`. All inputs are local and pinned in `reference_manifest.json`.

The source has 3,812 leaf occurrences. A source configuration consists of a site index and nine natural-number registers. The clean seed is site 25 with register vector `(2,0,0,0,0,0,0,0,0)`. Logical register indices are mapped to physical register positions by `(6,2,0,4,3,7,8,5,1)`. Dense control labels come from `PA196/Conjugacy.lean`: dense start 0 is native 74, dense root 75 is native 84, and dense terminal 196 is native 254.

The verifier resolves source control flow twice. The first resolver applies binary successor and cuts in a source path. The second uses the first and last leaf ordinals in ancestor subtrees. Equality of the two full control-flow graphs is checked.

## 2. The finite inductive invariant

For a register vector `r`, let `mask(r)` have bit `j` set exactly when `r[j] > 0`. The abstract configuration is `(pc, mask)`, with `0 <= pc < 3812` and `0 <= mask < 512`. Increment sets a bit. A zero decrement follows its zero successor without changing the mask. A positive decrement follows its positive successor and admits both possibilities for its resulting bit. Jumps preserve the mask.

Every concrete source transition is represented by one of these abstract transitions. Starting with `(25,1)`, a finite worklist produces 274,880 pairs at 3,810 sites. A separate pass checks initial inclusion and every successor edge. The sorted canonical JSON representation has SHA-256 `604a7915edb973658c1be8655751824a9424d26da180e45254cd82e13007b8ff`.

This is an inductive invariant, not a long bounded source run. Induction on the concrete step number therefore places every source execution from the seed inside the set. Sites 3774 and 3775 are absent. Fourteen `breakTo 1` sites have one or more forced-zero registers; the receipt lists all of them. In particular, at site 26, registers 3, 6, and 7 are zero.

The original instruction at site 26, path `100001`, is a jump to site 34. Replacing its source opcode by decrement of register 6 gives a zero successor of 34 and positive successor of 27. The positive successor is impossible under the invariant. Thus the substituted source step preserves the original control successor and all register values at every reachable configuration. This argument uses only natural-number arithmetic and finite membership checks; it does not assume consistency of PA.

## 3. A literal implementation that actually works

Source opcode equivalence alone is insufficient: the literal interpreter entry depends on the surrounding tape. We therefore checked whole symbolic source contracts rather than assigning a leaf-state number from an opcode name.

The positive construction changes one literal transition:

| Row | Original action | New action |
|---|---|---|
| Native `27/1` | `0 L 40` | `1 R 21` |
| Dense `27/1` | `0 L 39` | `1 R 21` |

No working state is added or removed. There are 196 graph-reachable working states and 392 defined rows. The unique undefined terminal is dense 196.

The symbolic verifier uses the register-block definitions and four engine summaries from `M6/Runtime.lean` and `M6/Native.lean`; the 45 required table rows are checked unchanged. A run segment represents a length affine in an arbitrary nonnegative gap parameter, and a register-file box represents arbitrary natural register values and a valid spare tail. Thus success is uniform in these values, rather than evidence from a finite sample of small registers.

All 4,959 source cases pass for `zerojump196.tm`. Only site 26 uses the additional hypotheses that logical registers 3, 6, and 7 are zero. Every other source case has the original unrestricted contract, or its original zero/positive decrement branch hypothesis. Every successful source case contains at least one literal transition. The source halt case reaches the literal terminal.

Separately, an exact finite-support tape simulation starts with every cell blank, state 0 and head 0. After 58,402 transitions it reaches the original clean seed: root state 75, head -2, gap 48, logical registers `(2,0,0,0,0,0,0,0,0)`, and 26 spare registers all valued 1. The checker compares the entire finite set of nonblank cells, not just a prefix or decoded register projection. The baseline reaches that seed in 58,154 transitions.

Consequently, composing these uniform nonempty instruction simulations proves that the positive 196-state variant follows exactly the original source computation after its finite startup. A finite source halt yields a literal halt; an infinite source run yields an infinite literal run. Any proved consistency characterization of that exact source transfers through this simulation. This is a mathematical relative correctness result. The packet does not claim that it rebuilt a formal Lean proof of the transfer or supplied the previously missing direction of a PA endpoint.

## 4. Exhaustive local synthesis within a stated grammar

We also varied the one action at native `27/1` over both writes, both directions, and all 197 existing dense destinations including the terminal: 788 possibilities. For each choice the same complete source-26 contract was checked, with a fuel limit of 1,024 symbolic steps. Exactly twelve actions are accepted. Every accepted action also reaches the exact original blank startup seed.

| Native action | Exact startup steps |
|---|---:|
| `1 L 9` | 58,432 |
| `0 L 10` | 58,114 |
| `1 R 17` | 58,366 |
| `1 R 21` | 58,402 |
| `0 L 40` | 58,154 |
| `1 L 77` | 58,408 |
| `1 L 87` | 58,474 |
| `1 L 93` | 58,116 |
| `1 L 103` | 58,116 |
| `1 R 103` | 58,466 |
| `1 R 113` | 58,156 |
| `0 L 302` | 58,154 |

The synthesis claim is exact for the finite enumeration and this symbolic acceptance procedure. The procedure is sound but is not claimed complete for all semantically correct replacement actions. The full 4,959-case runtime check in this packet is performed for the chosen `1 R 21` construction; the other eleven entries have their individual site-26 contract and startup checked.

## 5. Why the tempting 195-state construction is rejected

The false start used native `27/1 = 1 R 62`, based on an apparent register-7 decrement entry. It then folded native state 27 into native state 46, redirecting all incoming edges and setting native `46/0 = 0 L 81`. In old dense labels, it deletes 27, keeps 45, and sets `45/0 = 0 L 72`. This leaves 195 working states.

The decoder entry is context-dependent. Native 62 moves back and rereads the preceding leaf bit. The existing register-7 decrement enters with a left-child bit zero; site 26 enters with a right-child bit one. At site 26 the proposed transition instead acts as an increment of logical register 6 followed by continuation to site 27. A fold that simulates this wrong parent cannot repair the mistaken source interpretation.

An exact isolated counterexample begins at site 26, gap 48, all nine registers zero, and one spare register valued zero. The correct jump reaches site 34, with identical registers and spare, after 120 transitions. The changed 196-state parent and the folded 195-state table both reach site 27 after 558 transitions, with register 6 equal to one and spare list `(0,1)`. Every nonblank cell of each endpoint is recorded and checked. This refutes the advertised local contract without relying on a symbolic failure alone.

The same defect is also witnessed during the folded machine's actual blank execution. At transition 54,392 it is at a clean site-26 frame with gap 52, registers `(3,0,0,0,0,1,0,0,0)`, and 32 one-valued spares. At transition 55,186 it reaches site 27 with registers `(3,0,0,0,0,1,1,0,0)` and 33 one-valued spares. The required zero-decrement step would instead jump to site 34 and preserve all registers. The verifier independently reconstructs both complete tapes from the blank input.

The 195-state table satisfies the other 4,958 symbolic source cases but fails this one. It is therefore excluded from the positive constructions. These counterexamples disprove the claimed implementation of this source; they do not prove that the rejected table halts on blank input, nor rule out every unrelated interpretation one might try to attach to it.

## 6. Boundary of the result

The positive result is a rigorously checked new 196-state source-preserving variant and a catalogue of local replacement actions. The negative result prevents an attractive but invalid 195-state claim. Neither is a proof that 196 states are minimal. The wider research searches and their finite grammars are reported separately in the parent comparison packet.
