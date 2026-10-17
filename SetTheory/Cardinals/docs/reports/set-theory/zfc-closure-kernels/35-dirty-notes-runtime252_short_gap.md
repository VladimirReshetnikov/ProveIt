# Bounded diagnostic for the 252-state runtime core's blank start

## Result and limits

This experiment does **not** produce a new consistency-equivalent blank-tape machine. It establishes a reproducible literal prefix and then a bounded continuation in the upstream symbolic executor's design model. It corrects a potentially misleading interpretation of the earlier all-start search: the unresolved common orbit is not established to be a simple forever-growing zero-tail loop. It enters substantial arithmetic of the register program.

The uniform gap bound 40 is sufficient for every instruction site in the published program. A smaller gap can work for particular instruction sites. We therefore checked the actual paths reached, rather than declaring every frame with gap below 40 malformed. Two forms of this check must be distinguished:

1. **Affine gap:** every represented zero run has length `n + c`, with one unknown `n >= 0`. A successful execution describes all larger gaps simultaneously. The prototype sometimes stops when it cannot peel an unknown-length run.
2. **Exact fixed gap:** the gap is the literal integer 32, so those gap runs have coefficient zero. Register blocks remain abstract, using the same upstream register-box summaries. This resolves some failures of the affine abstraction; it is not a full literal simulation of the registers or a new kernel theorem.

From the reproduced frame below, the fixed-gap design model completed **1,000,000 register instructions**, using **124 distinct local cases**, without reaching a root, overflowing the program counter, or failing a local contract. The gap stayed 32. This bounded result supplies neither nonhalting nor a consistency-equivalence theorem. No claimed new state record follows from it.

## Reproducible starting configuration

The table is the already known 252-state runtime core. Start with upstream `zfc_254.tm`, apply the public253 edits in old labels,

| State | Read | Write | Move | Target |
|---|---:|---:|---|---|
| 3 | 0 | 0 | L | 48 |
| 5 | 0 | 1 | R | 97 |
| 5 | 1 | 1 | R | 64 |
| 49 | 1 | 0 | R | 5 |

then delete old states 5 and 8 and redirect every target 5 to 64. There are 252 working states and 504 transition rows, with terminal old254. This is the runtime-only fold already identified by ProveIt source04, not a new table.

From blank tape, start old64 at position zero. At literal time **999,186**, the exact table is in old96, head at absolute coordinate 4. Its complete tape equals the following encoding:

- A marker 1 at position `head - 1`; all farther-left cells are zero.
- Program-counter path `1110100100101000101100110110` beginning under the head. Its length is 28.
- A header 1 at offset 32; all cells between the path and header are zero.
- Physical register order is `(wffstack, param1, axiomcode, scratch2, scratch1, prooflist, nextproof, topwff, param2)`.
- Their values are `(60, 4, 2, 4, 0, 0, 0, 0, 0)`.
- Each register block is `0 1^(value+1)`.
- There are 359 additional spare blocks. Spare indices 62, 63, 75, and 88 have value 1; the others have value zero. These are zero-based indices **after** the nine live registers.
- The entire remaining right exterior is zero.

The source register vector is therefore `(0, 0, 60, 2, 4, 0, 0, 4, 0)` in declaration order `(nextproof, topwff, wffstack, axiomcode, param1, param2, scratch1, scratch2, prooflist)`.

The script replays the complete literal prefix and verifies every nonzero tape cell against this description. In particular, the four nonzero spare blocks are preserved; they are not discarded when treating the initial segment as a register encoding.

## Affine failure and concrete check

After 641 register instructions, the affine executor first fails with `peel right symbolic run in 10`. At that point:

- The path is `11101001001010001100110110110`, of length 29.
- The operation is increment physical register 7, namely `topwff`.
- The gap is still 32; the path-to-header slack is three cells.
- The physical register vector is `(0, 4, 2, 10, 19, 0, 0, 0, 0)`.
- There have been 217 positive decrements, each appending one zero spare block.

The analogous affine case succeeds at gap 33. However, failure at 32 is **not** evidence of an actual tape collision: from the precise reconstructed frame at gap32, a full literal table simulation performs the expected instruction in **2,794 Turing steps**, returning the exact expected tape and head. The fixed-gap abstract-register case also succeeds. Thus the first obstruction is the prototype's handling of an unknown-length gap, not a demonstrated incorrect machine transition.

The literal check here begins from the reconstructed configuration after the design-model continuation. It is a full literal check of that one instruction, not an independent literal replay of all preceding accelerated register instructions.

## Bounded continuation with an exact gap

At the end of 1,000,000 register instructions from the starting frame, the exact-gap design model reports:

- Path `11101001001010010000110010`.
- Next operation: increment physical register 3, namely `scratch2`.
- Physical register vector `(0, 4, 2, 141692, 20, 0, 0, 180, 0)`.
- 285,761 positive decrements, hence that many appended zero spare blocks, in addition to the original 359.
- Header gap 32, absolute head 4.
- No root/overflow event.

These are **register-instruction counts**, not literal Turing step counts. The unary arithmetic and growing spare suffix make the latter substantially larger. We did not continue into an unbounded or unconstrained search.

A useful future route is algebraic acceleration of the particular source-level routines reached by this orbit, with checked local TM contracts at their actual gaps. A conclusion about the orbit still requires either an eventual safe root with adequate runtime gap or a genuine inductive divergence invariant. This diagnostic supplies neither.

## Reproduction and dependency scope

Run:

```sh
python runtime252_short_gap.py \
  --upstream /path/to/busy-beaver \
  --limit 1000000 \
  --output runtime252_short_gap.json
```

The expected upstream revision is `297ab8df7e5de329605c3875b4934643b371a5e3`. Only these three files are needed; the script checks their SHA256 digests before use:

| Upstream-relative path | SHA256 |
|---|---|
| `ZF/m254/machine/zfc_254.tm` | `d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb` |
| `ZF/m254/coq/tm/Prog254.v` | `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746` |
| `ZF/m254/tools/tm/symexec.py` | `5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d` |

The program tree is parsed from the actual 6,459-node `p254_tab`, and its register numbers are mapped to their physical tape order. The upstream prototype's register-box summaries are reused unchanged, with the known runtime252 transition edits. Exact fixed-gap checks replace only the gap-run coefficient with zero. Every distinct `(path, operation, branch, gap)` case reached is checked before it is cached and reused.

The earlier `orbit.json` and exploratory files in this directory are intermediate caches and are unnecessary for reproduction or inclusion in the report archive.
