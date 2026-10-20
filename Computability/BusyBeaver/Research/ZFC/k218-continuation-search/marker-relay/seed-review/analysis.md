# Relay 217: clean-frame and sound-seed boundary

The recorded clean frame after 81,103 blank steps is **not yet a sound proof-search seed**. It is at source ordinal 148, inside an AX pairing loop. The generalized seed argument comes from Source 146 (`ZFC_218_Research`), not Source 145, and applies at the complete source-root boundary. It permits arbitrary next-candidate number, additive parameter, and command list. It still requires theoremhood of the current formula, cached formula, and every decoded theorem-stack entry.

## Exact bounded source calculation

Starting from the reported logical registers

`[np,tw,ws,ac,d,h,s1,s2,pl] = [1,9,0,2,0,1,0,2,0]`

at ordinal 148, the first four instructions reach the loop at 141 with `tw=10,s1=0,s2=2`. The ordinary pairing loop computes `ws = 2 + P(0,10) = 67` and clears `tw,s1,s2`. An independent parser for the accepted 218 source checked every one of the first 629 transitions in Drop's stored source trace:

| Source steps | Ordinal | Logical registers |
| ---: | ---: | --- |
| 0 | 148 | `[1,9,0,2,0,1,0,2,0]` |
| 613 | 154 | `[1,0,67,2,0,1,0,0,0]` |
| 629 | 161 | `[1,2,67,2,0,1,0,0,0]` |

Here `P(10,1)=67`, `P(1,0)=1`, and `10 = wal 0 F = 4*P(0,1)+2`. Thus the decoded stack is `[Q₀(F), F, 0, …]`. In particular the ordinary `Inv` theoremhood premise for this stack would imply a derivation of falsum.

## Ordinary macro interpretation

The inherited AX decomposition identifies ordinals 135–161 with `par3` and the suffix beginning at 161 with `f305`. The state at 161 is also what the normal AX macro would reach from `np=1,tw=F,ws=0,ac=2,d=0,h=F,pl=0`: `par1/par2/wal` form `Q₀(F)`, then `par3` pushes it above the old `F`.

The checked-source statement `L2Axioms219.e305` describes this suffix as retaining the supplied stack beneath the eight generated native row instances. Under the inherited ordinary macro correspondence, its eventual command-root state therefore has `np=1,pl=0,d=h=0`, current formula `bundle(0,1,2)`, and stack `[rho1(0,1),rho2(0,1,2),…,rho8(0,1,2,0),Q₀(F),F]`. The eight row instances are axioms; that fact does not sanitize the last two entries.

This is an ordinary source-level use of the retained macro contract. The maintained `Dag219` literal word differs from accepted primary 218 through inherited instruction commutations/reassociations, so this review does **not** claim literal whole-word/CFG equality or a freshly compiled Lean transport theorem.

## What follows, and what does not

The Source 146 generalized seed theorem cannot certify this state. In its soundness direction, `Enum222.Inv` demands `C222 tw`, `C222 h`, and `Good ws`; `Good ws` quantifies over every stack tail. The arbitrary initial `pl` is a command list, not an arbitrary theorem stack. The completeness prefix `START_U` resets the additive parameter/cache, but pushes the old current formula and generalizes the old cache rather than discarding all stored formulas.

No conclusion about eventual blank halting follows solely from these bad intermediate entries. The deterministic continuation might discard them or might keep them forever below inaccessible stack prefixes; either claim needs a new argument. A future sound-seed claim must exhibit a complete source-root boundary satisfying an appropriate theoremhood invariant, or prove a different invariant that safely excludes the contaminated tail. Separately, the modified binary table still needs a complete runtime justification. Twenty matching initialized frames and a finite blank continuation are not such a certificate.

`review.py` reads literal source data and the already recorded trace; it invokes no supplied runner or Lean compiler. It checks only the first 629 source transitions and elementary pairing identities. The physical 81,103-step claim and full-tape representation remain attributed to Drop's evidence.
