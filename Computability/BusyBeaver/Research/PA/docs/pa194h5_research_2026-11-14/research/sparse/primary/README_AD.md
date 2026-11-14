# Optional 194-state A/D register-allocation companion

The principal construction is `build194.py`. This companion preserves its
194-state decoder and complete 3,673-site source program, while exchanging
the physical tape blocks used for logical registers A and D.

## Reproduction

From this directory, run:

```sh
python3 build194_ad.py
```

This verifies the delivered bytes. To regenerate the three companion table
files before checking them, run:

```sh
python3 build194_ad.py --write
```

Use Python 3.10 or later without `-O`; assertions implement certificate
checks. Only the standard library and files in this release are needed.
The builder first checks the principal construction's source identity,
local folds, table binding and startup; it then performs all symbolic
instruction contracts for the companion. It writes
`evidence/pa194_AD.verification.json` without overwriting the principal
full-verification receipt.

## Literal changes and identities

Logical register order is `(N,T,W,A,D,H,X,Y,L)`. The original and new
logical-to-physical maps are:

```text
original: [6,2,0,4,3,7,8,5,1]
new:      [6,2,0,3,4,7,8,5,1]
```

Only three native transitions change:

| State / read | Principal action | Companion action |
|---|---|---|
| 17 / 1 | 0 R 32 | 0 R 48 |
| 144 / 1 | 0 R 48 | 0 R 32 |
| 161 / 1 | 0 R 32 | 0 R 48 |

The skip-chain entry 32 selects physical block 4; entry 48 selects block
3. All arithmetic-box transitions remain identical. These changes concern
the representation of the register store; they are not a renaming of
machine controls. The seven local reader folds are rechecked in the final
table after the router changes.

The native start and halt are 74 and 254. The dense table starts at 0,
has working controls 0 through 193, and halts at 194. It contains 388 rows.
`pa194_AD.labels.json` lists the native label for each dense label,
including the terminal halt label as its final entry.

| Artifact under `tables/` | SHA-256 |
|---|---|
| `pa194_AD.native.tm` | `2d65846b38081e6ca9b7572e784fcb362d8bd46fac0ea9cb2d35f791d4baa676` |
| `pa194_AD.tm` | `27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f` |
| `pa194_AD.labels.json` | `b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964` |

## Verification and proof transport

Let p and p' be the two maps above and let sigma exchange positions 3 and
4 in a physical file. Then sigma(v)[p'(r)] = v[p(r)] for every logical
register r. Increment, the zero test and positive decrement commute with
this identification; the remaining represented values are preserved. The
tail after the first nine physical blocks is unchanged by sigma, including
the one-valued spare appended by an increment.

The complete symbolic checks quantify over arbitrary register values and
an arbitrary spare tail. They establish 4,780 branch-sensitive contracts
with maximum 497 symbolic steps per case and 1,479,348 symbolic steps in
total. Those totals measure verification work rather than physical time
for arbitrary register inputs. The contracts implement the required
register update, next encoded address and spare-tail effect, and preserve
the untouched tape exterior. Every simulated nonhalting source instruction
has finite positive duration.

Literal execution from blank reaches the exact full source frame after
58,122 transitions, with dispatcher 84, head at -2, source site 25, logical
register vector `(2,0,0,0,0,0,0,0,0)`, and 26 one-valued spare blocks. The
whole finite-support tape is compared, not just selected cells. A and D
are both zero at this boundary. The principal startup takes 58,154 steps;
this difference does not assert a uniform speedup for later computations.

The store identity and positive simulations give primitive-recursive
translations of finite halting traces through the common source program.
For the reverse implication, a hypothetical physical halting time T is
covered by at most T+1 positive source blocks; determinism rules out a
physical halt within a certified nonhalting block. PA proves these finite
trace arguments by ordinary induction. Composing them with the same
supplied syntactic source calibration as the principal construction gives
PA-provable equivalence of this companion's nonhalting with Con(PA).

This is a mathematical proof transport supported by finite and symbolic
executable certificates. No newly compiled end-to-end Lean or Rocq theorem
is claimed. The A/D allocation technique appeared in a supplied 196-state
design; its composition with the new 194-state decoder is the additional
construction here. See the main report for the pinned corpus, source
calibration, proof provenance and broader comparison.
