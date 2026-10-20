# Both row-36 repairs fail at the first reachable source instruction

This is a concrete obstruction to applying the Source 146 bootstrap repairs to
the accepted K218 source and its existing register interpretation. It is not a
lower bound or an impossibility theorem for a redesigned source or simulation.

The tested 217-state core deletes state 301 and changes only `87/0` to `0 R 88`,
`88/0` to `0 L 51`, and `51/0` to `0 R 122`. The two further repairs set `36/0`
to `1 L 6` or `1 L 10`. Every other transition remains the accepted K218 row.

## The zero guard is actually reached

The accepted complete initialized tape has state 84, head −5, header 139, gap 80,
logical registers `[3,0,0,0,3,0,0,0,0]`, and 130 spares of value one. Its complete
277-cell support is taken from the published blank-startup record. The first
source occurrence is ordinal 0, address `000`, instruction `CD8`. Thus its zero
branch is reached before any source operation; no invariant of the accepted
source can exclude this interface.

`check.py` uses a newly written sparse simulator and literal tables. It neither
imports submitted code nor runs the full symbolic suite. The six traces are
preserved compressed, with complete ending supports in `result.json`.

| Table | First full source-frame endpoint | Steps |
| --- | --- | ---: |
| Accepted K218 | ordinal 2, `0100`, `CD0` | 1,242 |
| Initialized 217-state core | ordinal 2, `0100`, `CD0` | 1,242 |
| Core with `36/0 = 1 L 6` | ordinal 1, `001`, `CB1` | 1,232 |
| Core with `36/0 = 1 L 10` | ordinal 1, `001`, `CB1` | 1,232 |

All four encounter `36/0` at tick 459, head 140. The repaired endpoints have the
correct full register/spare tape but the wrong control bits: one at offset 2
instead of offset 1. From that wrong `CB1` endpoint, either repaired table takes
314 further steps to ordinal 9, `10000`, `CD8`, with registers still unchanged.

## The skipped fragment has a nonidentity effect

The accepted source occurrences 2–8 are:

```text
2  0100    CD0
3  01010   CI8
4  010110  CI6
5  010111  CC3
6  0110    CI0
7  01110   CD6
8  01111   CC2
```

Occurrences 2–5 repeatedly decrement register 0 while incrementing registers 8
and 6. When register 0 is zero, control goes to 6. Occurrences 6–8 increment
register 0 once before each test of register 6, consuming register 6 until its
zero branch exits to ordinal 9. Consequently, for arbitrary natural `n,m`, an
entry with `(R0,R6,R8)=(n,0,m)` exits with `(n+1,0,m+n)`; every other register is
unchanged. This follows directly by induction on the two loop counts.

For the actual accepted seed, the proper source reaches ordinal 9 with
`(R0,R8)=(4,3)`. The two repaired binary traces reach that same ordinal with
`(R0,R8)=(3,0)`. A finite 25-step source trace from ordinal 0 is in
`source-fragment.json`. Thus the extra `CB1` boundary is not harmless stuttering.

## Other uses and evidence boundaries

Source 146's delivered `research/source218/row36_usage/receipt.json` reports
4,218 generic cases using row `36/0`: both zero and positive cases of decrement
on registers 0,1,3,4,5,6,7,8, and increment cases on those same registers.
These are delivered census results on that packet's table/source; they were
read, not rerun or promoted to a fresh K218 census. The exact first-entry trace
above independently establishes the necessary reachable obstruction.

The two repairs are rejected for the unchanged accepted source contract.
This diagnostic does not assert that every altered seed or entirely different
source interpretation is impossible, nor that either repaired machine halts or
diverges on its own blank run. There is no reason to run a costly full runtime
suite for this already failing proposed contract.

## Independent finite replay

`replay.py` separately reconstructs all six literal traces and their entire tape
supports, and independently checks the source trace using subtree intervals.
It does not import `check.py` or execute any submitted checker.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/row36-repairs/replay.py \
  --repo . \
  --output /tmp/k217-row36-replay-fresh.json
```

The named output must be fresh. These finite traces justify the stated
counterexamples; they are not general runtime certificates.

Independent source review is preserved in [source-peer.json](source-peer.json); it read the diagnostic and recorded outputs without rerunning the candidate. The separate fresh [replay result](replay-result.json) checks all 5,576 recorded physical transitions and 25 source steps.

## A distinct two-context attempt

The follow-up [eight scan-clone diagnostic](scan-clones/README.md) finds an exact
bootstrap/runtime discriminator and proves a local unary-scan reuse lemma. Seven
reused scan states then fail at reached source frames; the eighth remains bounded
at 30,000 steps. Exact traces and the distant-prefix state-33 obstruction are
preserved separately.
