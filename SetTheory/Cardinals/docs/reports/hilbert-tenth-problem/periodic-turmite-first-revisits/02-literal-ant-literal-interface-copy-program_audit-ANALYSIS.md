# Independent exact compressed-program audit

Audited inputs are identified by SHA-256 in `receipt.json`. The source and data
were inspected directly; their pre-existing status fields and random-query
results were not used as evidence. No existing input or generator was changed.

**Result:** no semantic or index bug in the abstract adjacent-pair instruction
program. Its 958 positive-length nodes encode exactly **601,547,591 rows**.
Every row selects a pair with left index in **[0, 919]**, so its right index is
at most **920**, within active columns **0 through 957**. This is independent of
whether a literal-color physical atlas realizes those abstract instructions.

## 1. WORD grammar and semantics

Let the occupied logical prefix be `w[0:m]`; all cells beyond it may contain
arbitrary bits. Physical instructions act on two cells as follows:

- `DUP(p,q) = (p,p)`
- `NAND(p,q) = (1-pq,0)`
- `MOVE_RIGHT(p,q) = (0,p)`
- `MOVE_LEFT(p,q) = (q,0)`

For `WORD(DUP,m,i)`, require `0 <= i < m` and put `r=m-i`. Its first `r-1`
rows have pair indices `m-1, m-2, ..., i+1`, and its final row is `DUP(i)`.
Thus its length is `r`, its exact pair-index range is `[i,m-1]`, and its result
is the original word with `w[i]` inserted immediately after itself. Descending
moves preserve each suffix bit before its old cell is overwritten. It needs
exactly `m+1` prefix cells and does not require zero-filled slack.

For `WORD(NAND,m,i)`, require `0 <= i <= m-2`. Its first row is `NAND(i)`;
the remaining rows are `MOVE_LEFT(i+1), ..., MOVE_LEFT(m-2)`. Its length is
`r-1`, its exact pair-index range is `[i,m-2]`, and its logical result replaces
the adjacent inputs by their NAND, shifts the suffix one place left, and leaves
the old final cell zero. Length-one edge cases are included in both formulas.

These are direct affine descriptions of every row, not sampled descriptions.

## 2. SWAP grammar

The independent verifier records and checks the source's exact 24-operation
logical macro. Write `delta` for the change in logical word length before an
operation and `j` for its offset from the requested left index `i`.
Each constituent WORD has width `m+delta`, index `i+j`, and length

- `r + delta - j` for DUP
- `r + delta - j - 1` for NAND

The 24 length constants, in source order, are

`0,-1,1,0,1,1,2,0,0,0,2,1,2,2,3,1,1,0,-1,0,0,1,-1,-1`.

Their sum is 14, so `length(SWAP,m,i) = 24r+14`. There are 12 DUPs and
12 NANDs, the final length change is zero, and the peak change is four.
For every stage the logical operation is valid already when `r=2`; increasing
`r` only increases available suffix width. The local indices also remain within
the expanding two-bit subword, so the macro never consumes a logical suffix
value. An exhaustive four-assignment Boolean truth-plane evaluation gives
`(a,b) -> (b,a)`. This proves the swap for arbitrary prefix and suffix words.

The exact pair-index range is `[i,m+2]`, attained by the macro: apply the WORD
ranges above and maximize `delta-1` over DUP stages and `delta-2` over NAND
stages. The maximum is two. The exact peak logical width is `m+4`.

The physical opcode counts for SWAP are:

- DUP: 12
- NAND: 12
- MOVE_RIGHT: `12r-7`
- MOVE_LEFT: `12r-3`

The source's sequential decoder subtracts these strictly positive WORD
lengths. Therefore the selected WORD and residual are unique for every
`0 <= k < 24r+14`; the post-loop exception is unreachable on this domain.

## 3. COPY length, binary selection, and semantics

For `COPY(m,i)`, require `0 <= i < m`, with `r=m-i >= 1`. The initial DUP
WORD has length `r`. The inserted duplicate then moves right through the
original suffix by `r-1` SWAPs, indexed `t=0,...,r-2`. Each such SWAP has
width `m+1`, left index `i+1+t`, and residual width `r-t >= 2`.
The original prefix word is restored and the copied bit is appended at index
`m`. This remains true with arbitrary initial slack contents.

Define the prefix length of the first `t` SWAPs by

`P_r(t) = 12t(2r-t)+26t`, for `0 <= t <= r-1`.

This is exactly the source expression after collecting terms. Its increment is

`P_r(t+1)-P_r(t) = 24(r-t)+14`,

which is exactly the next SWAP length and is strictly positive on the domain.
Consequently the total COPY length is

`r+P_r(r-1) = 12r²+27r-38`.

For `r=1`, the total is one; execution always returns the initial DUP WORD and
cannot enter the SWAP decoder. Otherwise, after subtracting the initial `r`
rows, its residual `k` satisfies `0 <= k < P_r(r-1)`. The binary decoder begins
with `low=0`, `high=r-1` and invariant

`P_r(low) <= k < P_r(high)`.

Each branch preserves this invariant and strictly reduces `high-low`. At
termination, `high=low+1`; hence `t=low` is the unique valid SWAP index and
`0 <= k-P_r(t) < 24(r-t)+14`. The returned SWAP therefore exists, has a valid
adjacent pair, and receives a valid residual. There is no end-of-prefix or
last-SWAP off-by-one error.

COPY's exact pair-index range is `[i,m-1]` when `r=1`, and `[i,m+3]` otherwise.
Its exact peak logical width is respectively `m+1` or `m+5`.
Summing the SWAP counts gives exact COPY physical counts:

- DUP: `12r-11`
- NAND: `12r-12`
- MOVE_RIGHT: `6r²-6`
- MOVE_LEFT: `6r²+3r-9`

## 4. GATE and circuit references

The raw circuit has 24 inputs and 862 NAND gates. Every gate at logical width
`m=24+j` was independently checked to have `0 <= u,v < m`. The two COPYs append
`w[u]` at `m` and `w[v]` at `m+1` without changing earlier wires. The final
physical `NAND(m)` writes the new wire at `m` and clears `m+1`, so the logical
width becomes `m+1`. Self-input gates are covered without a special case.

The GATE length is the sum of those two COPY lengths plus one. Its three
intervals are contiguous and nonempty; the decoder tests the first, subtracts
its length, tests the second, and otherwise reaches exactly the final row.
Its exact pair-index range is `[min(u,v),m+4]`, and its exact peak logical
width is `m+6`. The second COPY always has residual width at least two.

Every requested output and the halt reference is in `[0,885]`, the completed
circuit's 886-wire prefix. The 25 output COPYs increase the logical width to
911. They preserve the 24 outputs at columns 886 through 909 and the halt bit
at 910. The observer's single `DUP(910)` reads that halt bit and copies it to
911. Its row index is exactly **601,515,562**.

## 5. Gather and scatter

For each input `j=1,...,23`, descending pair indices `40j-1,...,j` move input
column `40j` to column `j`, clearing intervening cells. Earlier gathered
inputs are below `j`, and subsequent source columns are above `40j`; neither
is disturbed. Input zero already occupies column zero. Initial values of
unselected columns do not affect this result. The length sum is
`39(1+...+23)=10,764`; pair indices range from 1 through 919.

For each output `j=0,...,23`, descending indices `886+j-1,...,j` move output
column `886+j` to `j`. Each block has length 886, totaling 21,264 rows. Earlier
gathered outputs lie below `j`, future sources lie above the current source,
and the halt bit at 910 is untouched. Pair indices range from 0 through 908.

For scatter, process `j=23,...,1` in descending order. Ascending pair indices
`j,...,40j-1` move output `j` to column `40j`; outputs already scattered have
larger destinations, while still-unscattered inputs have smaller indices.
Output zero remains in place. The length is again 10,764, with pair indices
1 through 919. Any overwrite of halt storage during scatter occurs after
observation and cannot change selected output bits.

## 6. Whole-program prefix and row_at proof

The independent verifier reconstructs all 958 nodes from the raw DAG and
explicit gather/output/scatter rules, and compares them to the serialized
nodes exactly. It computes every node length from the independent formulas
above, then constructs all 959 prefix entries. They match the JSON exactly,
begin at zero, and are strictly increasing. Their final value is 601,547,591.

For any legal row `k`, strict increase gives a unique `j` such that
`prefix[j] <= k < prefix[j+1]`. Therefore
`bisect_right(prefix,k)-1` is precisely `j`, including at every node boundary;
the residual `k-prefix[j]` is a legal local row. The component decoder proofs
above then prove the returned instruction correct for every row.

Exact physical counts are MOVE_LEFT 299,589,177; MOVE_RIGHT 299,226,786;
DUP 1,366,258; NAND 1,365,370. Their sum is the declared program length.

## 7. Exhaustive finite check and capacity

The verifier intercepts the production decoder's immediate recursive call in
memory, leaving the production files unchanged. It checks both endpoints of
every arithmetic branch interval: 958 top-level intervals, all 2,586 actual
GATE intervals, 83,783 COPY intervals across every occurring residual width,
and 20,112 SWAP WORD intervals covering all possible residual widths 2 through
839. WORD's 40,220 affine subintervals are checked at their extrema.

These are exhaustive interval certificates, not random or representative-row
sampling: comparisons in COPY use only thresholds `P_r(t)`, so every integer
inside a fixed half-open interval has identical comparison outcomes; its
residual is affine. The same argument applies to the strictly ordered WORD,
GATE, and program prefixes. Translating both `m` and `i` by the same amount
preserves every length and shifts every emitted index by that amount. Thus
normalizing COPY/SWAP to `i=0` covers every actual occurrence, not just one
chosen geometry. The algebraic proofs also cover all legal grammar parameters.

`node_bounds.json` records exact row intervals and pair-index extrema for
every compressed node. Group maxima for the left pair index are:

- Input gather: 919
- GATEs: 889
- Output COPYs: 913
- Observer: 910
- Output gather: 908
- Output scatter: 919

The exact highest touched column is 920. Consequently 921 physical columns
suffice for this abstract program, and the supplied 958 active columns leave
37 untouched columns at the right. The exact peak *compiler word* is **915**
cells, attained inside the last output COPY. The stored
`maximum_live_compiler_word=917` is a safe overestimate by two cells, not an
index error. Spatially sparse gather/scatter uses more columns than the compact
compiler word, which is why those ranges were checked separately.

This audit does not certify literal tile geometry, ant trajectories, marker
routing, or physical interface composition. Those remain distinct obligations.

Reproduce with:
`python copy/program_audit/verify_program_index_bounds.py`
from the atlas directory, or use the verifier's absolute path.
