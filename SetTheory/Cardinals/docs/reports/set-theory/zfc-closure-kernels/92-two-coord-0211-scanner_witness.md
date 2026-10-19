# Exact obstruction to the naive 244-state scanner contraction

The proposed contraction deletes old state 58 and changes the old-label row
`41 0 0 L 58` to `41 0 0 L 84`, leaving every other row fixed. It reduces the
scanner's zero threshold from eight to seven. The resulting table has 244
working states, but it loses the instruction-frame simulation at a shared
register-selection phase. This is an exact local obstruction, independently of
the separate question of the candidate's ultimate behavior from blank tape.

## Scanner lemma and the off-by-one suffix

For a threshold $k$, write the left-scanning states as $S_0,\ldots,S_{k-1}$.
On a one every $S_i$ preserves the symbol, moves left, and enters $S_0$.
On a zero, $S_i$ preserves the symbol and moves left into $S_{i+1}$, except
that $S_{k-1}$ enters the return state $R$. State $R$ scans right across zeros;
at its first one it moves right and enters the dispatcher. Every scanner
transition preserves the tape. Here $S_0=4$ and $R=84$. The baseline chain is

$$
(S_0,\ldots,S_7)=(4,6,9,13,19,29,41,58).
$$

A sufficient general scanner contract is as follows. Let the intended marker
be a one at coordinate $m$, with all cells to its left zero. Start in $S_0$ at
coordinate $s\geq m$. If the finite tape word on $[m,s]$ contains no $k$
consecutive zeros, the scanner eventually enters the dispatcher at $m+1$,
preserving every tape cell. Indeed, it cannot enter $R$ before reading the
marker. It then reads exactly $k$ exterior blank cells, enters $R$ at
$m-k-1$, and scans right to the marker. This is a sufficient contract, not a
necessary characterization: a run of exactly $k$ zeros immediately to the
right of the real marker also returns correctly.

During preparation of a CI/CD instruction, the gap after its PC is filled
with ones. Register selection changes the first post-PC cell to zero before
the shared return scan. If the PC has length $L$ and ends in

$$P=u1\,0^t,$$

then the scan reaches state $S_0$ at coordinate $L$, reading that extra phase
zero. The immediately preceding zero run now has length $n=t+1$, although the
PC itself has only $t$ trailing zeros. The cell at $L+1$ is still one. The
following trichotomy is an exact consequence of the scanner rows:

1. If $n<k$, the scan crosses these $n$ zeros and their preceding one, and
   continues in $S_0$ at $L-n-1$. This suffix causes no false return.
2. If $n=k$, after $k$ steps it enters $R$ on the preceding internal one at
   $L-k$. One further step enters the dispatcher at $L-k+1=L-t$.
3. If $n>k$, after $k$ steps it enters $R$ inside the zero run. It then scans
   right to the remaining gap one at $L+1$, entering the dispatcher at
   $L+2$ after $2k+2$ steps from the local start.

In cases 2 and 3 this is the wrong PC origin, because the displayed preceding
one is internal to $P$. If $P$ is entirely zero and the preceding one is the
real marker, case 2 is instead correct; this is why the marker exception
must not be suppressed when stating the lemma.

Consequently, a useful sufficient word condition for these marked scans is
that the PC's other zero runs have length less than $k$, while its trailing
zero run has length at most $k-2$. In particular, a seven-zero scanner needs
the marked instruction PCs to have at most five trailing zeros. This
statement concerns the local scanner. A complete changed-runtime proof must
also cover all other entry contexts and instruction effects.

## Literal eight-step witnesses

For $k=7$ and $t=6$, the candidate has the following exact local trace. Here
the coordinates of the six trailing PC zeros are $L-6,\ldots,L-1$; the
phase zero is at $L$; and the internal one is at $L-7$.

| Steps elapsed | State | Head | Read symbol |
|---:|---:|---:|---:|
| 0 | 4 | $L$ | 0 |
| 1 | 6 | $L-1$ | 0 |
| 2 | 9 | $L-2$ | 0 |
| 3 | 13 | $L-3$ | 0 |
| 4 | 19 | $L-4$ | 0 |
| 5 | 29 | $L-5$ | 0 |
| 6 | 41 | $L-6$ | 0 |
| 7 | 84 | $L-7$ | 1 |
| 8 | 96 | $L-6$ | 0 |

The baseline instead reaches state 58 at step 7. Reading the internal one
takes it left into state 4, so it continues toward the real marker.

`scanner_witness.py` checks the relevant rows and constructs three complete
instruction-frame executions using a header distance of 64 and one spare
register of value 1:

- Site 41, PC `11101001001000000`, CD on physical register 2, initially zero.
- The same site with that register initially one.
- Site 649, PC `1110100100101011010101000000`, CI on physical register 2.

The initial dispatcher is at coordinate 0, and the real marker at $-1$.
Both tables are executed from these full frames. They reach identical local
tapes at the displayed phase-zero window. The candidate then restarts at
coordinate 11 in the two CD cases and coordinate 22 in the CI case; the
baseline restarts at coordinate 0. The JSON records all initial and local
one-cells, all scanner states, and the exact numbers of literal steps needed
to reach the window. The omitted tape cells are zero.

This failure precedes the increment/decrement implementation and the
decrement zero/nonzero distinction. The mark-and-return phase is common to
CI and CD. Register values can change travel times and the marked register
region, but do not change the displayed PC/phase-zero scanner window.

## Site census and why it does not loosen this grammar search

The independent site census checks all 6,460 leaves and verifies that they
form a complete binary prefix tree. Exactly 50 PCs have a trailing zero run
of length six: 49 CD sites and one CI site. These are also exactly the 50 PCs
having a zero run of length six anywhere. Thus they represent 99 guarded
instruction cases. Comparison with the separate universal affine audit gives
an exact match to its 99 failures and 8,292 passes. There are no internal-only
six-zero examples in this particular program, so that census alone does not
establish their correctness.

Moreover, in any finite complete binary tree,

$$
\max_{P\text{ a leaf}}\operatorname{maxZeroRun}(P)
=\max_{P\text{ a leaf}}\operatorname{trailingZeroRun}(P).
$$

To prove the nontrivial direction, take an occurrence of $0^r$ in a leaf
path, stop at its final node, and continue only along zero edges until
reaching a leaf. The new leaf has at least $r$ trailing zeros. In the current
tree every leaf of a kind other than CI/CD ends in one. Therefore a bound of
five on CI/CD leaf suffixes already bounds every zero run by five. The
refined local suffix condition consequently supplies no larger feasible
grammar family under this preserved leaf-kind property. It explains the
failure precisely, but it is not a demonstrated new route to 244 states.

## Reproduction and scope

The checker uses only the Python standard library and imports no package
code. After extracting the included original baseline archive, run:

```bash
python3 -B scanner_witness.py \
  --package /path/to/zfc245-proof-20261018 \
  --output scanner-witness.json \
  --candidate-output rejected-scanner244.tm
```

If the separate affine audit result is available, add
`--affine-result /path/to/second_scan_result.json` to check its failure set
against the census. The generated candidate SHA256 is
`dd8f19b2764cf73e263a812e5fb466c11259f4d2dc650ac75a8d49c38053a0db`.
The generated table is an explicitly rejected candidate, not a proposed
consistency-equivalent machine. Neither an arbitrary-frame failure nor a
finite blank-tape run settles its ultimate blank-tape halting behavior.

Primary artifact sources are the original package's
`machine/zfc245_old.tm` and `certificate/sites_physical.json`, with the
independently produced `second_scan_result.json` used only for the optional
affine-result comparison. The source hashes are retained in the witness JSON.
