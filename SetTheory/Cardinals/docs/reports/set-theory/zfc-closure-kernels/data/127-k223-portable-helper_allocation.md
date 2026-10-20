# The one-state allocation saving

The four physical states 11, 26, 37, and 162 have source-decoder capacity available after the conditional-K source change. They are not globally unreachable or unused engine states. Their following arithmetic/helper transitions must remain fixed:

| state | read | write | move | next |
|---:|---:|---:|:---:|---:|
| 11 | 0 | 0 | L | 26 |
| 26 | 0 | 0 | R | 37 |
| 26 | 1 | 1 | R | 38 |
| 37 | 0 | 0 | R | 17 |
| 162 | 1 | 0 | L | 27 |

Let A be the newly changed source chunk with physical entry 142, and let B be the unchanged chunk with physical entry 38. Four successive new source nodes have shapes

1. X = (CD3, A)
2. Y = (X, B)
3. Z = (Y, CB1)
4. W = (CD3, Z)

The compatible allocation is X → 37, Y → 26, Z → 162, W → 11. Its complete physical rows are:

| state | read 0 | read 1 |
|---:|:---|:---|
| 37 | 0 R 17 | 1 R 142 |
| 26 | 0 R 37 | 1 R 38 |
| 162 | 0 R 26 | 0 L 27 |
| 11 | 0 L 26 | 1 R 162 |

The listed fixed engine rows are unchanged. The source-specific primitive entries and whole prefix-restoring decoder paths are checked against every corresponding source occurrence; the full runtime proof separately validates every guarded instruction on unbounded frames.

Choosing state 11 greedily for X consumes its compatible CD3 entry but gives Y children (11, 38). State 26 has both rows fixed to (37, 38), so it cannot implement Y. The greedy allocator leaves 26 without a source role and allocates a new state for Y. Giving X to 37 instead enables the fixed two-child decoder 26, and 11 can still implement W later.

All 24 orders of these four helper-state choices were tested. Exactly 12 place 37 before 11 and yield a 224-state prefold table; the other 12 yield 225. There are only two distinct byte-level tables, and all 24 pass intended decoder-prefix binding checks. The detailed census is in helper_order_census.json. The chosen reproducible order is 162, 26, 37, 11.

Both table families admit the same all-tape local fold 18→180. The successful allocation therefore yields 223, with state 180/read 0 = 0 L 119 and state 180/read 1 = 1 R 192. This last fold is independently rechecked by build.py, rather than inferred from the allocator census.
