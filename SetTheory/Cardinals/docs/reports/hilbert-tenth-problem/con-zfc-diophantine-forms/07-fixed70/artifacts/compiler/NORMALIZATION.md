# Exact controller and finite windows for the fixed ZFC equation

This directory removes the phrase “choose a machine for the r.e. set” from the
coefficient specification. Its input is the literal released K215 transition
table, not an unspecified universal-machine index. Everything here is a finite
construction. The enormous window list and integer coefficients are specified
by terminating finite recipes; they are not claimed to have been materialized.

## Source and trust boundary

The pinned ProveIt revision is
`cdd582bec13f908df3711fa9e05d1ddac368a5db`. The file
`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` has SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
It has states 0 through 214, halt 215, symbols 0 and 1, and a two-way tape.
Its initial tape is all 0, head position is 0, and initial state is 0.

The current K215 verification README states the closed endpoint
`Halt(K215,blank) iff ZFC has a finite derivation of falsity`. This directory
uses that inherited theorem. It does not freshly run Lean or Rocq, produce an
internal ZFC proof object, or decide whether K215 halts.

The helical local predicate below transcribes the source
`Computability/HilbertTenthProblem/Papers/verification/explore_helical_unary_tableau.py`,
SHA-256 `ca612f502b18b1b7a59c7c356938d108d00fb4fdaa7e719ccde1d667ef467823`.
Its soundness and completeness are the inherited helical tableau and marker
bijection theorems. The present addition is the explicit controller instance
and exact finite coefficient recipe, plus the elementary normalization proof.

## 1. The one-sided machine

There are 435 total states and ten tape symbols. The states are

* 0: start;
* 1: erase;
* 2: return;
* 3: nonhalting trap;
* 4: absorbing halt;
* `5+2q+s`, for `0 <= q < 215` and `s` in `{0,1}`: simulation states.

Symbol 0 is blank. Symbols 1 and 2 are used only by the unary loader. Pair
symbols encode two original binary tape cells:

| Pair `(p,n)` | Ordinary symbol | Origin symbol |
|---|---:|---:|
| `(0,0)` | 0 | 6 |
| `(0,1)` | 3 | 7 |
| `(1,0)` | 4 | 8 |
| `(1,1)` | 5 | 9 |

At physical position `-j`, the first component is original cell `j` and the
second is original cell `-j-1`, for `j >= 0`. Only physical position 0 has an
origin symbol. A simulation state with `s=0` reads and writes the first
component; one with `s=1` reads and writes the second. The unused component
and the presence of the origin flag are preserved.

For an original transition `(q,a) -> (q',a',D)`, the physical motion is:

| Side and original motion | Physical motion and new side |
|---|---|
| side 0, right | left, side 0 |
| side 1, left | left, side 1 |
| side 0, left, ordinary cell | right, side 0 |
| side 1, right, ordinary cell | right, side 1 |
| side 0, left, origin | stay, side 1 |
| side 1, right, origin | stay, side 0 |

The target is `5+2q'+s'`, except that original halt 215 becomes absorbing
halt 4. On symbols 1 or 2, every simulation state enters the trap. Every
otherwise unspecified transition also enters the trap without moving or
changing its symbol. The trap and halt preserve every symbol and stay put.
Thus the complete 4,350-row transition function is total and unambiguous.
In `normalized_machine.json` each row is
`[state, read_symbol, new_state, written_symbol, physical_motion]`, with motion
equal to -1, 0, or 1.

### Loader

The helical initialization supplies `t+1` consecutive 1s at positions
`-t,...,0`, with the head at 0 in the start state. Its six relevant rows are

| State | Read | New state | Write | Motion |
|---|---:|---|---:|---|
| start | 1 | erase | 2 | stay |
| erase | 2 | erase | 2 | left |
| erase | 1 | erase | 0 | left |
| erase | 0 | return | 0 | right |
| return | 0 | return | 0 | right |
| return | 2 | simulation `(0,0)` | 6 | stay |

After exactly `2t+4` transitions, the head is at 0 in simulation `(0,0)`,
the origin holds the flagged pair `(0,0)`, and every other cell is blank.
The loader never visits a positive position and cannot halt.

### Normalization theorem

For every `t >= 1`, this normalized machine halts on the stated unary
initialization if and only if the literal K215 table halts on blank input.

**Proof.** The loader invariant is immediate by scanning the `t` nonorigin
ones leftward, then the `t` erased cells rightward. For the simulation,
map an original head position `h` to `(-h,0)` if `h >= 0`, and to
`(h+1,1)` if `h < 0`. Represent the tape by the pair convention above.
The six motion cases in the table are exactly the images of `h -> h+1`
and `h -> h-1`; the two boundary cases exchange original cells 0 and -1
at the same physical origin. Every transition writes only the intended
component. Thus induction on the number of original transitions proves
the simulation invariant, including tape contents and state. No simulation
row reaches halt unless the corresponding original row does, and every
original halt reaches the absorbing halt. The invariant also shows the
simulator never visits a positive physical cell. QED.

The executable check covers all 3,440 possible simulation rows on the eight
valid pair symbols, including both side tags and both boundary cases. It
also checks 64 loader lengths. These finite checks supplement the induction;
they do not substitute for it.

## 2. Exact tile alphabet and window predicate

A tile is `(v,h,payload,phase)`. The alphabet, in this exact order, is:

1. `V=(1,0,None,None)`;
2. `H=(0,1,None,None)`;
3. `(0,0,(a,q),None)`, in lexicographic `(a,q)` order, where
   `a=0,...,9` and `q=None,0,...,434`;
4. the four initial-phase tiles L, I, Q, R, in that order, with payloads
   `(0,None)`, `(1,None)`, `(1,start)`, `(0,None)`, respectively.

There are exactly `2+10*436+4 = 4366` tiles. For a center and its left,
right, down, up neighbors, `local_valid` in `finite_window_constants.py`
is the full finite predicate. In prose, it imposes all of the following.

* Vertical boundaries propagate vertically and are not horizontally adjacent.
  Horizontal boundaries are not vertically adjacent and propagate to the
  right whenever both adjacent cells are nonvertical.
* V and H have no payload. Nonboundary cells have a legitimate symbol and
  either no head or one state.
* Exactly the cells immediately above H have an initialization phase.
  The phase edges are L to L/I, I to I/Q, Q to R, and R to R. A V neighbor
  on the left requires L, and one on the right requires R. The phase fixes
  the payload as above.
* A head cannot move through a neighboring V. If the next row is H, the
  head, if present, must be in halt.
* Otherwise, the next symbol is the center's written symbol, and the next
  state is the unique incoming head among a left head moving right, a center
  head staying, and a right head moving left. Two or more incoming heads
  are rejected. A neighboring V supplies a headless blank for this test.

A 3-by-3 window is allowed exactly when its central cross satisfies this
predicate. The four corner tiles are unrestricted. The fixed Start window is
centered at the last I, immediately left of Q; End is centered at the first I.
Their tile-index lists are in `compiler_metadata.json`. The normalized first
step is stationary and writes 2 while entering a distinct nonhalting state,
so these are precisely the inherited Start and End windows.

The allowed-window sequence is defined to start with Start and End, followed
by all other allowed nine-tuples in lexicographic tile-index order. The
generator `allowed_windows` is a literal terminating definition of this
sequence: at most `4366^9` predicate calls. No halting oracle or r.e. index
selection is hidden in this finite enumeration.

## 3. Exact compressed census

The literal predicate has 311,471,256,024,587 allowed five-cell crosses.
The four independent corners give exactly

`k = 113175624520853754856480928432`

allowed windows. The following partition explains the census.

| Center category | Allowed crosses |
|---|---:|
| V | 83,205,437,940 |
| H | 166,372,751,968 |
| Ordinary cell with ordinary next row | 309,557,950,136,775 |
| Ordinary cell with H next row | 1,663,727,607,000 |
| Initial cell with ordinary next row | 64,712 |
| Initial cell with H next row | 26,192 |

For nonboundary centers, partition the left and right neighbor choices by
the state they send toward the center, or by no incoming head. At most one
of those heads and the center's stationary head may be present. The up tile
must have the resulting payload. Its multiplicity is 3 for a headless blank,
2 for a headless 1 or the initial `(1,start)` payload, and 1 otherwise.
Multiplying these counts, with the exact phase and V-boundary exclusions,
is exactly the sum of the local predicate. This is the algorithm
`count_crosses`, and its six disjoint categories are recorded in the JSON.

Two 18-tile fixtures independently enumerate every one of their 1,889,568
crosses and agree with the factorized census. One is the stationary rejecting
fixture from the repository; the other exercises left, right, and stationary
motion, collisions, and boundaries. The actual 4,366-tile census is exact
integer arithmetic, not a finite sample estimate.

## 4. Marker semantics and absence of spurious accepting cycles

The local predicate's periodic soundness argument is inherited without
changing a clause. A Start occurrence lies on an initialization row. The
acyclic portion of the phase graph through Q forces vertical boundaries on
both sides in a horizontally periodic covering plane. The nearest such
boundaries determine a strip. H propagates across its interior, and vertical
periodicity gives a next H row. Between these boundaries lies a finite
rectangle initialized by `L^a I^t Q R^b`. The exact update and no-escape
clauses inductively preserve the unique genuine head. The last row's head
is halted. Periodic headless or unrelated components therefore cannot make
the distinguished Start into a false accepting computation.

For a genuine cyclic window word, each maximal I-run of length at least two
has one Start at its last I and one End at its first I. These maps are inverse
on the cyclic indices, even if the helical stride does not divide the period.
Consequently unique End implies unique Start. Start at index 0 and unique End
at index 2 belong to the same run, which has three I cells and therefore four
initial unary 1s including Q. This is the fixed input used by the main equation.
The loader erases these four 1s and starts K215 blank after ten transitions.

Conversely, a halting K215 run yields a finite normalized one-sided run.
Choose any sufficiently large strip width and any sufficiently large height,
independently. Place a vertical boundary at column 0, initialize at width-3,
and pad with absorbing halt rows. The inherited sheared strip construction
gives a helical cyclic word with Start at 0 and End at 2. Width and height
can in particular be chosen to be the powers of five needed by the modified75
compiler. This is why no numerical runtime bound on K215 is required.

## 5. Reproduction and attribution

Run `python3 k215_one_sided.py` and `python3 finite_window_constants.py`.
They require only the Python standard library and generate the two receipts,
the normalized literal machine, and the scalar compiler metadata. They do
not import or execute the repository's historical Python scripts.

The table and the inherited K215 mathematics retain the attribution in
`K215_NOTICE.md`. The helical predicate, compiler layout, and modified-mask
proof are ProveIt constructions; this packet does not assert priority for
them. New material follows the repository's MIT No Attribution terms.
The exact coefficient formulas are in `COEFFICIENTS.md`.
