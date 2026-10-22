# Explicit K215 input for the fixed polynomial compiler

Snapshot: `cdd582bec13f908df3711fa9e05d1ddac368a5db` of
`VladimirReshetnikov/ProveIt`. This note supplies a finite machine and window
specification; it does not claim that its enormous window list or compiler
numerals were expanded.

## 1. The exact upstream endpoint

The maintained machine is the literal binary table `candidate-k215/k215.tm`,
SHA-256 `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
There are 430 rows, working states 0 through 214, initial state 0 on the
all-zero two-way tape, and halt state 215. The only row entering the halt is
`68 1 1 R 215`.

The source theorem is:

```
KEndpoint215.blank_halts_iff_zfc_refutation :
  BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot
```

The candidate README states the ordinary mathematical result
`ZFC proves: not Halt(K215,blank) iff Con(ZFC)`. The verification README
carefully distinguishes this from its external Lean/Rocq theorems: no
internal PA derivation or proof encoded in the object's own ZFC syntax is
included. Lean's endpoint depends only on `propext`, `Classical.choice`,
and `Quot.sound`; Rocq's endpoint reports are closed. Those are upstream
records, not builds rerun by the current construction.

The ordinary transfer needed here is formalizable in ZFC. Its numerical
calculus is inductively generated over the natural numbers; the
set-theoretic calibration uses first-order completeness, countable/set
models, relative constructibility, reflection, and quotient constructions.
These do not require a proper-class model or an inaccessible universe.
The subsequent folded simulation and finite-window constructions use only
finite combinatorics and natural-number induction. Formalizing the complete
new arithmetic endpoint in Lean/Rocq is additional work.

Relevant pinned files and Git blob hashes:

| Path below `Computability/BusyBeaver` | Git blob SHA-1 |
|---|---|
| `Research/ZFC/candidate-k215/k215.tm` | `27b9a81b10b8f5dff712592695882c3315cfcdec` |
| `Research/ZFC/candidate-k215/README.md` | `2768ef3f05b6b0a7415aa2194e8a92c5ef645f06` |
| `Research/ZFC/k225-formal/verification/k215/README.md` | `e5bdaf20b21e87abf456d9659896da27e0c74583` |
| `Lean/BusyBeaver/ZFC/KEndpoint215.lean` | `c3bf472b1b612da640407984b834f4e6f802a542` |
| `Lean/BusyBeaver/ZFC/KEndpoint.lean` | `bdf3a570fe02e5e0becf6c12f562957cf03fc8d5` |
| `Lean/BusyBeaver/ZFC/KCode222.lean` | `74b23e1cd0c5852d6a2ffe65009fffa910e72bdb` |
| `Lean/BusyBeaver/ZFC/KUpper222.lean` | `8b5cac6cf90d224535872baea7766d2c26948821` |
| `Lean/BusyBeaver/ZFC/Enum222.lean` | `7d94b3fd653fc4dbb2902d6d30ca8762b0cfd9f1` |
| `Lean/BusyBeaver/ZFC/Seed222.lean` | `a4a8027d7ba476ecc10da75ff0673e8d5e4b20cf` |

Each has the canonical pinned URL
`https://github.com/VladimirReshetnikov/ProveIt/blob/`
`cdd582bec13f908df3711fa9e05d1ddac368a5db/` followed by its full repository path.

## 2. A fully specified one-sided normalization

Use physical positions 0,-1,-2,... . At physical -k store the ordered pair
of original bits at virtual positions k and -k-1. The physical origin has
a flag carried by its tape symbol. The eight symbols are exactly:

| Symbol | Positive bit | Negative bit | Origin flag |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 1 | 1 | 0 | 0 |
| 2 | 0 | 0 | 1 |
| 3 | 0 | 1 | 0 |
| 4 | 1 | 1 | 0 |
| 5 | 0 | 1 | 1 |
| 6 | 1 | 0 | 1 |
| 7 | 1 | 1 | 1 |

Control states 0,1,2,3,4,5 are respectively START, AFTER, ERASE, RETURN,
SINK, HALT. State `6+2q+side`, for `0<=q<215` and `side in {0,1}`, simulates
K215 state q on the nonnegative/negative half. Total: 436 states, including
the absorbing HALT. All 3488 transitions are defined by the supplied
`NormalizedK215.delta`.

On an input of n>=3 consecutive ones at positions 1-n through 0, START
writes symbol 2 and stays at position 0 in AFTER. AFTER moves left into
ERASE. ERASE changes each 1 to 0 while moving left, then on the first 0
turns right into RETURN. RETURN crosses the cleared zero cells, encounters
the origin symbol 2, and stays there in simulation state `(q=0,side=0)`.
This takes exactly 2n+2 steps. Any unexpected initialization symbol enters
SINK. The first step is precisely the stationary distinguished step
required by the retained fixed-window construction.

For a simulation step, read and update the selected bit of the pair and
apply the matching K215 row. On the nonnegative half a virtual right move
is a physical left move; on the negative half a virtual left move is a
physical left move. A move toward the origin is a physical right move,
except at the origin, where it switches the selected half and stays. Thus
virtual moves 0 to -1 and -1 to 0 are stationary half switches. A K215
transition to 215 becomes a transition to HALT; HALT preserves every
symbol and stays forever.

### Simulation invariant and theorem

After initialization, for every virtual coordinate j>=0 the first track
at -j is the original cell j, and the second track at -j is the original
cell -j-1. The origin flag holds exactly at physical 0. If the virtual head
is j>=0, the physical head is -j and side=0; if j<0, the physical head is
j+1 and side=1. The original and simulated control labels agree through
`6+2q+side` until acceptance.

Inspecting each of the two sides, two virtual directions, and the
origin/interior case proves that one simulation transition preserves this
invariant. Only the appropriate track bit changes. No physical head ever
enters a positive coordinate. Induction therefore proves, in ZFC and in
much weaker elementary theories, that for every n>=3 the normalized
machine accepts its n-one input iff the exact K215 machine halts blank.
The normalized accepted set is consequently either all positive inputs
or the empty set; its definition never consults which case actually holds.

## 3. Exact finite tile and window alphabet

The supplied local predicate is the retained helical-tableau predicate,
with the same coordinate convention (row -1 precedes the center and
row +1 succeeds it). Tile IDs are fixed in this order:

1. V and H, IDs 0 and 1;
2. no-phase payload tiles `(symbol,head)` in lexicographic order, with
   symbol 0 through 7 and head `None,0,...,435`;
3. the four initialization phase tiles L,I,Q,R, with payloads
   `(0,None),(1,None),(1,START),(0,None)`.

The exact original tile alphabet size is `2+8*437+4=3502`. The phase graph
allows LL, LI, II, IQ, QR, RR. The first initialization tile next to V
must be L and the last must be R. Noninitial rows have no phase. V is
uniform vertically; H propagates horizontally only between non-V cells.
The last interior row may contain only an accepting head, and no head
may escape through V. Between consecutive interior rows the ordinary
radius-one transition rule is exact and rejects multiple arriving heads.

The distinguished Start and End 3-by-3 windows, listed row-major by tile
ID, are:

```
Start = (1,1,1,3499,3499,3500,439,439,878)
End   = (1,1,1,3498,3499,3499,2,439,439)
```

Start is centered on the last I just left of Q; End is centered on the
first I. Both local predicates were checked. Define the complete window
list by placing Start first, End second, and then all other 9-tuples in
`{0,...,3501}^9` whose center clause passes, in lexicographic order. This
is a completely finite enumeration with no oracle or unspecified index.
The code exposes it as `iter_allowed_windows()` but does not execute it
during ordinary validation.

### Exact count without enumerating the window list

The local clause ignores all four corner coordinates. Let a=3502 and
N=a-1=3501. Among all 3488 machine rows there are 1722 left moves, 904 stay
moves and 862 right moves. The extra headed phase tile Q stays, so these
counts also give the numbers of possible left-neighbor arrivals and
right-neighbor arrivals: ell=862 and r=1722. The no-arrival counts are
L=N-ell=2639 and R=N-r=1779; these include V, viewed as blank and headless.

For a no-phase center payload, let b be the symbol written, and let d be
its move if headed. Put `L'=L-[d=-1]`, `R'=R-[d=+1]`; this excludes an
escape through a neighboring V. An unheaded center has no d. If the center
is headed and stays, there are exactly `L'R'` successor crosses. Otherwise
there are

```
L' R' m(b) + ell R' + L' r,
where m(0)=3, m(1)=2, m(b)=1 for b=2,...,7.
```

The multiplicities count possible phase/no-phase upper tiles for a
headless output. Every headed output has multiplicity one because no
transition targets START. A simultaneous pair of incoming heads is
excluded. Let P be the sum of this expression over all 3496 no-phase
center payloads. The valid five-coordinate cross counts are:

| Center/upper case | Count formula | Exact count |
|---|---|---:|
| Center V | `a^2 N` | 42,936,278,004 |
| Center H | `2a^2(a-2)` | 85,848,028,000 |
| Interior center, upper H | `16aN^2+6a-4` | 686,784,301,040 |
| Interior center, interior upper | `PN+17L+6ell-11` | 135,633,605,274,191 |

For the final term, the four initialization centers L,I,Q,R contribute
respectively `2(3L+ell)`, `2(2(L-1)+ell)`, `L-1`, and
`2(3(L-1)+ell)`. Their sum is `17L+6ell-11`.

The cross total is 136,449,173,881,235. Multiplying by the independent
four-corner factor gives the exact allowed-window count

```
k = 20,522,746,353,535,702,537,070,419,760.
```

Thus the retained compiler's selector radix is exactly `A=2^95`.
The count routine is also checked against an independent exhaustive
five-coordinate enumeration on two 18-tile fixture machines, one with
only stay steps and one with both moving directions. Those fixtures
are counting controls, not substitutes for the actual K215 semantics.

## 4. The marker distance and the fixed input

For the standard raw input x, the normalized unary word has x+2 ones,
the I run has x+1 members, and the Start-to-End leftward distance is x.
The modified75 arithmetic slice uses the even-distance interface: its
raw input x has End distance 2x. Setting x=1 therefore selects distance
2, with a four-one input. The normalized machine deliberately ignores
that input after erasing it, so this particular selection is equivalent
to blank K215 halting. No universal-machine program index, encoding of
a formula, or runtime bound remains to be chosen.

## 5. Validation and limits

`normalization_checks.json` records the exact table hash, all 3488 total
transitions, 5160 folded-transition cases over every source state, both
halves, four bit pairs, and three boundary/interior positions. It also
records correct input erasure for lengths 3,4,5,12, four 1000-step matched
prefixes, and a 95714-step matched prefix from a four-one input. These
finite tests check implementation details. The all-time equivalence is
proved by the invariant above, not inferred from finite execution.

The astronomical full allowed-window list and fixed compiler numerals
were not materialized. They are specified by a terminating finite
algorithm. No claim about actual nonhalting or consistency follows from
these checks; the result is the conditional/equivalence theorem required
for the Diophantine construction.

## 6. A smaller conceptual route for future arithmetic optimization

The literal machine is a convenient independently checked input. It is
not intrinsically the smallest source for Diophantine compilation.
`KEndpoint.c222_iff_zf_refutation` calibrates the much simpler numerical
calculus C222 directly, and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`
then changes ZF to ZFC.

Its four constructors are ordinary integer polynomials:

```
I(x,y) = 2(x+y)(x+y+1)+4y,
Rel(x,y)=I(x,y)+1, All(x,y)=I(x,y)+2, Eq(x,y)=I(x,y)+3.
```

Truth is 0 and falsity is 1. The rules are truth, modus ponens,
generalization, eight fixed axiom-row polynomials, and one gated seed
bundle. A direct arithmetic encoding of finite C222 derivations could
avoid all Turing-machine normalization overhead. However that route
still needs a completely explicit finite-sequence/derivation compiler;
simply writing an existential derivability predicate is not an ordinary
Diophantine equation. The present construction uses the verified literal
machine to keep this missing step out of its trusted interface.
