# A conditional binary tag history and a necessary disjoint-marker test

This note gives a **29-operation conditional encoded-word halting component**
for a binary tag system. Its six bitwise disjointness tests, the power geometry,
and its nonnegative-word domains are assumptions, not operations implemented
by this component. The literal schedule has **12 multiplications and 17
additions/subtractions**, with twelve checked equations. It is not a complete
positive-integer or Pell construction and supplies no universality bound.

The sixth disjointness test cannot simply be deleted, even for a zero-leading
appendant. Two exact false-positive tuples below retain every other equation,
range, and test. The second also has a genuine one-hot terminal length.

Author and two independent complete proof/source reviews and fresh verification
runs passed without findings, including the added canonical-history regression.
The proof and arithmetic are frozen.
The executable source and receipt are
[explore_binary_tag_queue_history.py](../verification/explore_binary_tag_queue_history.py)
and [its JSON receipt](../verification/explore_binary_tag_queue_history.json).

## 1. Exact conditional interface

Fix a deletion number `beta >= 1` and a binary appendant `u` of length `a >= 2`.
The productions are `0 -> 0` and `1 -> u`. Queue order is least-significant-bit
first. Write

```
K = 2^beta,  Kh = K/2,  B = 2^(a-1),
U = sum(u_i 2^i),  c = Kh-1.
```

Choose a fixed power of two `C > max(K, 2^a, 2U+2)`. The compiled numerals
`K, Kh, B, U, c, C` are free constants. Given an initial word `w` of length
`ell >= beta`, its input parameters are `Ni = value(w)` and `Li = 2^ell`.

Assume the **true power geometry**

```
R = 2^m,  q = R^t,  t >= 1,
H = (q-1)/(R-1),  CA = R.
```

The displayed product `CA` is paid in the schedule. The remaining geometry
and input-length power conditions are external to the 29-operation count.
The nine words `Q,S0,S1,M0,M1,N,Nbar,E,Ebar` are nonnegative integers below
`q`. They are ordinary binary words; there is no ternary Boolean encoding.
The auxiliary sums `L,Nsum` are nonnegative. Impose

```
Q+S1 = M1,       S0+S1 = H,
L = M0+M1,       Nsum = N+Nbar,       L = Nsum+H,
E+Ebar = cH,     d = 2E+S1,

R(N-d+U M1) = K(N-Ni+q Nfinal),
R(M0+B M1) = Kh(L-Li+q Lfinal).
```

The three positive slacks impose

```
Li+alphaI = A,
Lfinal+alphaH = K,
Nfinal+alphaN = Lfinal,
```

with `Lfinal > 0` and `Nfinal >= 0`. The six external tests are

```
Q & M1 = 0,        Q & (AH) = 0,       S0 & S1 = 0,
N & Nbar = 0,      E & Ebar = 0,       M0 & M1 = 0.
```

Here `&` is bitwise AND on nonnegative integers. In particular, the last test
and `L=M0+M1` imply `L<q`; the fourth implies `Nsum<q`. No separate range
assumption on an untyped sum is silently used.

The component characterizes **eventual halting of this encoded input**:
every admitted tuple implies a genuine halt, and every genuine halt has an
admitted tuple at a sufficiently large width. An admitted tuple need not be
the literal first-halting history; the proof stops at its first short marker.

## 2. Why the six-pair interface is sound

**Selector and interval.** Since `S0+S1=H` and `S0&S1=0`, each row head
belongs to exactly one selector and both selectors vanish elsewhere. Put
`A=2^p`, where `p=m-log2(C)`. Process `Q+S1=M1` from low bits upward.
An inactive row has no incoming carry and must have `Q=M1=0`, since otherwise
its first nonzero `Q` bit also occurs in `M1`. In an active row, `Q` is an
initial run of ones. Its first zero becomes the sole `M1` bit. The guard
`Q&(AH)=0` forces that zero at or before offset `p`, preventing a carry into
the next row. Consequently an active row has

```
Qrow = 2^k-1,  M1row = 2^k <= A;
```

an inactive row has both words zero. This proves the row induction without
assuming a marker property for `L` in advance.

**One increasing length path.** Divide the length equation by the fixed
integer `Kh` and set

```
shift0 = m-beta+1 > 0,
shift1 = m+a-beta > 0.
```

It becomes

```
L+q Lfinal = Li + 2^shift0 M0 + 2^shift1 M1.                 (1)
```

The left side is a binary support set: `L=M0+M1` has disjoint summands below
`q`, and `q Lfinal` occupies positions at or above `mt`. Every source bit
belongs to exactly one of `M0,M1`, and so has exactly one outgoing edge to a
strictly larger bit position.

For completeness, disjointness of the two **shifted right-hand summands** is
not assumed. Start with the single pending position supplied by `Li`.
Before it, the right side has coefficient zero, hence the left side does
too. At the pending position the coefficient is one. If it is a source
position, its unique type creates precisely one new pending position; if
it is beyond `mt`, it is the terminal position. Induction leaves at most one
pending edge at every stage. Thus no coefficient two, and hence no first
binary carry, can arise. Every left bit lies on this one increasing path;
there are no unused source components or extra terminal bits. In particular,
`Lfinal` is forced to be a power of two even though it was an arbitrary
positive integer below `K` in the interface.

**Rows before the first short marker.** The path starts at the initial
marker `Li`. While a marker has value `lambda >= K`, its successor lies in
the next row and has value

```
2 lambda/K       for an M0 marker,
2^a lambda/K    for an M1 marker.
```

The stronger invariant `K lambda < R` holds initially because
`Li<A` and `C>K`. An `M0` step preserves it since `K>=2`; an `M1` step
preserves it because its source marker is at most `A` and `C>2^a`.
These bounds also show that neither successor skips a row. Therefore,
until the first marker below `K`, each row contains exactly one path bit.
Such a short marker must occur by row `t`, because the terminal marker is
below `K`.

**Content and the real prefix.** On each preceding row, process
`Nsum+H=L` with zero incoming row carry. The binary disjointness of
`N,Nbar` gives `0<=Nsum_row<=R-1`. Thus `Nsum_row+1<=R`; a carry out would
leave a zero output row, contradicting its nonzero marker. It follows that
`Nsum_row=lambda-1` and `0<=Nrow<lambda`, with no outgoing carry.

Likewise `E&Ebar=0` and `E+Ebar=cH` put `E` in the low `beta-1` positions
of each row. Hence `drow=2Erow+S1row` lies in `[0,K)` and has low bit
`S1row`.

The content equation modulo `R` first gives `Nrow0=Ni`: division by the
fixed `K` gives congruence modulo `R/K`, and both numbers are below that
modulus. At any subsequent pre-short source row, cancel the already
verified preceding rows and reduce modulo `K`. Its selected length is
divisible by `K`, so

```
drow = Nrow mod K.
```

In particular the selector reads the genuine first bit. Now
`Nrow-drow+U M1row` is nonnegative and is the actual appended queue number
times `K`. It is strictly below `K` times the successor length, hence below
`R`. Before the first short target, the next encoded content is bounded
the same way, so reduction modulo `R` identifies it exactly. At the first
short target this last identification is unnecessary: the genuine preceding
word has already taken a valid transition to length below `beta`. This
establishes a real halt, without assuming that later formal rows are causal.

**Converse.** Take a genuine first-halting run and choose the width so that
every source length marker is at most `A`, with `Li<A`. Pack its lengths in
`M0` or `M1` according to their true first bits. In active rows use
`Q=lambda-1`. Set `Nbar_row=lambda-1-Nrow` and
`Ebar_row=c-Erow`. These are literal bit complements in their respective
intervals, so all six AND tests hold. Both transport equations telescope,
and the genuine terminal word supplies the three positive slacks. Zero
packed words and a zero terminal number are allowed in this conditional
nonnegative interface; converting them to strictly positive supplied
coordinates has not been counted here.

## 3. The paid schedule

The checker lists all 29 primitive operations and checks all twelve source
polynomials symbolically. Its accounting is

| Portion | Multiplications | Additions/subtractions |
|---|---:|---:|
| `CA` and `AH` | 2 | 0 |
| Selector, marker, and content sums | 0 | 5 |
| Prefix scale, partition, and `d` | 2 | 2 |
| Content transport | 4 | 4 |
| Length transport | 4 | 3 |
| Three bounds | 0 | 3 |
| **Total** | **12** | **17** |

This is the literal generic DAG, not a lower bound; particular compiled
constants may permit further specialization. Bitwise AND is not a free
arithmetic primitive in a completed construction. This note does not add an
uncounted mask encoder, geometry compiler, input loader, positive adapter,
or Pell witness and does not claim a total such as 106 operations.

## 4. Two complete false positives after deleting `M0&M1=0`

Use the fixed system

```
beta=2,   0 -> 0,   1 -> 01,
K=4, Kh=2, B=2, U=2, c=1, C=8.
```

The appendant starts with zero, so `U` is even. The initial word is `111`,
with `Ni=7, Li=8`. It is provably nonhalting:

```
111 -> 101 -> 101 -> ... .
```

Both tuples use `A=16, R=128`. The table gives all remaining words and
terminal coordinates; `q=R^t` and `H=(q-1)/(R-1)` hold exactly.

| Coordinate | Four rows | Five rows |
|---|---:|---:|
| `q` | 268435456 | 34359738368 |
| `H` | 2113665 | 270549121 |
| `Q` | 2097551 | 6291855 |
| `S1` | 2097281 | 2097281 |
| `S0` | 16384 | 268451840 |
| `M1` | 4194832 | 8389136 |
| `M0` | 4326392 | 1073873912 |
| `L` | 8521224 | 1082263048 |
| `Nsum` | 6407559 | 811713927 |
| `N` | 2163847 | 539034759 |
| `Nbar` | 4243712 | 272679168 |
| `E` | 1 | 268435457 |
| `Ebar` | 2113664 | 2113664 |
| `Nfinal` | 1 | 0 |
| `Lfinal` | 3 | 2 |
| `alphaI,alphaH,alphaN` | `8,1,2` | `8,2,2` |
| Omitted `M0&M1` | 4194832 | 528 |

For both columns, every word is in `[0,q)`, all three slacks are strictly
positive, all twelve source comparisons hold, and each of the five retained
AND tests is zero. The first column's two transport equalities both evaluate
respectively to `1082397184` and `1627655168`; the receipt records the second
column's exact values as well.

The five-row tuple has `Lfinal=2`, the proper marker for a one-symbol terminal
word, and `Nfinal=0`. Thus separately requiring a genuine short terminal
length does not repair the omission.

The defect already appears in the first radix-128 row. Both examples have
`M0_row=120` and `M1_row=16`, so their sum is `136=8+128`. The carry leaves
the apparent initial marker `8` while the selected append uses marker `16`.
This is precisely the behavior excluded by the sixth test. The counterexample
refutes the proposed five-test **conditional component**; it is not presented
as a counterexample to an unspecified complete mask/Pell packing.

## 5. Finite evidence

The fresh checker verifies the complete generic 29-operation source, then
checks 26,004 complete selector candidates in 30 finite configurations,
accepting exactly 370 canonical interval selections. Its independent flow
enumeration covers 157,440 disjoint-marker/shift candidates and verifies that
all 3,650 admitted equations have exactly one increasing path and one terminal
bit. It also checks both full integer false tuples, all retained ANDs,
all ranges and slacks, and the exact nonhalting two-word transition proof.

The complete canonical regression independently simulates every binary
appendant of length two or three, deletion number two or three, and every
initial word of length `beta` through `beta+2`, with a twenty-step cutoff.
It obtains **776 genuine first-halting runs with 2,006 source rows**, plus
232 cutoff cases. Each halting run is encoded in ordinary binary without
importing a ternary implementation, and passes all twelve complete source
comparisons, all six AND tests, the word ranges, true power geometry, three
positive slacks, and exact initial/final words. The runs include 336 histories
using only selector zero, 48 using only selector one, and 392 using both;
72 initial numbers and 632 terminal numbers are zero. Every one of the nine
packed word coordinates is zero in at least one admitted canonical example.
These are tests of the nonnegative conditional interface, not an implicit
claim that its positive adapters have been paid.

These finite checks support the general proof above. They are not a
materialization of a Pell extension or a full universal verifier.
