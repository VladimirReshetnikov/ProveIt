# An explicit K215 slice of the fixed-program polynomial compiler

## Result and scope

This directory specifies six particular integers for the fixed-program
Diophantine compiler in ProveIt, pinned at
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.
There is no unknown recursion-theoretic program index and no search for
coefficients. All six integers are defined by finite sums with numerical
limits, a literal 2,616-row machine table, and an explicit finite predicate.
Their binary expansions are intentionally not printed: already the base is

\[
B=2^{5^{85}}.
\]

The fixed machine ignores its unary input, erases it, and simulates the exact
215-state K215 machine on a blank tape. Consequently every positive input
is accepted exactly when K215 halts. Substitution of these six constants and
the ordinary input `x=1` in the repository's complete84 polynomial gives an
18-positive-integer-variable polynomial of degree 187 with a zero exactly
when K215 halts. This statement uses the repository's mathematical compiler
and complete84 correctness theorems. This file is not a new Lean proof of
those theorems.

The original table is `k215.tm`, SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
Its state 215 is the external halting state; its 430 instructions have source
states 0 through 214. The table is not changed by this construction.

## 1. A completely specified normalized machine

The normalized machine has 436 states and six tape symbols. Its ordered
states are

```
start, enter, erase, return, dead, halt,
p0,...,p214,m0,...,m214.
```

Its ordered tape alphabet is `0,1,2,3,4,5`, and its blank is 0. At a physical
position `-n`, with `n>0`, the two tracks store K215's cells `+n` and `-n`:

| Symbol | Positive track | Negative track |
|---|---:|---:|
| 0 | 0 | 0 |
| 1 | 0 | 1 |
| 4 | 1 | 0 |
| 5 | 1 | 1 |

At the physical origin, symbols 2 and 3 represent K215's origin bit 0 and 1.
The prefix transitions are

| State/read | Next state | Write | Physical move |
|---|---|---:|---:|
| start/1 | enter | 2 | 0 |
| enter/2 | erase | 2 | -1 |
| erase/1 | erase | 0 | -1 |
| erase/0 | return | 0 | +1 |
| return/0 | return | 0 | +1 |
| return/2 | p0 | 2 | 0 |

All unspecified prefix transitions go to `dead`, preserve the symbol, and
stay. Both `dead` and `halt` stay forever, preserving every symbol.
For every K215 instruction `(q,a)->(q',b,D)`, the states `pq` and `mq`
perform that instruction on their selected track. On the positive track,
the physical direction is the opposite of `D`; on the negative track it
equals `D`. At an origin marker either side state reads the origin bit,
writes the new origin marker, and moves physically left. Its new side is
positive for an original right move and negative for an original left move.
If `q'=215`, the target is `halt` instead of a side state.

The complete transition list, including all default cases, is emitted as
`folded_machine.json`. Thus no conventional meaning of a schematic
instruction or missing transition is required to recover the finite table.

### Correctness of normalization

Starting with any finite positive length `l` of unary ones ending at the
origin, the first transition is the required stationary origin-marking
step. The erase phase traverses the other `l-1` ones and replaces them by
zero. Upon reaching the first zero it turns right and reaches the unique
origin marker. After exactly `2*l+2` transitions the physical head is at
the origin, state is `p0`, all nonorigin cells are zero, and the origin
marker represents zero. No prefix transition halts or visits a positive
physical coordinate.

For the simulation invariant, let K215 have tape `T`, state `q`, and head
`h`. The normalized physical head is `-|h|`; its origin marker represents
`T(0)` and its depth-`n` pair represents `(T(n),T(-n))`. Its side is `p`
when `h>0` and `m` when `h<0`; either side is allowed at `h=0`. The displayed
transition rules preserve this invariant in one step, including crossings
of the origin. A halt is reached exactly on the K215 transition to 215.
Induction proves the full finite-run equivalence in both directions.

This construction accepts every unary input if K215 halts and none if it
does not. The original complete75 input convention uses a unary length
`2*x+2`; `x=1` therefore starts with four ones. No unary length calculation
is needed by our normalized machine, because the input is ignored.

## 2. An exact finite window alphabet

There are 2,628 tile symbols, in the following order:

1. Vertical boundary `V=(1,0,None,None)` and horizontal boundary
   `H=(0,1,None,None)`.
2. For each tape symbol in increasing order, each head label in
   `None,start,enter,...,m214`, the ordinary tile `(0,0,(symbol,head),None)`.
3. Four initialization tiles with phases `L,I,Q,R`, carrying respectively
   `(0,None),(1,None),(1,start),(0,None)`.

The helical radius-one predicate is implemented directly in `local_valid`.
It is the predicate of the pinned repository's
`Papers/verification/explore_helical_unary_tableau.py`, with the stationary
first-step markers of `explore_fixed_raw_universal_81.py`:

- A vertical boundary persists vertically and has no payload. Adjacent
  vertical boundaries are forbidden.
- Horizontal boundary flags agree between horizontally adjacent nonvertical
  cells. Consecutive horizontal boundaries are forbidden.
- A first interior row has phase word `L^a I^u Q R^b`, with all three
  exponents positive; other interior rows have no phases.
- The next payload is the exact three-neighbor machine update. At most one
  arriving head is allowed, and a head may not cross a vertical boundary.
- A head on the last interior row must be in `halt`.

The code gives every boundary case, so this prose is explanatory rather
than an additional part of the definition.

The rule depends on the center and its four axial neighbors. A permitted
cross is `(center,left,right,down,up)`, listed in lexicographic tile order.
Its four corners are independent and are listed lexicographically as
`(northwest,northeast,southwest,southeast)`. The row-major window is

```
(northwest, down, northeast, left, center, right, southwest, up, southeast).
```

There are exactly

\[
c=43\,126\,116\,188\,949
\]

permitted crosses, and hence

\[
k=c\,2628^4=2\,057\,035\,525\,715\,746\,135\,339\,455\,744
\]

permitted windows. Two distinguished windows are moved to the beginning,
with every other window retaining the foregoing order:

```
Start = (1,1,1,2625,2625,2626,439,439,878)
End   = (1,1,1,2624,2625,2625,2,439,439).
```

The initial Start is centered on the last I immediately before Q. End is
centered on the first I. Both are valid even for the smallest accepted input
convention. The actual functions `crosses` and `windows` define the finite
enumerations without reliance on prose names or an r.e. index.

### Why the cross count is computable without listing crosses

For a fixed center, allowed left and right tiles can be partitioned by
whether they send no head into the center or send a head in a specified
target state. Let these multiplicities be `L_none,L_q,R_none,R_q`, and let
`U_(s,q)` count the upper tiles with payload `(s,q)`. If the center sends
itself a stationary head in state `q`, the number of interior updates is
`L_none*R_none*U_(written,q)`. Otherwise the number is

\[
L_0R_0U_{s,0}
+R_0\sum_q L_qU_{s,q}
+L_0\sum_q R_qU_{s,q}.
\]

Two arrivals are excluded. Initialization restrictions, no-escape restrictions,
upper-boundary endings, and the two boundary-center cases give the remaining
elementary counts. `count_crosses` is this exact factorization of the sum
of the local predicate over all `2628^5` crosses. Its per-center count list
is included in the coefficient recipe for audit.

## 3. Fully numeric layout parameters

Write `a=2628` and use the numerical `k` above. We make a permitted padding
choice for the clause radix:

\[
\ell=92,\qquad A=2^{92}.
\]

This has `A>k+1` and `A=1 mod 5`. The latter makes the optional correction
computable without any window enumeration: selector coefficients are all
`14=4 mod 5`, and copy and anchor coefficients are all `1 mod 5`.

| Name | Exact value |
|---|---:|
| Initial clause count `h0` | 23,656 |
| Zero-clause padding `p` | 1,028,517,762,857,873,067,669,700,184 |
| Final clause count `h=h0+p` | 1,028,517,762,857,873,067,669,723,840 |
| Old field-mask population `m` | 2,057,035,525,715,746,135,339,479,400 |
| Ignored dummy positions | 1 |
| Dummy exponent `e*` | 2,057,035,525,715,746,135,339,487,280 |
| Anchor unit `M` | 2,057,035,525,715,746,135,339,495,165 |
| Inner radix exponent `b` | `5^42` |
| Inner cell length `L` | `5^43` |
| Cell bit width `d=bL` | `5^85` |

Further parameters, determined by these integers, are

\[
H=51M+3a+1,\quad T_1=105M+4a+2,\quad
T_2=159M+4a+3,\quad g=186M+4a+4.
\]

Set `R=2^b`, `B=R^L=2^d`. The integer

\[
\mu=A-2+\sum_{j=1}^{h}A^j
\]

is the duplicated center-clause mask. The full native exponent set is

\[
\begin{aligned}
E={}&\{0,\ldots,k-1\}\cup\{k+3a,\ldots,k+12a-1\}\\
&\cup\{e_*\}\cup\{M,3M,9M,27M\}.
\end{aligned}
\]

For `0<=r,c<3` and `0<=s<a`, let

\[
j(r,c,s)=1+(3r+c)a+s,\qquad
e(r,c,s)=k+3a+(2-r)3a+(2-c)a+s.
\]

The coefficient `c_e` is specified on this disjoint set:

\[
\begin{aligned}
c_i&=1+\sum_{r,c=0}^{2} A^{j(r,c,w_i[3r+c])}
        +\sum_{t=1}^{4}A^{9a+t} &&(0\le i<k),\\
c_{e(r,c,s)}&=A^{j(r,c,s)},\\
c_{3^tM}&=A^{9a+1+t} &&(0\le t<4),\\
c_{e_*}&=0.
\end{aligned}
\]

Here `w_i` is exactly the finite window enumeration in Section 2.

## 4. The six fixed integers

Define

\[
\begin{aligned}
D_C={}&R^{3a}+R^{H+a}+R^{8M}+R^{24M}
 +\sum_{e\in E}c_e(R^{T_1-e}+R^{T_2-e}),\\
D_R={}&R^H,\\
M_C={}&B-1-\sum_{e\in E\setminus\{1\}}R^e-2R^{e_*},\\
M_F={}&\mu(R^{T_1}+R^{T_2})
 +\sum_{r=0}^{1}\sum_{c=0}^{2}\sum_{s=0}^{a-1}R^{e(r,c,s)}\\
&+\sum_{r=0}^{2}\sum_{c=0}^{1}\sum_{s=0}^{a-1}R^{H+e(r,c,s)}
 +R^{9M}+R^{27M}+4.
\end{aligned}
\]

The optional high monomial is absent: direct modular evaluation gives
`2*D_C-D_R=2 mod 5`. The six source ports, in their exact upstream meanings,
are

| Port | Fixed integer |
|---|---|
| `Bm1` | `B-1` |
| `Kconstant` | `D_C+B*D_R` |
| `twice_cell_bits` | `2*d` |
| `inner_bits` | `b` |
| `MC` | `M_C` |
| `MF` | `M_F+B-1` |

The last shift is essential: the source `MF` port is not the native field
mask `M_F`. The low-mask modification `-2R^(e*)` and the field-mask
modification `+4` are likewise essential; they are the modified75 compiler,
not the older complete76 masks.

### Admissibility of the padding choices

The center compiler requires a power-of-two clause radix exceeding `k+1`;
using the slightly larger `2^92` changes no clause meaning. The number of
zero clauses is the smallest number making at least one ignored dummy
available. The layout gives `L>g+27M`; all anchor and duplicated-band
separations therefore hold.

For the stronger modified75 coefficient bound, let `K=m+1`. The sum of
the nonzero center coefficients obeys

\[
\sum_e c_e\le(14k+9a+4)A^{h_0}.
\]

The code chooses `b` as a power of five above both the binary exponent
needed for `2*mu+4` and that needed for

\[
4(K+2)\bigl(2\sum_e c_e+6\bigr)+8.
\]

For this concrete layout those two exponent bounds are
`94,623,634,182,924,322,225,614,593,282` and `2,176,541`, respectively;
rounding upward to a power of five gives `b=5^42`. This deliberately
conservative choice is allowed by the compiler theorem. Both `b` and `L`
are powers of five, so `d` is too and the actual-index dummy control applies.
Increasing a permitted radix does not alter the overlap predicate or the
set accepted by the fixed machine.

All coefficient recipes are finite integer arithmetic. Their huge fixed
powers are coefficients, not variable exponentiation in the final
Diophantine equation. None depends on a hypothetical halting time, proof
length, witness, or truth value of consistency.

## 5. Reproduction and evidence

Run

```
python3 compiler_k215.py --table k215.tm --out generated
```

The command verifies the source table hash, constructs every machine
transition, computes the exact finite layout, and emits
`folded_machine.json`, `coefficient_recipe.json`, and
`compiler_checks.json`. It uses only Python's standard library. It does
not execute any downloaded repository helper.

The saved finite evidence includes 5,160 local folded-transition checks,
initialization lengths 1, 2, 3, 4, 7, 19, and 64, both literal marker
checks, and an independent enumeration of all 1,889,568 crosses in the
repository's 18-tile rejecting-machine fixture. That enumeration reproduces
121,165 valid crosses and agrees with the aggregated count at each center.
The local proof explains why the aggregation is valid for the actual 2,628
tile alphabet; the small fixture is corroboration, not the proof of the
actual count or of unbounded compiler soundness.

The generic semantic and arithmetic dependencies are, at the pinned commit:

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`:
  `blank_halts_iff_zfc_refutation` and `nonhalting_iff_zfc_consistency`.
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md`:
  stationary first-step markers and exact helical semantics.
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md`:
  native selectors, copied tile coordinates, duplicated clauses and anchors.
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md`:
  power-of-five layout and actual-index dummy control.
- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md`:
  the modified native masks and stronger no-carry margin.
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`:
  complete arithmetic soundness and positive completeness.
- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md`:
  the 18-witness degree-187 polynomial and its precise positive-domain theorem.

The K215 verification README explicitly distinguishes its external proof-
assistant endpoint from a formal derivation encoded in ZFC's own proof
syntax. Applying these finite arithmetic constructions yields an ordinary
mathematical proof that can be formalized in ZFC; it does not by itself
produce that encoded derivation or a new end-to-end Lean build.
