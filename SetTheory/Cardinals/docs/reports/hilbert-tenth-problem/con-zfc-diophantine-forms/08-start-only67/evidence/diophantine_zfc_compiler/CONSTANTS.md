# Exact, bounded constants for the blank-input K215 instance

This annex specifies the coefficients, rather than asserting that some
universal-machine coefficients exist. The integers are defined by a completely
bounded computation which never simulates K215 until halt. Decimal expansion
of these integers is neither practical nor claimed.

## 1. The exact starting machine

The included `k215.tm` has 430 transition rows and SHA256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
It is the file at
`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` in commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm).
Each row is `(source state, read bit, write bit, direction, target state)`.
The working states are 0 through 214; target 215 halts. The tape is initially
blank and the initial state is 0. The included file is inert input data,
not imported or executed Python.

## 2. The normalized fixed machine is completely explicit

`explicit_constants.py:delta` is a total transition function for 435 states
and ten tape symbols. States 0,1,2,3 are respectively q0,q1,Erase,Return;
states `4+2q+t`, for `0<=q<215` and `t in {0,1}`, simulate state q on
track t. State 434 is the absorbing halt. Physical coordinates are nonpositive.

The tape symbols 0,3,4,5 represent the two-track pairs 00,01,10,11;
6,7,8,9 are the same pairs with a permanent origin flag. Symbols 1 and 2
are the initialization-one and temporary-origin flag. The prefix is

- delta(q0,1) = (2,stay,q1);
- delta(q1,2) = (2,left,Erase);
- delta(Erase,1) = (0,left,Erase);
- delta(Erase,0) = (0,right,Return);
- delta(Return,0) = (0,right,Return);
- delta(Return,2) = (6,stay,4).

At physical cell -n, n>=0, track 0 stores logical K215 cell n and track 1
stores logical cell -n-1. A logical move across 0/-1 changes the active track
and stays at the flagged cell; every other move is the corresponding physical
left/right move. A simulated write changes only the active bit. This rule is
implemented explicitly by `delta`, including the final transition to the
absorbing halt. All other malformed state/symbol combinations stay put without
halting. The first transition is stationary, exactly as required by the fixed
Start window.

Starting on any finite positive unary string with its head at the rightmost
one, the prefix erases every one, arrives at the flagged blank origin, and
enters K215 state0 on track0. Thus this fixed machine halts on every such
unary length if K215 halts blank, and on none if K215 does not. It never visits
a positive physical coordinate.

## 3. Exactly 4366 underlying tiles and a bounded window alphabet

The tile indices are:

- 0: vertical boundary V;
- 1: horizontal boundary H;
- 2,3,4,5: initialization phases L,I,Q,R, carrying respectively
  `(0,nohead),(1,nohead),(1,q0),(0,nohead)`;
- `6+436s+h`, for `0<=s<10` and `0<=h<436`: a noninitial interior
  tile with symbol s, and no head if h=0 or head state h-1 otherwise.

Consequently the tile alphabet size is the actual numeral

    a = 4366.

For a row-major 3x3 tuple w, the Boolean predicate
`explicit_constants.py:allowed_window(w)` is the full local definition. It
checks vertical propagation of V, nonadjacent V columns, uniform horizontal
boundary status between non-V neighbors, nonadjacent H rows, initialization
phases and allowed phase edges, exact deterministic centered updates, no escape
through V, and halting heads on a final interior row. The exact source is
included; there is no unspecified standard-TM-encoding step.

Only the center's radius-one clauses need to be checked in each window.
Exact horizontal and vertical overlap of successive 3x3 windows imposes these
clauses at every cell of the recovered plane. The four corners are legitimate
but unused by the centered predicate; overlap still binds all nine entries.

Put

    S = (H,H,H, I,I,Q, tile(1),tile(1),tile(2,q1)),
    E = (H,H,H, L,I,I, tile(0),tile(1),tile(1)).


For the fixed loader W0=R B^2, choose the actual initialization
`L^a I I I Q R^2`, not the shorter two-I example. The unary input has four
ones, including Q. Start is centered on the last I and End on the first I,
so End lies exactly two physical cells to the left of Start. With cyclic
index `i=-(r-r_Start)-h(t-1) mod N`, a physical right neighbor has index i-1,
and the next time row has index i-h. Hence End has cyclic index +2, precisely
the exponent in W0. This agrees with the compiler overlaps
`center[r,c+1]=right[r,c]` and `center[r+1,c]=next[r,c]`.
The normalized machine ignores unary length, so this fixed input has exactly
the desired blank-K215 semantics.

Both pass the displayed local predicate. Enumerate the finite allowed window
alphabet as S first, E second, then all other passing tuples in lexicographic
order on `{0,...,4365}^9`. This fixes `w_0,...,w_(k-1)` uniquely. The enumeration
examines at most the following explicit number of tuples:

    U = 4366^9 = 576439300316095098822468574875136.

Equivalently, using the nine base-a digits of n (most significant first),
let P(n) be 1 if that tuple passes the predicate and 0 otherwise. Then
`k=sum_(n=0)^(U-1) P(n)`. This is a bounded sum of a total, explicitly supplied
predicate, not a halting test. For n other than the codes of S,E, its enumeration
rank is `2+sum_(j<n) P(j)-[code(S)<n]-[code(E)<n]`. Thus every entry of every
w_i can also be written as a bounded sum of base-a digits times rank indicators.
There is no choice of an unknown accepting computation in any coefficient.

## 3a. Why a marked periodic plane is a genuine halting computation

Exact overlaps pull a cyclic word back to a valid plane using
`i=-x-hy mod N`. This plane has both axis periods N, even if h does not
divide N. A Start window contains an initialized Q immediately to its right.
The phase graph has no directed cycle through Q, so horizontal periodicity
forces vertical boundary columns on both sides of this Q. Choose the nearest
pair. Vertical propagation makes them the sides of one finite-width strip.
The H immediately above Start propagates horizontally throughout that strip.
Vertical periodicity supplies a later H; choose the first later one. The
region between the two H rows is a finite rectangle. Its initial phase path
is exactly `L^a I^u Q R^b`, with a,u,b>=1. Exact updates, together with the
no-escape condition, inductively preserve one genuine head and simulate the
total normalized machine. The last-row restriction requires that head to be
in its absorbing halt. The unary erase prefix then identifies this with a
blank-tape halting computation of K215. This argument needs the occurrence
of Start, not uniqueness of Start or the identification of End.

Conversely, given a finite blank-K215 halt, the initialized normalized run
on four ones has finite duration and leftmost visited cell. Take u=3 and any
sufficiently large width h, with left margin `a_margin=h-7>=2` and two blank
right cells. Independently take any sufficiently large time height Htime and
pad the halted tail using the absorbing transition. Put one V column and one
H row in the h-by-Htime base array G, and extend it by
`T(x,y)=G[x mod h,(y+floor(x/h)) mod Htime]`. All helical seams pass because
V has no time-dependent payload and horizontal boundary propagation stops at V.
The periods `(h,-1)` and `(0,Htime)` give a cyclic word of size N=h Htime.
The map `i=-(r-r_Start)-h(t-1) mod N` is bijective on the base rectangle.
This gives one Start at0 and one End at2 with the exact required overlaps.
Since both dimensions may be enlarged independently, choose h,Htime as powers
of five with Htime>=25 and N>25d, exactly as required by the five-adic dummy
control. No bound on the unknown halting duration is used to define coefficients.

## 4. Deterministic compiler formulas

The following reproduce the mathematical complete75 compiler interface. The
independent implementation is `compiler_layout`; it neither imports nor runs
any upstream checker. All indices in this section are finite.

Let `ell=max(2,bitlength(k+1))` and `A=2^ell`. Let

    e(r,c,s)=k+3a+(2-r)3a+(2-c)a+s,
    j(r,c,s)=1+(3r+c)a+s.

There are k selector positions i=0,...,k-1, and 9a copy positions e(r,c,s).
Initially define the nonzero coefficient map by

    c_i = 1 + sum_(r,c) A^j(r,c,w_i[3r+c])
              + sum_(j=9a+1)^(9a+4) A^j,
    c_e(r,c,s) = A^j(r,c,s).

Set

    m0 = 2ell+30a+8,
    p = max(0,ceil((k+9a+4-m0)/2)),
    m = m0+2p,
    mu = A-2 + sum_(j=1)^(9a+4+p) A^j,
    D = m-k-9a-3.

Here p is the number of zero-expression padding clauses and D>=1 is the
number of ignored dummy positions. The dummies are the consecutive exponents
`k+12a,...,k+12a+D-1`. Let E0 be the union of selector, copy and dummy
positions, and define

    M0=max(E0)+3a+1=k+15a+D,
    (u1,u2,v1,v2)=(M0,3M0,9M0,27M0).

Add those four anchors to E0 to obtain the native exponent set E; set
`c_u1=A^(9a+1)`, `c_u2=A^(9a+2)`, `c_v1=A^(9a+3)`,
`c_v2=A^(9a+4)`. All dummy coefficients are zero. Then

    K=|E|=m+1, Emax=27M0,
    H0=Emax+24M0+3a+1,
    T1=H0+2Emax+a+1,
    T2=T1+2Emax+1,
    g=T2+Emax+1.

Let L be the least power of five strictly greater than g+Emax. Put

    mass=(K+2)(2 sum_(e in E) c_e+6),
    target=max(4mass+8,2mu+4,16).

Let b be the least power of five such that `2^b>=target`. Finally put

    R=2^b, d=bL, B=2^d.

These least-value definitions have fixed elementary bounds: for every positive
integer n, the least power of five at least n is at most 5n. The code computes
b as the least power of five at least `bitlength(target-1)`. No unbounded search
for machine behavior occurs.

Define the sparse polynomial

    DC0(T)=T^(3a)+T^(H0+a)+T^(8M0)+T^(24M0)
            + sum_(e in E) c_e [T^(T1-e)+T^(T2-e)].

Let epsilon=1 if `2 DC0(2)-2^H0` is zero modulo5, and epsilon=0 otherwise.
Then

    DC=DC0(R)+epsilon R^g,
    DR=R^H0,
    MF0=mu(R^T1+R^T2)
         +sum_(r<2,c<3,s<a) R^e(r,c,s)
         +sum_(r<3,c<2,s<a) R^(H0+e(r,c,s))
         +R^v1+R^v2,
    e_star=k+12a,
    MC=B-1-sum_(e in E,e!=1) R^e-2R^e_star,
    MF=MF0+4.

The six universal-compiler numerals (before final source aliasing) are:

    Bm1=B-1,
    Kconstant=DC+B DR,
    twice_cell_bits=2d,
    inner_bits=b,
    MC=MC,
    MF=MF.

Here MF denotes the native field mask, also written M_F^native. The source-side
alias is `MF_source=MF+B-1`, also written M_F^src. They are different integers.
The explicit fixed-input loader at x=1 is

    W0=R B^2=2^(b+2d).

The actual six ports in `fixed_input_polynomial74.json` are bound by
`emitted_fixed_ports(layout)` as follows:

    Bm1 -> B-1,
    Kconstant -> DC+B DR,
    twice_cell_bits -> 2d,
    MC -> MC,
    MF -> M_F^src = M_F^native+B-1,
    W0 -> 2^(b+2d).

In particular the target JSON port named MF must NOT receive the native MF.
The generic `materialize_constants` function exposes both values explicitly;
use `emitted_fixed_ports` for this deliverable. The symbolic expression DAG
contains the same target-port map. A materialized small stub checks all six
bindings, including native52 becoming source563 when B=512.

All exponentiations in this annex define coefficients, not operations on
existential variables. This distinction is essential when stating a polynomial
or counting its variable arithmetic operations.

## 5. Strong raw margin for projected variants

For the canonical completeness encoding, including the five-adic low-dummy
adjustments, all native digits of C and Z are 0 or 1. At whole-cell alignment,
the field F has each radix-R coefficient at most `mass+1<=R/4-1`.
Thus every coefficient of C+F+Z is at most `R/4+1<=R-2` (R>=16), without
carries. Every radix-B cell is therefore at most B-2. With
`q=B^N` and `J=(q-1)/(B-1)`,

    C+F+Z <= (B-2)J,
    q-C-F-Z >= J+1 > 2d

whenever the freely padded N is larger than 2. The last inequality follows
from `J>=B^2>2d`. This proves strict positivity of the stronger projected
raw-bound slack without changing any compiler numeral.

## 6. Evidence and limits

`python explicit_constants.py --receipt compiler_audit.json` checks:

- the SHA256 and all 430 rows of the K215 data file;
- the complete 4350-action total normalized transition function;
- all 3440 combinations of original state, stored bits, endpoint flag and
  active track in the fold conversion;
- unary erasure for lengths2 through30;
- both fixed marker windows;
- four synthetic compiler layouts, with 35364 exact native-basis field tests,
  native geometry, unique anchor difference, dummy invisibility, both branches
  of the five-adic correction and the stronger quarter-radix margin;
- a fully specified immediate-halting toy substitution:750 local windows across
  helical seams,250 cyclic overlaps, and unique markers at indices0 and2.

The full window alphabet and full huge constants are not materialized.
The displayed bounded definitions specify them exactly. The general semantic
arguments and number-theoretic certificate proofs remain mathematical proofs,
not a new proof-assistant formalization. Bounded tests do not establish the
unbounded K215/ZFC bridge; that bridge must be supplied by the separately
identified repository theorem and its checked source binding.

`python explicit_constants.py --symbolic-spec constant_expression_dag.json`
also exports a human-readable finite expression DAG for all fixed constants,
without enumerating the huge alphabet or evaluating the final integers.
