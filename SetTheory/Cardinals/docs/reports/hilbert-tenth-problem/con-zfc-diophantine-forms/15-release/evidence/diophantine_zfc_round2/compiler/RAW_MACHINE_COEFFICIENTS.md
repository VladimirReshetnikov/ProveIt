# A smaller exact coefficient instance for the 61/67-operation construction

## Result and scope

The package `06-blank67` at ProveIt revision
`3b201cdea32d2c816f5f3d20734051f25fd3ef14` supplies a valid raw-machine
replacement for the earlier 435-state, 4,366-tile normalized-machine
coefficient instance. Its machine table is the same K215 table pinned by
SHA-256 `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The first action really is `(0,0) -> (write 1, right, state 93)`; the final
action `(68,1) -> (write 1, right, state 215)` must retain its move and write.
Only the new absorbing transitions at state 215 are stationary.

All 430 rows of package 06's inert JSON were compared with the original
table. An independently written exhaustive count over all 439 center
symbols reproduces its 38,256,607,897 valid crosses and
1,420,903,358,357,108,792,377 windows. Its scalar coefficient recipe,
including b=5^33, L=5^34, d=5^67, is correct. Its modified band spacing
does eliminate the old optional correction term: 2 D_C-D_R=3 modulo 5.

There is a further coefficient-only improvement. Impose at most one head
in each of the three rows of each local window. The resulting exact
alphabet has

    kappa = 10,762,728,984,864

symbols. With a shorter congruence-compatible clause-band separation,
the same four-port compiler gives

    b = 5^21, L = 5^22, d = 5^43,
    B = 2^(5^43).

This changes neither the 15-positive-variable polynomial skeleton nor
its 67-operation count, nor the 61-operation six-equation system.
It also applies unchanged to compatible lower-degree versions of that
skeleton. It is a reduction of coefficient height and description
complexity, not a new operation-count or variable-count record.

The proofs below are ordinary mathematics supported by separately
written finite checks. They are not a Lean/Rocq certification of the
Diophantine bridge. The retained arithmetic compiler and K215 calibration
theorems remain separate dependencies.

## 1. Explicit local alphabet and relation

There are a=439 underlying cell codes:

- 0 and 1: the two headless tape symbols;
- 2(q+1)+s for 0<=q<=215 and s in {0,1}: a head in state q on symbol s;
- 434=L, 435=Q, 436=R: initialization phases with payloads
  (0,no head), (0,state 0), (0,no head);
- 437=V: vertical boundary; 438=H: horizontal boundary.

The vertical boundary bit is 1 only at V; the horizontal bit is 1 only
at H. Boundary cells have no payload or phase. Ordinary cells have no
phase. Complete the exact K215 table by (215,s)->(s,stay,215).

For a 3-by-3 window in row-major order, let P,Lc,C,Rc,N be its previous-time,
left, center, right, and next-time codes. Time increases downward. Require:

1. v(C)=v(N); not both C and Rc are V; not both C and N are H.
   When neither C nor Rc is V, h(C)=h(Rc).
2. At a boundary center there are no further original center conditions.
3. At an interior center, an initialization phase is present exactly
   when P=H. If present, a V on the left forces phase L and a V on the
   right forces phase R. If Rc is not V, the ordered center/right phase
   pair is one of LL,LQ,QR,RR.
4. An interior head with N=H is halted, in state 215. An interior head
   cannot make its next move through an adjacent V.
5. If N is not H, its payload is the deterministic update of the three
   current payloads: a center head writes; otherwise the symbol stays;
   incoming heads are exactly a left head moving right, a center head
   staying, or a right head moving left. More than one incoming head is
   forbidden. V is blank and headless for this update; an H neighbor
   cannot supply an interior update.

These are the asymmetric center clauses of package 06; no additional
left or prior-time copy of a boundary condition is silently inserted.
The new additional condition is:

6. Each of the window's three rows contains at most one headed code.

Here a headed code means 2 through 433 or 435. Exactly 433 codes are
headed and six are headless (0,1,434,436,437,438).

Call the resulting predicate Good. It is explicitly evaluated by the
newly authored `raw_coefficients_audit.py:allowed`. The mathematical
definition is the six clauses above; no machine simulation or halting
test is used to define Good.

## 2. The two distinguished windows

In row-major form put

    S = (438,438,438, 434,435,436, 0,1,188),
    E = (0,438,0, 0,437,438, 0,437,0).

Both satisfy Good. S's center is Q, and the actual first machine action
forces its lower row (0,1,188) in any globally valid plane. In particular
no artificial stationary first action or auxiliary machine is needed.

E is locally allowed, has no heads, and is globally impossible. Its
previous-time center is H and its center is V. The center predicate at
that previous-time H requires v(H)=v(V), or 0=1. This argument works in
every globally valid plane, not just the canonical halting presentation.
Thus assigning E the compiler's forbidden selector 1 removes no genuine
global solution. S is assigned selector 0.

Define W_0=S, W_1=E, and enumerate all remaining Good windows
lexicographically. This is a bounded enumeration of 439^9 tuples and
defines every W_i independently of whether K215 halts.

## 3. Soundness and completeness of the smaller language

Soundness is inherited from package 06, because Good implies its original
center predicate. For completeness, the additional restriction needs an
argument about helical seams, not merely the assertion that a Turing
machine has one head globally.

For soundness, suppose the Good windows overlap horizontally by two
columns and vertically by two rows and give a finite cyclic word with
neighbor offsets -1 and -h. The overlaps reconstruct an actual plane:
the entry at offset (dx,dy) in the window at i is the center at
i-dx-h*dy modulo the word length. This holds even if offsets coincide.
The plane is periodic separately in both coordinates.

At an occurrence of S, the phase graph LL,LQ,QR,RR has no directed cycle
through Q. Horizontal periodicity therefore forces V columns on both
sides. Vertical propagation makes these genuine boundaries of a finite
strip. The H immediately above Q propagates across that strip. Temporal
periodicity supplies a next H row. Between the nearest such rows, the
first interior row is L^u Q R^v with u,v>=1. It has exactly one state-0
head and otherwise blank tape. The local update and no-escape rules
preserve that unique head and the exact machine computation. The last
interior row's unique head must be in state 215. Hence K215 halts.
Neither global uniqueness of S nor any condition h|N is needed.

Conversely, given a finite blank-input halting run, choose a strip whose
leftmost and rightmost two interior cells lie strictly outside every
visited head position. Put V at column zero, H at time zero away from V,
L^u Q R^v at time one, then the genuine run and absorbing halt padding.
The width and height can each be any sufficiently large integer.

Extend the rectangle G of width w and height Ht by

    T(x,t)=G(x mod w, (t+floor(x/w)) mod Ht).

Inside one strip, each three-cell row has at most one head because its
whole computation row has one head. A three-cell row that crosses a
helical seam either meets V or consists only of cells within two places
of V. All such interior cells are permanently headless by the chosen
margins. Consequently it cannot collect two heads from the adjacent
strips at their different time offsets. Thus clause 6 holds everywhere.
All original clauses remain valid as in the raw helical construction.

The periods are (w,-1) and (0,Ht), and with N=w*Ht the cyclic coordinate

    i=-(x-x_S)-w(t-1) modulo N

puts the unique S at zero and gives right/next-time offsets -1 and -w.
E never occurs. Width and height can still be padded independently to
arbitrarily large powers of five, preserving the hypotheses of the
native compiler's Boolean dummy-control theorem.

This proves that the smaller marked periodic language is solvable
exactly when blank-input K215 halts.

## 4. Exact alphabet cardinality

For a fixed headed row center, its two corners have 6^2=36 possible
headless assignments. For a fixed headless row center, the two corners
have 6^2+2*6*433=5232 assignments with at most one head.
The original predicate depends only on the five-cell cross. Therefore
one may enumerate all center/left/right combinations with at most one
head and sum these exact corner weights over allowed prior/next centers.

The resulting count is 10,762,728,984,864. Two separately implemented
calculations agree for every one of the 439 center symbols:

- C++ enumerates all 439 centers and every left/right pair, evaluates
  the exact center predicate, and weights all possible prior/next codes;
- Python uses closed category formulas derived from the head-count
  restriction and the actual transition counts (349 symbols send a head
  right, 82 send a head left, four right-moving symbols target state 0).

The four initialization and boundary coding multiplicities are not
silently removed: a next payload (0,no head) has three possible symbols
0,L,R; a next payload (0,state 0) has ordinary code 2 and phase Q. Their
own next-centered phase tests have not yet been imposed locally.

All the individual counts are in `raw_coefficients_audit.json`.
This is an exact count of the specified finite language, not a sampled
estimate or an enumeration of all 439^9 windows.

## 5. Complete four-coefficient recipe

Use the following fixed integers. No symbol in this section is an
existential unknown. Set a=439 and kappa=10,762,728,984,864. Let

    ell = 44, A0=2^ell,
    p = max(0,ceil((kappa-2ell-21a-4)/2)),
    jmax = 9a+4+p,
    mu = A0-2 + sum_(j=1)^jmax A0^j,
    m0 = 2ell+30a+8+2p,
    npos = m0+1, ndum=npos-kappa-9a-4,
    e_star=kappa+12a, M0=kappa+15a+ndum.

For 0<=r,c<=2 and 0<=u<a put

    e(r,c,u)=kappa+3a+(2-r)3a+(2-c)a+u,
    j(r,c,u)=1+(3r+c)a+u.

The native exponent set is the disjoint union

    Eset = {0,...,kappa-1}
           union {e(r,c,u)}
           union {e_star,...,e_star+ndum-1}
           union {M0,3M0,9M0,27M0}.

Its cardinality is npos. Define c_e by

    c_i = 1 + sum_(r,c=0)^2 A0^j(r,c,W_i[3r+c])
              + sum_(t=1)^4 A0^(9a+t), 0<=i<kappa;
    c_e(r,c,u) = A0^j(r,c,u);
    c_(3^(t-1)M0) = A0^(9a+t), 1<=t<=4;
    c_e = 0 on the dummy exponents.

Now set

    Emax=27M0,
    HC=Emax+24M0+3a+1,
    T1=HC+2Emax+a+1,
    gap=4*ceil(Emax/2)+2,
    T2=T1+gap.

Let L be the least power of five at least T2+2Emax+2. Set

    U=4(npos+2)(28(kappa+9a+4)+6)+8,
    bmin=max(ell(jmax+1)+3,ell(9a+4)+bits(U)+1,4),

where bits(U)=floor(log2 U)+1. Let b be the least power of five at
least bmin, and put rho=2^b, d=bL, B=rho^L. Finally define

    DC = rho^(3a)+rho^(HC+a)+rho^(8M0)+rho^(24M0)
         + sum_(e in Eset) c_e(rho^(T1-e)+rho^(T2-e));
    DR = rho^HC;
    MF0 = mu(rho^T1+rho^T2)
          + sum_(r=0..1,c=0..2,u=0..a-1) rho^e(r,c,u)
          + sum_(r=0..2,c=0..1,u=0..a-1) rho^(HC+e(r,c,u))
          + rho^(9M0)+rho^(27M0);
    MC = B-1-sum_(e in Eset,e!=1)rho^e-2rho^e_star;
    MF_native=MF0+4.

The four actual polynomial coefficient ports are

    m = B-1,
    K = DC+B*DR,
    MC,
    MF_source = MF_native+B-1.

The last source coefficient is not the one-cell field mask. Do not
substitute MF_native for MF_source, or combine these masks with the
old DC or K, or use the old window ordering with the new constants.

## 6. Concrete scalar values

    p = 5,381,364,487,777
    jmax = 5,381,364,491,732
    m0 = 10,762,728,988,820
    npos = 10,762,728,988,821
    ndum = 2
    e_star = 10,762,728,990,132
    M0 = 10,762,728,991,451
    Emax = 290,593,682,769,177
    HC = 548,899,178,565,319
    T1 = 1,130,086,544,104,113
    gap = 581,187,365,538,358
    T2 = 1,711,273,909,642,471
    bmin = 236,780,037,636,255
    b = 476,837,158,203,125 = 5^21
    L = 2,384,185,791,015,625 = 5^22
    d = 1,136,868,377,216,160,297,393,798,828,125 = 5^43.

In particular m=B-1 has exactly 5^43 binary digits, compared with
5^67 in package 06. The ratio of these bit lengths is 5^24.
The coefficients remain astronomically large and are not expanded.

## 7. Why the shorter bands preserve the compiler

The two clause bands need gap>2Emax, L-gap>Emax, and T2+Emax<L.
The chosen gap is the smallest integer greater than 2Emax congruent to
2 modulo 4, and the chosen L implies both other inequalities.
All other native positions and transport shifts are unchanged.

The bounded mass proof also remains unchanged:

    sum c_e <= 14(kappa+9a+4) A0^(9a+4),
    mu < A0^(jmax+1).

The chosen b is consequently large enough for the same uniform no-carry
margin rho>=max(4(npos+2)(2sum c_e+6)+8,2mu+4,16).
The native field mask and data mask have populations m0+1 and d-m0-1,
so their sum is d; MC=2 modulo 4 and MF_native=4 modulo 8 as required.

For the modulo-five unit, b is a power of five, hence rho=2 modulo 5.
Each paired clause term cancels because gap=2 modulo 4. Since a=3
modulo 4, the remaining terms give

    2DC-DR = 2(2+3rho^HC+1+1)-rho^HC = 3 modulo 5.

No conditional correction or fifth coefficient is introduced.

For support geometry, all non-anchor exponents lie below M0-3a.
The shifts 3a and HC+a reproduce exactly the two-row and two-column
copy tests; the shifts 8M0 and 24M0 give exactly the anchor tests
M0->9M0 and 3M0->27M0. No other support pair has the anchor difference
18M0. The high clause bands remain separated from every lower test,
and their mutual separation excludes cross-contributions. Therefore
the retained native synchronization and half-binomial mask proof has
the same hypotheses, including the extra upper dummy bit.

Six independently constructed sparse test layouts, including one/two
dummy and nonzero padding regimes, passed 336,576 individual basis
convolution checks and exact all-rotation band/anchor intersection
checks with this shorter gap. These finite checks supplement, rather
than replace, the support argument.

## 8. Reproduction and limits

The newly written audit can be reproduced with

    g++ -std=c++17 -O2 count_windows_independent.cpp -o count_windows_independent
    ./count_windows_independent ../../diophantine_zfc_compiler/k215.tm > count_windows_independent.json
    python -B raw_coefficients_audit.py

The Python script uses relative paths to the inert original table and
the downloaded package 06 JSON. It imports no received Python module.
The exact receipt is `raw_coefficients_audit.json`.

In addition to exact cardinality and coefficient-layout checks, 75
independently padded halting-control helices passed 13,250 local window
and overlap tests. Their first action is the actual K215 first action;
their later actions are explicit finite halting controls, not a claim
that K215 has halted. No actual K215 halting witness, giant coefficient
expansion, ZFC refutation, or proof-assistant certificate is supplied.
