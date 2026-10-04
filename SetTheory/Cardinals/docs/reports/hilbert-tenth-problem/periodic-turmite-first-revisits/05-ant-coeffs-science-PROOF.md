# Exact structured coefficient construction

This is a new coefficient-prefix construction, not a change to the ant theorem or its variable-dependent arithmetic source. It works in the same source language as Report44: addition, subtraction and multiplication, starting with literal 1 and literal 3. (Addition and multiplication alone could not even form the old prefix's zero or negative anchor coefficients.) Loop bounds and fixed template bits are compile-time data, not free run-time coefficients.

No upstream Python module, physical ant execution, row decoder, coefficient recipe, upstream saved row schedule or upstream saved arithmetic schedule is executed. The new compiler reads the pinned JSON description as finite data and lowers its fixed combinatorial specification algebraically. The fixed row program is not applied to any ant or Boolean tape state. `prefix_rows` is deliberately not read. All powers and geometric sums appearing in the arithmetic source are paid.

## 1. Occurrence constants

Let R=601547591, S=576000, V=400(R+2)=240619037200, u=2V and Z=3^400. For instruction kind a and adjacent-pair index s, define

    T[a,s] = sum { Z^r : 0<=r<R and the fixed row specification has kind a,index s at r }.

The 957 possible pair indices are s=0,...,956, and a belongs to DUP,NAND,MOVE_LEFT,MOVE_RIGHT. In particular these are fixed integers, not witnesses or oracles.

A monotone run starts at time n, slot s and direction d in {-1,1}, has length L, and contributes Z^(n+k) at slot s+d*k. Introduce events +Z^n at s and -Z^(n+L) at s+d*L. Sweeping slots in direction d using

    value[s] = Z*value[s-d] + event[s]

recovers exactly that run: induction gives Z^(n+k) on its L visited slots and zero thereafter. Linearity establishes the same statement for every overlapping run. Exterior events at -1 and 957 are paid but unused. Singleton DUP/NAND events are accumulated directly.

The compiler lowers the fixed description as follows. A DUP word at logical size m/index i is a decreasing MOVE_RIGHT run of length m-i-1 followed by a DUP singleton; a NAND word is a NAND singleton followed by an increasing MOVE_LEFT run of length m-i-2. An interchange is the displayed fixed24-word specification, updating only the compile-time size parameter. A copy is one DUP word followed by m-i-1 interchanges. A gate is two copies and a NAND singleton. Top-level RANGE nodes contribute one monotone run. These finite identities are transcriptions of the pinned formal row specification, not claims about machine behavior.

Maintain an arithmetic wire P=Z^n. Each nonempty run computes Pnext=P*Z^L, with Z^L built once per occurring length by an explicit binary chain. Thus neither exponent lookup nor division is hidden. Each directional run costs 1 M+2 A after its cached power; each singleton costs 1 M+1 A. Four directional sweeps cost 4*957 M and 4*957 A, and their two kind-wise sums cost 2*957 A. The literal zero costs 1 A; Z costs its binary-chain multiplications.

The executed new symbolic compiler produces R rows using 5,456,442 runs, of which2,724,814 are directional and 2,731,628 singleton. It uses 2,730,765 words,113,709 interchanges and 1,749 copies. The exact occurrence-source cost is5,469,985 M +8,186,999 A=13,656,984 gates. The source is topological and has only literal 1/3 leaves. Its canonical stream hash and source/data pins are in `occurrence-receipt.json`.

## 2. Disjoint geometric decomposition

In one macro use canonical400-height bands y=50+400r,...,449+400r. Bulk bands r=1,...,R consist of all 958 DELAY templates, both turning routes (including the prior left-turn tail), and the vertical return wire. Black sets are unioned before they are encoded. A bulk slab contains 2,695,878 black cells.

For each operation kind a, let Q[a,dx] be the signed ternary400-vector obtained from the black indicator of its two-slot operation template minus that of two adjacent DELAYs. Every nonzero correction lies strictly in y=56,...,449 (NAND in57,...,297), so its support misses consecutive-band overlaps. It also misses every routing margin. The23 black cells shared by DELAY and its next-round translate agree for all pair operations and are owned by the following canonical band. Therefore replacing two DELAYs by one operation is exactly addition of Q, with no double black digits or carries. Same-row tiles outside the two replaced slots are disjoint from the correction.

Let B[x], H[x], F[x] be the unsigned400-digit bulk, header and footer profiles at x mod S, with their respective digit zero at y=50,50,F0+50, where F0=400(R+1). Header union includes the previous staggered macro's footer tails; footer union includes the previous round's common tails. All remaining fixed routes are explicitly unioned in these finite boundary profiles. The next vertical macro uses profiles at x-S/2 mod S. Exact finite-set checks, including black/white compatibility, certify this decomposition independently of R.

Define

    G = 1+Z+...+Z^(R-1)
    C[x] = sum_(a,s,dx: x=600(s+1)+dx mod S) Q[a,dx] T[a,s]
    U[x] = B[x] G + C[x].

Then U[x] is exactly the bulk column, with each400-digit band aligned to its own start. Q may be signed, but the theorem identifies the resulting coefficients with Boolean colors. No claim relies on treating a signed redundant digit expansion as already carry-free.

## 3. The y=75 cut and full coefficient identity

Write Hlow[x] for the first25 ternary digits of H[x], and Hhigh[x] for the remaining 375 digits, so H=Hlow+3^25 Hhigh. These two constants are built separately from the same fixed bits, without division.

Define

    Full[x] = H[x] + Z U[x] + 3^(V-400) F[x]
    Cut[x] = Hhigh[x] + 3^375 U[x] + 3^(V-425) F[x]
    Tile[x] = Cut[x] + 3^(V-25) Full[x-S/2] + 3^(u-25) Hlow[x].

The three summands are disjoint consecutive vertical regions, namely the first macro after cutting off its first25 header rows; the full second macro; and the 25 wrapped header rows. Their exponents follow directly from y-75. Consequently

    Tile[x] = sum_(i=0)^(u-1) c(x,i+75) 3^i.

The Report44 label tile:j aliases Tile[(288650-j) mod S]. Its first:j aliases the fixed header bit at y=75, namely digit 25 of H at that x. Anchor coefficients are rebuilt by the unchanged221-digit signed Horner grammar from the pinned anchor JSON. The remaining named constants and literals are also rebuilt with paid arithmetic.

## 4. Division-free geometric sum and source domains

For n>=1, construct a pair (P_n,G_n)=(Z^n,sum_(k=0)^(n-1)Z^k). Start(P_1,G_1)=(Z,1). A doubling uses P_2n=P_n*P_n and G_2n=G_n+P_n*G_n (2 M+1 A). A following odd step uses P_(2n+1)=P_2n*Z and G_(2n+1)=G_2n+P_2n (1 M+1 A). This is an ordinary binary finite grammar, with no division or input-dependent exponentiation oracle.

All new wires are degree-zero constant expressions. The existing two-input and one-input arithmetic streams can therefore retain their exact coefficient labels, witnesses, residual equations, and variable degree. The complete-ant conclusions remain conditional on precisely the existing inherited theorems; this prefix construction adds no theorem about ant dynamics, no positive witness and no equation.

## 5. Exact finite-source ledger

The complete generated prefix costs 13,182,377 multiplications and 15,898,997 additions/subtractions, totaling 29,081,374. This is an exact count of the provided grammar, not an optimized bound.

Stage | M | A
---|---:|---:
Occurrence constants | 5,469,985 | 8,186,999
Small profiles and remaining basic literals | 324,462 | 324,464
Geometric sum and five shifts | 283 | 45
Operation corrections | 3,227,004 | 3,227,004
Bulk/boundary/period join | 4,032,000 | 4,032,000
584 anchor rows | 128,480 | 128,480
Remaining named constants | 163 | 5
Total | 13,182,377 | 15,898,997

The small-profile cache contains 736 nonzero400-digit signed or unsigned profiles,21 nonzero25-digit profiles and 81 nonzero375-digit profiles. Thus its Horner cost is736*399+21*24+81*374=324,462 of each operation type. The remaining 2 A form minusOne and 2; zero was already paid by the occurrence source. Zero profiles alias the paid zero.

The four correction templates have763,1159,678,772 nonzero horizontal columns respectively for DUP,NAND,MOVE_LEFT,MOVE_RIGHT. Each is multiplied by all 957 occurrence constants, and every result is added, so this stage costs 957*(763+1159+678+772)=3,227,004 of each operation type. No multiplication by a possibly zero occurrence constant is silently omitted.

For every one of 576,000 horizontal coordinates, the stated bulk, Full, Cut and Tile source uses exactly 7 M+7 A, giving4,032,000 of each. It then aliases the 1,152,000 tile/first labels without arithmetic. The anchor stage retains every one of 584*220 multiplications and additions. The final named constants use independent binary chains of lengths47,50,10,55, plus one multiplication for9 and 5 additions/subtractions.

Adding the unchanged Report44 main source gives:

- Two raw inputs:14,335,963 M +17,052,868 A =31,388,831 operations,465 positive witnesses, one equation
- One raw input:14,335,967 M +17,052,874 A =31,388,841 operations,467 positive witnesses, one equation

Both retain exact variable degree 2,304,000. The old dense coefficient prefix cost 554,386,261,707,905,131 operations; this construction saves554,386,261,678,823,757. The prefix alone is smaller by a factor about19,063,276,092. The comparison concerns these two specified grammars and is not an optimality or novelty-priority claim.

All1,152,598 coefficient labels are retained. The canonical full new arithmetic source has SHA256 `6a01d7c1d8ee6b268d49c921b3263b578c152e49c62810d5aa877a4103cb9759`; its output-label alias map has SHA256 `87c890e3fe7bb138378d09df71125cc5783219b99d171ed426ed9791b0cdcc3e`. These hashes identify the new stream and alias map; equality with the old coefficient values is established by the geometric and algebraic proof, not by pretending the old astronomical prefix was executed.

Independent audit results, when present, are distinguished from the compiler's own receipts under verification. No ant-dynamics theorem is strengthened by finite profile checks.

## 6. Full literal binding

`SPLICE.md` defines the exact prefix-to-main operand map, ID offset, domain declarations, residual metadata and final-zero binding. `join_strict.py` implements that transform using only the pinned own-code Report44 arithmetic generator and its reconstructed component data, then validates every resulting operand and counts/hashes both complete sources. This is separate from, and does not execute, the upstream physical-ant or coloring recipes. The joined receipt records actual generation status and hashes.
