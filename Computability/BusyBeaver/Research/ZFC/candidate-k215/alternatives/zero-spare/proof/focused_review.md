# Independent focused review: Z215 source schedule and protected tail

**Result: PASS, as an ordinary mathematical argument.** I independently reviewed
the new all-natural two-entry debt bound, bound its command arities and control
conventions to the exact 4,751-row source, and checked its use for initial tuple
`[N,T,W,A,D,H,X,Y,L]=[1,0,5,0,0,0,0,0,0]`. This is not a proof-assistant theorem.
The inherited numerical-calculus calibration and strong proof compiler remain
explicit mathematical dependencies.

`review_schedule_source.py` imports neither the parent's schedule program nor
any inherited source interpreter or TM checker. It reads the source as data and
reconstructs primitive successors from binary paths. Its actual result is
`focused_review_receipt.json`. No full binary runtime proof was rerun for this
focused review; that obligation already passed all6,176 guarded cases.

## Exact source and field arities

The audited source SHA-256 is
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.
Selector decrements at ordinals23,24,25 route tag0 to NIP at4725, tag1 to DROP
at4698, tag2 to MP at4591, and every tag>=3 to AX at26 with residual tag-3.

All increment/decrement accesses to retained proof-list register L are:

| Purpose | Ordinals |
| --- | --- |
| Fetch / continuation wrapper | 0,3 |
| Common selector unpair | 9,18 |
| First AX payload unpair | 159,168 |
| Second AX payload unpair | 200,209 |
| MP payload unpair | 4591,4600 |

The eleven-instruction unpair blocks starting at9,159,200,4591 have identical
opcode/register words and identical complete guarded graphs after translating
ordinals. Their contracts replace y by its second Cantor projection f(y),
retaining the first projection in scratch before transfer. The following
transfers use destinations A,H,D,D. NIP and DROP contain no L access. Thus the
extra field arities are exactly0,0,1,2 for NIP,DROP,MP,AX.

At root, positive L is first decremented and then decoded; zero L triggers a
fresh fetch of N and increments N once. Hence suffix r>0 executes word r-1,
whereas fresh candidate n executes word n. The source's early literal execution
independently confirms this convention.
The only increment/decrement accesses to N in the complete source are ordinals
2 and6 in the fetch wrapper; commands cannot alter the enumeration counter.

## NIP tests before popping

The sole CH is4736; the first NIP stack access is4737 (`CD W`). No W access
precedes it inside NIP. The fragment sets scratch X to1 and compares H with1.
For H=0 or H>=2 it clears the comparison scratch and proceeds to unpair W.
For incoming H=1,X=0 its exact path is
`4725,4726,4727,4728,4726,4730,4736`, leaving W unchanged. Therefore a halt is
licensed by the incoming cached theorem1 before any next stack head is read.

## Independent finite base

I recursively expanded each complete command word n=0..665 and directly summed
its prefixes, instead of using the parent's b/m recurrence. The975 resulting
command occurrences have global minimum-3. Starting from candidate1 gives
minimum-2. The least completed balance after candidate6 is7, and B(665)=5762.
Since T(36)=666, this is the entire base through Cantor diagonal35, rather than
an empirical extrapolation.

## All-natural induction

For n=P(t,y), the command/delta/suffix triples are `(NIP,-1,y)`, `(DROP,1,y)`,
`(MP,0,f(y))`, and `(AX,10,f(f(y)))` for t=0,1,2,>=3. Successful MP actually
pushes truth, so delta0 is conservative even when I(0,0)=0 causes success.
There are at most n+1 commands in word n, hence m(n)>=-(n+1).

Set g(0)=0 and g(r)=b(r-1) for r>0. Inclusive sums of g are bounded below by
p(t)=[0,-1,0,-2,-2,-2,-2] through6 and7 thereafter. Cantor diagonals give the
first projected prefix bound

`q(T(d)+e) = sum(p(j), j<d) + p(e)`.

For d>=7 this equals `7d-58+p(e)`, and is nonnegative when d>=9. The finite
part has minimum-11 and total negative contribution-224. A second diagonal
decomposition therefore bounds every prefix sum of g(f(f(y))) below by-235.
This estimate includes prefixes ending inside a diagonal.
The independent review script recalculates both finite constants directly.

The first k AX words have balance at least10k-235. Inside the next AX word,
the bound is at least9k+10-235 because f(f(k))<=k and m(r-1)>=-r. Both bounds
are nonnegative for k>=26; the review script also directly expands and checks
all prefixes of the first26 AX words, independently of the parent's recurrence.

On diagonal s the last three words are MP,DROP,NIP. Their worst combined loss,
including internal prefixes, is at most `(s-2)+(s-2)+(s+1)=3s-3`. The first
s-2 AX words therefore leave every final-tail prefix at least

`10(s-2)-235-(3s-3) = 7s-252 >= 0` for s>=36.

The induction is well-founded: all b/m arguments used while proving diagonal
s are below its first candidate T(s). The projected-sum argument never assumes
a future balance bound. Every new diagonal stays above its starting balance,
preserving B>=7. The global minimum remains-3, from the finite base. Word0 is
one NIP of balance-1; omitting it raises all subsequent prefixes by1 and gives
the required debt-two theorem from candidate1.

## Soundness of W=5

Unpairing gives `5=P(0,P(0,1))`: two truth entries above arbitrary tail1. Top T
and cache H begin at0. Track the theorem-valued prefix above tail1, initially
of size2. Actual stack growth is at least the conservative schedule growth,
so the prefix size never becomes negative. Immediately before a nonhalting NIP
pop it must be positive, since that pop's counted endpoint is also covered by
the prefix bound. Tail1 is never decoded.

AX pushes the permitted axioms, dominated row, theorem-only generalization of
the cache, and old theorem-valued top. DROP pushes the old top. Successful MP
pushes truth. Every nonhalting command preserves the theorem invariant; a halt
tests the already established cached theorem1. This uses neither Con(ZFC) nor
a theoremhood assumption about the hidden tail. Inherited raw numerical
calibration turns the resulting numerical refutation into a ZFC refutation.

For a concrete encoding check, literal source execution processes candidates
1..5 as `DROP; NIP,NIP; MP(0); DROP,NIP; NIP,DROP`. Stack values at successive
command boundaries are `5,20,5,2,5,20,5,2,5`. MP(0) succeeds via I(0,0)=0;
the conservative proof already allows its extra push. The next fresh fetch
has registers `[6,0,5,0,0,0,0,0,0]`. This confirms the field and continuation
conventions directly in the pinned source.

## Completeness and arbitrary retained tails

The inherited command-local strong compiler for a derived X works from every
`(t,w,0,0)`, preserves retained w, and returns X or halts earlier. Its explicit
push/pop counts do not decode the retained tail. `START_Y=AX(0;1,Y)` resets
counter/cache from any incoming retained tuple. The compiled refutation plus
`DROP;NIP;NIP` therefore halts even above an arbitrary untrusted retained tail.

Its candidate code is `P(3,P(Y,P(1,R)))>=Y`, so Y at least the finite cutoff1
gives a cofinal family of successful candidates. Every earlier nonhalting
candidate drains: positive continuations are decremented; field readers leave
tails at most their input; arithmetic macros terminate on naturals. Thus a
finite ZFC refutation eventually causes a halt. Completeness does not require
the hidden tail to satisfy a theorem invariant.

Together with the complete blank prefix and quantified zero-spare runtime,
this supports the equivalence in ZFC for Z215. It proves neither unconditional
nonhalting, a214-state construction, nor state minimality.
