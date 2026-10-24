# Independent ordinary review of the shifted-t guard

Verdict: **PASS for the final ordinary72-predicate source equivalence.**
This review independently read the entire final proof, focused checker and
stdlib-only peer audit in `research/shifted-t-index-guard`, together with the
relevant partial73 and corrected74 arguments. No mathematical gap was found.
The reviewed ordinary packet manifest SHA256 is
`e62f2ddce24b9a9fd02ffc31a8c6ba75d68eb65e6a23b4557dff2899ad4987dd`;
its proof SHA256 is
`a00c5df7cf7c7efc0870acce657d78ed291e651e1768298273c9626f55923a5f`.
All complete final-file bindings are retained in this profile packet's source
pins. The full73 chain is licensed only after raw825 has been recovered.

Raw825 is the actual shifted-t slack, with X=raw821,Y=raw822,k=raw110.
Its only original source use is row762, outside0..642 and the actual
43-argument frame. Dropping its guard therefore leaves the early ordinary73
proof through raw104 sign recovery intact: that partial argument uses only
the641-coordinate prefix, weak frame, calls0/2/9 and paired seeds0/4.
It does not require the shifted-t seed or its missing index bound. The
bootstrap and positive V product similarly require no825 sign. All source
rows remain present, so the exact slack, norm and congruence identities
continue to hold as unrestricted polynomial equalities.

The corrected74 argument is then used only through its local factorial0
and t/k122 recovery. Its local seed dichotomy and weak-radix digit argument
use K/shifted-K seeds1/2 and calls1/5/6. They handle possible collapsed
seeds before giving f=K! and its parity. The t norm and literal call2
residue provide the parity relation, and the paired-slack product recovers
t/k122 using safe supports0/9. No shifted-t bound, call7 meaning, g=t!,
choose-one binomial meaning or moduli-product decoding is used here.

Exactly calls0,1,2,3,4,5,6,8,9 now use the four recovered pairs at t,K,
shifted-K,k122. Call7 is deliberately excluded. In particular calls4/8
give Nt=(1+g*t²)^t and raw547=b^t. The prefix already gives g>=0 and
every actual digit/remainder coordinate used below nonnegative. The literal
source rows give C1=raw114+raw115+1>=1 and

    raw546=b^t*C1+b^t*b*raw548+raw549 >= b^t*C1.

This is an inequality from actual coordinates, not an assigned binomial
meaning for C1 or an interpreted call7 output.

Suppose the shifted-t seed has |Y|=1. Its norm gives X=+/-A. With
n=b+1>=3,m=raw546>=0 and the actual T=2An-n²-1, the frame gives n,m<W
and A>W^W>W². Consequently

    T-(2A+n+m)=2A(n-1)-n²-n-m-1 >= 4A-W² > 0,
    2A>n+m.

The four literal call7 residues are n,-2A+n,2A-n,-n. The differences
between each of the last three and m are nonzero and have absolute value
below T. They cannot satisfy the congruence. The first forces m=n since
|m-n|<W<T. Thus the only collapsed possibility is X=A,Y=1,m=b+1.
This uses the actual call7 congruence under the small-ordinate assumption;
it does not require k<=|Y| or interpret call7 as a k-th power.

For t>=2, the preceding row inequality gives m>=b²>b+1 because b>=2.
For t=1, the already interpreted call4 gives Nt=1+g. Its actual ceiling
g*C1=Nt+raw115 therefore yields

    g*(C1-1)=1+raw115>0.

With integer g>=0,C1>=1 this forces C1>=2. Hence m>=2b>b+1 for t=1
as well. No g=t! or factorial1 semantics has entered this boundary case.
The exact combined source cut and substitution giving this positive constant
are independently recollected by both the stdlib peer and this profile
checker; omitting that constant would invalidate the argument.

Thus |Y|>=2. Ordinary Pell classification now gives |Y|>=2A>W>k,
supplying the missing short interval for the signed comparison-index
theorem. It identifies the absolute coordinates at the true k. Actual
call7 at base b+1>=3 then excludes the other three X/Y orientations:
they force T to divide m*n^k+1,m*n^k-1 or m+n^k, each nonzero with
absolute value below T. The middle expression cannot vanish since
n>=3,k>=1. Consequently X,Y are positive and Y>k. The original slack
identity gives raw825=Y-k>0 at the unchanged source body tuple.

A fresh Legendre triple supplies exactly the missing73rd predicate; the
complete73 theorem may now be used. Conversely forget precisely the825
triple. Every original row and all other triples are retained in these
existence maps; no uniqueness or inverse choice of the fresh triple is
claimed.

The final focused checker verifies95 complete source identities,573 ordered
signs,429 strict constructors and the exact chronology, and rejects16
corruptions. The separate PEER_AUDIT.py uses only the standard library and
independently recollects15 cuts, the actual ports4/7/8, the single825 use
and the t=1 identity. The profile checker pins and replays both in each
interpreter mode. Its own four weak-frame/D/k122 cuts and seven shifted-t
cuts additionally bind the required source interfaces. Finite controls
supplement the unbounded argument; no sampling establishes the theorem.

This approval concerns ordinary source zero-existence equivalence only.
Projected metrics require the separately generated complete quartics and
independent checks in this packet. No native calibration, internal-ZFC or
Lean theorem is asserted. No frozen source was edited; Lean remains paused.
