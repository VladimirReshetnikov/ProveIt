# Asymmetric linear-input and auxiliary-gap degree tradeoffs

The scale **X=wq, Y=sq³** extends to the complete linear-input89 and
positive auxiliary-gap families, with their actual compiler contract,
ordinary positive input and **19 strictly positive witnesses** unchanged.
The resulting union with the frozen asymmetric87/88 grouping family has
this operation/exact-degree frontier:

    87/169, 88/125, 89/113, 90/109, 91/104, 92/92,
    93/72, 94/62, 95/60, 96/50, 97/48, 98/44.

The points87/169,88/125,91/104,93/72 belong to the already proved
[three-base asymmetric grouping family](complete75_asymmetric_factor_partitions.md).
The new endpoints below come from ten explicitly enumerated bases.
Every grouping preserves its base's entire supplied positive zero set.
The scale change is a bijection with its own frozen parent's positive
integer zeros, rather than an arbitrary-integer coordinate substitution.
No polynomial operation bound below87, comparison bound below75, or
minimum degree across all arithmetic circuits is claimed.

| New-family operations | M | A | Exact degree | Certificate gates | Equations | Base |
|---:|---:|---:|---:|---:|---:|---|
|89|47|42|113|88|1|linear, coupled eight units|
|90|47|43|109|89|1|gap, coupled eight units|
|91|47|44|108|90|1|gap, uncoupled eight units|
|92|48|44|92|84|3|linear, coupled seven plus strong comparison|
|93|48|45|84|82|4|linear, six plus two comparisons|
|94|48|46|62|83|4|linear, coupled seven plus strong comparison|
|95|48|47|60|84|4|gap, coupled seven plus strong comparison|
|96|48|48|50|82|5|linear, coupled seven plus strong comparison|
|97|48|49|48|80|6|linear, six plus two comparisons|
|98|48|50|44|81|6|gap, six plus two comparisons|

The new-family91/108 and93/84 rows are dominated in the displayed union
by the historical91/104 and93/72 rows. The source retains both finite
frontiers explicitly. Counts include numerical multiplications, squares,
residual subtractions and the complete polynomial finalizer.

## 1. Exact source change and the retained contracts

Keep every fixed-compiler hypothesis in
[linear-input89](complete75_linear_input_modulus89.md), including B=2^d,
d>=4, the actual layout and masks, MC=2 modulo4, MF=4 modulo8,
0<MC,MF<B−1, popcount(MC)+popcount(MF)=d, and the positive odd input
suffix b<B. All synchronization, transport and ordinary-input conditions
are retained. The nineteen positive coordinates are

    J,F,alpha,zplus,f,h,i,j,o,s,w,g,eta,zeta,y,Z,delta,rho,sigma.

In the gap bases, e replaces y as a supplied positive coordinate and
one paid addition reconstructs y=V+e, exactly as in the frozen
[auxiliary-gap family](complete75_auxiliary_gap_degree_tradeoffs.md).
Source names are Jrep,tau_gap,y_aux,aux_gap for J,g,y,e.

Definitions are

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, A=a+2,
    Delta=A²−1, H=4a+3, D=X+ac+(rho+sigma)H,
    C=q−F−Z−alpha−2dx, W=C−Z, u=2dx+b,
    kappa=u+delta*(a+1), mu=W+a*kappa+rho*H,
    G=q²−Z−qF,
    R=G(q²−1)+(MC+q(MF+B−1))J,
    K=Delta*(f²−1), T=ic², V=of−c, U=jc−R.

As in the parents, source register A stores Delta. Use the factors

    N0=g²+E*(kY)*(2g−k),
    N1=D²−Delta*c², N2=mu²−Delta*kappa²,
    N3=K*(V²−y²)+y²,
    Nk=k−R−hE,
    Nt=(DC+B*DR+X)C+(q−F)−zplus(q−1),
    Ns=1+T²−K,
    L=V−jc+k−hE, L0=1+V−U.

They satisfy L=L0+Nk−1. U and L0 are paid only when needed. The
coupled and uncoupled products are respectively

    N0*N1*N2*N3*Nk*Nt*Ns*L−1,
    N0*N1*N2*N3*Nk*Nt*Ns*L0−1.                    (1)

The [checker](complete75_asymmetric_linear_gap_tradeoffs.py) guards the
complete selected frozen source, comparisons, witness list and output.
It changes only `wn2=w*n2` to `wn2=w*q`; `n2=q³` remains live in
`sn2=s*n2`. This applies directly to linear89, all six frozen
[linear-input grouping schedules](complete75_linear_input_degree_tradeoffs.md),
and all four frozen gap schedules. Their operation counts are unchanged.
The [receipt](complete75_asymmetric_linear_gap_tradeoffs.json) contains
these eleven complete direct transfers and the new frontier schedules.

On arbitrary rational tuples with q nonzero, the maps

    w_old=w_new/q²,  w_new=q²*w_old                (2)

preserve every computed register, comparison and complete polynomial.
All other coordinates are fixed. In particular V=of−c and y=V+e are
independent of X and w, so the gap reconstruction commutes with (2).
The inverse in (2) is often nonintegral off the zero set; its integrality
at positive zeros is proved next.

## 2. Recover positivity before using an auxiliary Pell index

Consider a positive zero of either product in (1), first allowing the
gap reconstruction y=V+e to be signed. Every factor is an integer unit.
The retained negative-Pell descent for N0 and the modulo-four arguments
for N1,N2,N3,Ns give

    N0=N1=N2=N3=Ns=1, K=T².

These exclusions do not need the input-index modulus Delta: N2 is used
only as a norm at this stage. Nor do they need y positive:
K=Delta*(f²−1) is0 or1 modulo4, so N3 is congruent to y² or V² even
for signed y,V. Thus changing kappa to u+delta*(a+1) and computing
y from a positive gap does not alter this first sign step.

Weak transport Nt=±1 forces C>=0 and F+Z<q. The unchanged packing
estimate gives

    (2q−1)(q²−1)<R<q⁴−q³,
    q>=16, X>=q, Y>=q³, E>=q⁴>R+q³.              (3)

Let Nk=epsilon and let lambda denote L in the coupled case or L0 in
the uncoupled case. The first and main positive roots supply indices
n,p with

    k=2psi_P(n), P=2XY²+1>A,
    c=psi_A(p), D=chi_A(p), p>n,
    2n=R+epsilon+vE, v>=0, n>=(R−1)/2.           (4)

Here P=1 modulo E and0<R+epsilon<E. Crucially, no claim v=0 has yet
been made. The large lower bound on n gives c>A*Delta² and c>2p;
also c>kY>2(R+2).

The generic ordinary strong-rank lemma now applies to T²=K using only
the first/main norms, index, strong equation and bounds (3)–(4). It gives

    f=chi_A(m), c divides m, m>=c>2p,
    T=Delta*psi_A(m), f>2c.

Therefore V=of−c>c>1. In a gap base this proves y=V+e>0 **before**
classifying the auxiliary Pell norm. This is the positivity dependency
needed to extend the scale argument to that family. For the direct-y
bases, y was already supplied positive.

## 3. Main-power recovery and the positive inverse

The common rank and lower-ratio proof is the ordinary part of
[asymmetric scale Sections2–4](complete75_asymmetric_scale_tradeoffs.md).
Its required hypotheses have all just been verified. To make the
uncoupled branch and the weaker E bound explicit, the signed auxiliary
step-down has target

    Jtarget=R+epsilon−lambda    (coupled),
    Jtarget=R+1−lambda          (uncoupled).

In either case0<Jtarget<c/2 and0<p<c/2. The retained equations and
positive y,V therefore give p=Jtarget, with R−2<=p<=R+2.
If v>=1 in (4), then

    2n>=R−1+E>2R+q³−1>2(R+2)>=2p,

contradicting n<p. Thus2n=R+epsilon. In the coupled case,
p=2n−lambda, and lambda=−1 is excluded by Pell duplication and the
upper ratio c<k(Y+1). In the uncoupled case,
p−2n=1−lambda−epsilon; every sign pair except epsilon=lambda=1 has
p>=2n+1 and is excluded by the same inequality. In both cases write

    p=2r+1, n=r+1, r>=1.

The lower-ratio estimate, requiring only6XY²>a, yields

    c/(k/2)> (X+1)^(2r)/X^r,
    Y> X^r/3, a> X^(r+1)/3 > 2^(2r+1), X<a.     (5)

No upper binomial-error bound or prior q³ divisibility of X is used.
For z_j=chi_A(j)−a*psi_A(j), the recurrence with z0=1,z1=2 gives
z_j=2^j modulo H=4a+3. The actual main-root definition therefore implies
X=2^p modulo H. Both X and2^p are positive and below a by (5), hence

    X=2^p.

Since q divides X, q=2^t for t>=4. Equations (3) and the bound p>=R−2
give p>3q>3t. Thus q³ divides X, and w_old=w_new/q² is a positive
integer. Identity (2) now restores a positive zero of the **selected
frozen parent**, including its smaller input modulus, complete output,
strong equation and positive domains. Its full input theorem and sign
recovery apply. In particular every individual unit factor is+1.

Conversely, any positive zero of the selected parent maps by
w_new=q²*w_old to a positive new zero, with all registers unchanged.
The two maps are inverse. This proves the full positive-zero bijection
for both products, and then for every direct frozen grouped schedule.
It does not restrict witnesses to a canonical Pell extension.
The gap coordinate retains its parent's separate positive bijection
y=V+e, e=y−V; no new assumption about computed positivity has been added.

## 4. Ten explicit grouping bases and exact source costs

For each coordinate choice (linear y or positive gap e), enumerate:

| Treatment | Factors | Additional comparisons | Linear core | Gap core |
|---|---|---|---:|---:|
|coupled eight|N0,N1,N2,N3,Nk,Nt,Ns,L|none|81|82|
|uncoupled eight|N0,N1,N2,N3,Nk,Nt,Ns,L0|none|82|83|
|coupled seven|N0,N1,N2,N3,Nk,Nt,L|T²=K|79|80|
|uncoupled seven|N0,N1,N2,N3,Nk,Nt,L0|T²=K|80|81|
|six|N0,N1,N2,N3,Nk,Nt|T²=K, U=V|78|79|

Every base is rebuilt from its complete canonical parent and pruned only
to the ancestry of its factors and comparisons. There are no unused
gates or dangling supplied ports. The seven-factor comparisons restore
Ns=1. The six-factor comparisons restore Ns=L0=1. Consequently group
products equal to one imply one of the full product equations (1), so
Sections2–3 apply even before positivity of computed y has been proved.
Conversely every individual factor is+1 at those positive zeros.
Thus **every disjoint partition has precisely the same supplied positive
zero set within its base**.

Allow either a sum of squares of all comparison and group residuals,
or one distinguished group product U times one plus the sum of the
remaining squared residuals, minus one. In the latter case
U(1+S)=1 over integers forces U=1,S=0; no factor-positivity assumption
is needed. The empty remaining sum is emitted as U−1 directly.

For core size C, n factors, m additional comparisons and g groups, the
literal operation count is

    C+n+3m+2g−1,

except for m=0,g=1 with that group distinguished, where the count is
C+n. Group multiplication costs n−g; every subsequent residual, square,
addition and anchor operation is charged. There are m+g equations and
19 supplied positive witnesses. No source search outside these ten
factor/comparison bases is claimed; in particular this is not a search
over alternate transport recodings or arbitrary circuits.

## 5. Exact degrees and finite optimality

Give every supplied coordinate and x degree one and fixed numerals degree
zero. Let Q=(B−1)J, k0=eta+zeta, gamma0=rho+sigma,
Ctop=Q−F−Z−alpha−2dx and g0=2g−k0. The nonzero highest forms are

| Factor | Linear-y degree | Highest form |
|---|---:|---|
|N0|12|w*s²*k0*Q⁷*g0|
|N1|18|8gamma0*k0*w²*s³*Q¹¹|
|N2|20|4delta*(2rho−delta)*w³*s³*Q¹²|
|N3|24|f²*k0²*w²*s⁴*Q¹⁴|
|Nk|7|−h*w*s*Q⁴|
|Nt|3|w*Q*Ctop|
|Ns|22|i²*k0⁴*s⁴*Q¹²|
|L|7|−h*w*s*Q⁴|
|L0|6|−j*k0*s*Q³|

For the gap bases only N3 changes: the identity

    N3=V²−(K−1)*e*(2V+e)

gives degree20 and highest form2e*f²*k0*w²*s³*Q¹¹.
The full strong residual T²−K has degree22, and U−V has degree6.
These forms follow from the actual source, including its norm
cancellations; naïve operation-by-operation maximum-degree propagation
would overestimate several of them.

Products add these exact degrees. Squares of real polynomial leading
forms cannot cancel in a sum. Thus, for group weights s_j and maximal
ordinary residual degree r0, the exact final degree is

    2max(r0,s_1,...,s_g)                            (SOS),
    s_a+2max(r0,{s_j:j!=a})                        (anchor a).

The subset dynamic program computes the minimum of these formulas for
every group count. A separate restricted-growth Bell enumeration checks
all20,474 partitions and102,902 SOS/anchor choices across the ten bases.
Each linear-y base has minimum attainable degree48; each gap base has
minimum44. The checker also enumerates every nonempty distinguished
subset to certify that no anchor escapes these family floors.

For direct transfer without repartitioning, the eleven frozen schedules
have the following new degrees:

    linear89:113; linear90:112; linear92:92; linear94:62;
    linear95:60; linear96:50; linear97:48;
    gap90:109; gap91:108; gap98:44; gap99:44.

The new-family ten-row table above is the exact operation/degree frontier
of the stated ten-base objective. The opening twelve-row list is its
finite union with the frozen three-base frontier. Those union points
remain separate literal sources, with their respective witness coordinate
systems and strong treatments; this does not assert identical supplied
tuples across different coordinate systems.

## 6. Reproducible evidence and scope

Run the checker with `--write` to regenerate its receipt, or with no
arguments for an exact fresh replay. The author audit verifies all eleven
direct sources,1,408 complete two-direction register/output identities
(704 signed),704 separately evaluated manual outputs, and641 cases
where the off-zero rational inverse is nonintegral. The gap audits
include200 assignments with negative computed y; these are algebra
fixtures, not positive compiler zeros.

The72 optimal-by-group-count schedules across the ten bases pass literal
counts, dependency closure and1,152 independent parent/manual finalizer
identities (576 signed). Sixty-two weighted polynomial slices check
factor leading coefficients and direct/frontier exact degrees. The
checker rejects122 modified-source, domain, comparison and partition
callers and checks1,600 coupled/uncoupled first-index wrap boundaries.
None of these finite algebra or degree fixtures is claimed to
materialize a complete universal-compiler Pell zero. Positive soundness
and completeness are supplied by the proof above and the retained parent
compiler theorems.

Author writer78872 and a separate fresh default replay12446 passed on
the final source and receipt. All seven local links resolve.

Gibbs's independent full proof/source/dependency review and fresh72062
passed with no findings. A separate oracle enumerated all20,474
partitions,102,902 literal objectives and1,654 anchor-floor subsets;
checked152 emitted opcode/liveness ledgers; and verified704 complete
two-direction register/output maps (352 signed),352 manual direct-factor
outputs and1,216 manual grouped outputs (608 signed). It included323
nonintegral inverse and101 negative reconstructed-y cases, all72
group-count winner and11 direct exact-degree slices, and1,800
coupled/uncoupled wrap boundaries. The review independently checked the
positivity-before-auxiliary-index order, smaller input modulus, complete
factor signs and full within-base positive-zero equivalence. Seven links
and whitespace passed; no target source or receipt was edited, and no
full Pell-zero fixture was claimed.

Root also read the complete proof and source and ran fresh replay29146,
with no findings. A further independent rational-coordinate/manual-finalizer
audit checked576 complete outputs and every retained parent register
(288 signed) across all72 group-count winners. Literal opcode totals
agreed in every case.
