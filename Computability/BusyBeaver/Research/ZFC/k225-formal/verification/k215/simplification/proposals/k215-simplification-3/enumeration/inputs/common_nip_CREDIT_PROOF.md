# Exact common-NIP scheduler credit and cofinality

## Result for the actual startup

For the ordinary increment-by-one scheduler starting with next candidate
N=1 and residual pointer L=0, assign conservative command balances

    R = -1,     M = -1,     A = +9.

Each command first consumes one stack head. A then emits ten heads; its
transient balance is therefore -1, even though its final balance is +9.
Successful M replaces its consumed head by zero, improving its actual
balance to 0; that improvement is deliberately ignored below.

**Exact conservative boundary debt is 3; exact debt including internal
pops is 4.** From ten protected theorem heads, at least seven remain at
all complete command boundaries and at least six throughout the common
NIP pop. Both debts are attained in the conservative syntactic schedule:
W(1);W(2) is M;R;R, followed by the first pop of A in W(3).

This is an all-natural proof, not a bound extrapolated from testing.
The argument applies to every finite executed prefix before a possible
sound halt. It does not assume nonhalting in order to establish safety.

## 1. Exact source/parser premises

The source is `../../calculus/common_nip/a40_CC3.sites.json`, SHA-256
`83676e82d3b80150cf68b3b52ab72acf5b0c1ae2a6f7d2c3500bef3d17ab71c1`.
Its independent source audit is
`../../calculus/common_nip/source_packet/source_audit.json`.
The source worker confirmed the following exact half-open ordinal ranges:

* 0..9: unchanged scheduler. If L>0, decrement L. Otherwise fetch L=N
  and increment N. Scratch X is restored to zero.
* 9..23: unchanged field reader, unpairing L into command tag A and
  residual L.
* 23..49: common NIP; it does not alter N, A, or L.
* Ordinals49 and50: successive decrements of tag register A distinguish
  tag0 R, tag1 M, and tag>=2 A.
* A body51..4616 has two further field readers, at184..198 into H and
  225..239 into D, each taking one left projection and leaving the right
  projection in L.
* M body4616..4722 has one further field reader at4616..4630 into D.

Consequently R reads one field total, M two, and A three. There is no
hidden fourth A field. The A body contains no increment/decrement of N,
so the startup's N=1 survives its completion unchanged.

The checker independently compares the first23 primitive operations to
the pinned parent, locates these14-operation reader words, checks the two
selector decrements, and checks the stated noninterference registers.
The complete CFG audit and primitive meanings are separate source/runtime
premises; literal word equality alone does not prove their semantics.

## 2. Syntactic words and balances

Let P be Cantor pairing, f its right projection, and T_s=s(s+1)/2. Thus

    unpair(T_s+y)=(s-y,y),  0<=y<=s.

Let W(n) be the command word obtained from a freshly fetched candidate n,
disregarding semantic halts. Put Remainder(0)=empty, and
Remainder(r)=W(r-1) for r>0. The decrement belongs to a continuation, not
to the first command of a freshly fetched candidate. If unpair(n)=(a,y),
then exactly

    W(n)=R ; Remainder(y)           when a=0;
    W(n)=M ; Remainder(f(y))        when a=1;
    W(n)=A ; Remainder(f(f(y)))      when a>=2.

All suffix arguments are at most n. Whenever a suffix is nonempty its
next candidate index is strictly less than n. Induction therefore proves
that W(n) is finite, with length at most n+1, and Remainder(r) has length
at most r. The schedule is well-defined independently of possible halts.

Every command has final balance at least -1 and internal minimum at
least -1 relative to its entry. Therefore every prefix, including an
internal-pop point, of Remainder(r) has balance at least -r. This follows
by counting the at most r commands: at a point inside the j-th command,
the preceding j-1 completed commands lose at most j-1 and the current
command loses at most one more.

Let b(n) be the final balance of W(n). Let m_b(n) and m_t(n) be its minimum
boundary and transient prefix balances, including the empty prefix. Set

    B(k)=sum_{n<k} b(n),
    g(0)=0, and g(r)=b(r-1) for r>0,
    q(r)=g(r)+1.

The local conservative event sequences can be taken to be
R=(-1,+1,-1), M=(-1), A=(-1,+10). For A it suffices that the unchanged
old A body never reads its incoming opaque tail and prepends ten theorem
heads; intermediate construction steps do not require another tail head.
The command contracts are proved separately in `PROOF.md`.

## 3. Prefix pullback and the corrected induction invariant

If q has nonnegative initial partial sums, so does q composed with f.
Indeed f(0),f(1),... is the concatenation

    [0], [0,1], [0,1,2], ... .

Any initial segment is a union of complete blocks followed by an initial
partial block. Apply this twice to obtain the claim for q composed with
f twice. Only the finitely many q-prefix sums involved in a given
application are needed.

For k>=1,

    sum_{r<k} q(r) = 1+B(k-1)+(k-1).

Thus the sufficient invariant is B(j)+j>=-1, NOT the stronger >=0.
The shift q=g+1 remains valid even though B(3)+3=-1; the corresponding
q-prefix sum is exactly zero. No shift by2 is necessary.

The exceptional initial words are

    W(0)=R,  W(1)=M,  W(2)=R;R.

Hence B(0),B(1),B(2),B(3) are0,-1,-2,-4. The invariant B(k)+k>=-1
holds through k=3, and the boundary before diagonal2 has B(3)=-4.

## 4. All-natural diagonal proof

Induct jointly on Cantor diagonals to establish:

1. B(k)+k>=-1 at every completed candidate prefix;
2. B(T_s)>=-4 at every diagonal boundary;
3. for each s>=2, every complete-command prefix of its diagonal has
   balance>=0 relative to the diagonal start, every transient prefix has
   balance>=-1, and its final balance is at least6s-9>=3.

The initial three candidates supply the base. Fix s>=2. The diagonal
positions y=0,...,s-2 begin with A; position y=s-1 begins with M;
position y=s begins with R.

For the first k A candidates, 0<=k<=s-1, the final relative balance is

    9k + sum_{y<k} g(f(f(y))) >= 8k.

This is the pullback lemma applied to q=g+1. The needed induction
instances have indices at most s-2, strictly less than T_s, so there is
no circular use of the current diagonal.

Before A candidate y, balance is at least8y. Its initial pop gives at
least8y-1>=-1. After its complete A command, its continuation has length
at most f(f(y))<=y, so every subsequent boundary or transient prefix has
relative balance at least

    8y+9-y = 7y+9 > 0.

Thus the A portion has nonnegative boundary prefixes and transient
prefixes>=-1. After all s-1 A candidates its balance is at least8(s-1).

The next M candidate costs at most one initially and at most f(s-1)<=s-1
through its continuation. Every boundary/transient prefix and its end
therefore have relative balance at least

    8(s-1)-1-(s-1) = 7s-8.

The last R candidate costs at most one initially and at most s through
its continuation. All its boundary/transient prefixes and its end are
therefore bounded below by

    7s-8-1-s = 6s-9 >= 3.

This proves assertion3. Since the diagonal starts at B(T_s)>=-4, its
candidate boundaries have B(k)>=-4. For k>=3 this gives B(k)+k>=-1.
Its end also has B>=-4, completing the joint induction.

This covers internal A pops even inside recursively parsed continuations,
not just the leading commands of candidates or a long-run average.

## 5. Exact debts at cutoff1

Before diagonal2 the boundary minimum from candidate0 is -4. Every later
diagonal starts at B>=-4 and has nonnegative relative boundary prefixes,
so the global boundary minimum from candidate0 is exactly -4.

Every later diagonal has relative transient minimum -1, attained at its
first A pop. Therefore the global transient minimum is at least -5.
It is attained at the first pop in W(3), immediately after B(3)=-4.
Thus the exact transient minimum from candidate0 is -5.

Removing W(0), whose balance is -1, shifts all subsequent balances by+1.
From cutoff1 the exact boundary and transient minima are consequently

    -3 and -4.

The boundary witness is after W(1);W(2)=M;R;R. The transient witness is
the immediately following initial A pop in W(3). Successful M commands
may improve an actual run; these are exact debts of the conservative
schedule, not a claim that every actual run attains both minima.

For completeness, exact conservative credit at any cutoff N is computable
from a finite word, without a truncation heuristic. Choose s with
T_s<=N<T_(s+1), and set E=max(3,T_(s+1)). Inspect W(N) through W(E),
including internal pops. E begins a complete diagonal of index>=2;
W(E) is its sole leading A command with empty continuation, and captures
its minimum -1. The rest of that diagonal never drops below its start;
later diagonals start at strictly greater credit and have the same
relative transient lower bound. Hence no later prefix can lower the
minimum already inspected. The corresponding boundary minimum needs only
W(N) through W(E-1). This optional generalization is not needed for the
actual cutoff1 bootstrap.

## 6. Protected arbitrary tail

Maintain a logical list of theorem heads above a fixed arbitrary natural
tail J. Its length is proof bookkeeping, not the length of a canonical
numerical decoding. The pairing identity unpair(P(x,v))=(x,v) holds even
when P(0,0)=0; explicit zero heads are legitimate protected resources.
Assume theorem-valued top and cache at the completed startup boundary.

Starting with ten heads, the conservative bound gives at least seven at
every command boundary and at least six after the common initial pop.
Thus every common NIP consumes an explicit theorem head, never a head of
J. R's remaining push/pop uses the theorem-valued top and consumes its
own temporary head. M's success uses the consumed theorem major and the
theorem top; it produces a theorem consequent and a zero head. Failure
produces theorem zero. A's old body prepends its ten theorems and does
not inspect J. Extra successful-M zeros may be retained as additional
protected heads and cannot weaken the bound.

All cache/top halting guards therefore see theorem codes. A halt yields
a proof of1. If it halts partway through a command, this conclusion uses
only the invariant before that guard and does not require the command to
return. The numeric contents of J are unrestricted.

Four heads would suffice for these conservative command contracts, while
three would not suffice at the first A pop. The actual ten-head bootstrap
has the stronger7/6 margins proved above.

## 7. Exact matched-bootstrap application

The verified source-level startup premise is the interior point of the
unchanged old A body beginning at ordinal51 with

    (N,T,W,A,D,H,X,Y,L)=(1,0,2,0,0,0,0,0,0).

Its source prefix has177 primitive steps to the separately matched
physical frame at ordinal84. These177 steps are not the entire A body.
The corresponding virtual complete new A input has W=P(0,2)=5, top0,
cache0, counter0, zero parameters, and N=1,L=0. Its common NIP safely
consumes the leading theorem zero and gives exactly the old-body W=2
seed. No assumption about the contents of tail2 is made.

The retained A-body contract supplies termination and its ten theorem
heads above that same opaque tail2, with theorem top/cache0, N=1, and
residual L=0. Applying sections5--6 gives the7/6 margins forever after,
or a prior sound halt. The old A-body contract permits reaching this
boundary mathematically; one need not simulate its enormous formula codes
literally after the matched finite prefix.

The reported70506-transition blank run and full physical-frame equality
are separate binary premises. This proof neither rechecks nor infers
those facts from credit or source size. A frame match must include the
complete store, source ordinal, scratch/address fields and whole-tape
admitted-frame requirements established by the runtime audit.

## 8. Cofinality and completeness bridge

Every W(n) is finite by section2. Its source subroutines terminate on
natural registers by the separate command/runtime contracts. Hence if
no semantic halt occurs, a candidate finishes and the empty-residual
scheduler fetches the next N, then increments N. Induction shows that
every candidate n>=1 is eventually fetched. Protected credit prevents
any earlier candidate from obtaining a spurious refutation from J.

More specifically, let r be the exact residual-pointer encoding of any
fixed suffix V (r=0 for an empty suffix, otherwise1 plus the fresh-candidate
encoding of V). For every Y,

    n_Y = P(2,P(Y,P(1,r)))

starts with A(0;1,Y), according to the source's H-then-D field order, and
has residual r. Thus it continues with exactly V; also n_Y>=Y. The
compiler's universal-entry suffix can therefore be placed in cofinally
many candidates. For the suffix proved in `PROOF.md`, each such candidate
halts whenever the numerical calculus has a proof of1, from every natural
entry store (or it has already halted). Increment-by-one enumeration
reaches one of them.

This establishes the scheduler/credit bridge for the existing strong
compiler. It does not replace that compiler proof, the accepted numerical
calculus/ZFC calibration, or the physical/runtime/startup certificates.

## 9. Independent finite corroboration

`check_credit.py` imports only the standard library and executes no
inherited proof or checker. It computes500000 candidate summaries,
independently expands1000 command words, and checks997 complete diagonals.
It rechecks the shifted q-prefix invariant and records both exact debts,
the attaining candidates, and7/6 margins in `credit_result.json`. It also
performs the literal source checks in section1.

The first invocation completed the mathematical tests but used an incorrect
relative directory for the source file; it stopped with FileNotFoundError.
The path was corrected and the complete checker rerun. No mathematical
assertion or expected debt was relaxed. The unbounded argument is sections
2--8, not extrapolation from this finite run.

## Portable reproduction

The checker defaults to the two local files in `inputs/`, whose SHA-256
identities are enforced before source checks. It accepts explicit
`--source` and `--parent` paths to those same pinned inputs. It writes no
file by default, printing its receipt to stdout; `--output PATH` requests
a new receipt at the chosen path. For example, from any working directory:

    python /path/to/common_nip_repair/check_credit.py --output /tmp/common_nip_credit.json

The input source hash is recorded in section1. The pinned parent hash is
`05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922`.
The include-ready self-contained mathematical section is
`research_sub214d/report_draft/sections/credit.tex`.

## Conditional reuse for a guardless common-pop variant

The numerical credit argument depends on the unchanged parser, R/M net
loss at most1, A net gain at least9, the one-head initial pop, and the
old A-body opaque-tail contract. It does not depend on the incoming-cache
halt test being present. Therefore deleting only that test leaves this
credit theorem available **if a separate exact-source/command audit proves
all those same effects for the new source**, including R's final stack
loss1 and internal minimum-1. This is conditional reuse, not a source
certificate or a complete soundness/completeness proof for a guardless
variant. All source hashes, local input files and current receipts in
this directory continue to refer exclusively to the guarded a40_CC3
source; none is silently transferred to a changed machine.
