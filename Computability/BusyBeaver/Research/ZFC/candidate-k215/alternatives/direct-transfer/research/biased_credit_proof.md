# A protected-credit theorem for a hypothetical skipped-candidate parser

**Status: abstract scheduling lemma only. It does not apply to the archived
scratch-biased source or transition table.** The ordinary all-natural proof
below treats the intended parser equations as a mathematical definition.
The incoming `T215_Transfer_2026-10-20` packet claimed those equations for its
scratch-biased experiment, but that claim is false: its `CC3` at source
ordinal4697 returns to selector ordinal23, not scheduler ordinal0. After
the initial AX it enters S with scratch X=1 and halts after15 more source
transitions. `reject_biased.py` and `biased_rejection.json` give the exact
dual-CFG audit and trace. Thus this note cannot calibrate that table or
establish any Busy Beaver bound. It remains potentially useful for a future
implementation of the intended abstract parser.

## 1. Defining the hypothetical words and weights

Let `P(a,b)=(a+b)(a+b+1)/2+b`, write `unpair(n)=(a,y)`, and let
`f(n)=second(unpair(n))`. Put `T_s=s(s+1)/2`. The projection sequence is
`f(T_s+y)=y` for `0<=y<=s`, and `f(n)<=n/2` for all natural n.

The fresh-candidate word W(n), ignoring semantic halts, has recurrence

- a=0: `W(n)=S ; W(y-1)` if y>0, otherwise just S;
- a=1: `W(n)=MP ; W(f(y))` if f(y)>0, otherwise just MP;
- a>=2: `W(n)=AX ; W(f(f(y)))` if f(f(y))>0, otherwise just AX.

The asymmetry is essential: S leaves scratch bit 0, while MP and AX leave
scratch bit 1. For a positive residual r the next read is from r-1 after S
and r after MP/AX. Zero residual always ends the candidate. All recursive
indices are strictly below n, so W(n) is a finite word for every n.

Assign `wt(S)=-1`, `wt(MP)=0`, and `wt(AX)=10`. This ignores the additional
truth head pushed by a successful MP. Let b(n) be total weight and let D(n)
be minus the minimum prefix weight, including the empty prefix. Let
`e(0)=0` and `e(r)=D(r)` for r>0, and `q(n)=2^D(n)`.

The exact debt recurrences are:

- a=0: `D(n)=1` if y=0, and `D(n)=1+D(y-1)` otherwise;
- a=1: `D(n)=e(f(y))`;
- a>=2: `D(n)=max(0,e(f(f(y)))-10)`.

## 2. Pointwise and prefix exponential bounds

**Lemma 1.** `q(n)<=n+2` for every n.

Proof by strong induction. The S case n=0 gives equality 2=0+2. For y>0,
`q(n)=2q(y-1)<=2y+2<=P(0,y)+2=n+2`; the last inequality is equivalent to
`y(y-1)>=0`. In the MP case the suffix is empty or uses a smaller index
r=f(y), giving `q(n)<=r+2<=n+2`. The AX case has
`q(n)=max(1,2^e(r)/1024)`, which obeys the same bound. In particular,
`e(r)<=r`: this is immediate at r=0 and r=1, and for r>=2 follows from
`2^r>=r+2` and `2^D(r)<=r+2`.

**Lemma 2 (Cantor prefix pullback).** If `sum_{r<k} v(r)<=C*k` for every
needed k, then `sum_{y<k} v(f(y))<=C*k`, and also the twice-pulled-back
version. Subtract v from the constant C and use that the f-sequence is the
concatenation `[0];[0,1];[0,1,2];...`. Every finite initial segment consists
of full blocks and one initial partial block. Only the earlier prefix
bounds encountered in these finite blocks are required.

**Lemma 3.** `sum_{n<k} q(n)<=4*k` for every k.

Induct over Cantor diagonals. Diagonals s=0,1 have q-values `[2]` and
`[1,4]`, which obey the claim at every prefix. For s>=2, its first s-1
candidates are AX, followed by MP, followed by S. For the first k AX
candidates, each with y<k, the q-sum is at most

    k + (1/1024) sum_{y<k} q(f(f(y))) <= (257/256) k.

For a zero suffix we have q=1, so using q(0)=2 in this upper bound is
harmless. The pullback uses only bounds at smaller candidate indices than
T_s, already established by induction. The MP contribution is at most
`f(s-1)+2 <= (s+3)/2`. The S contribution is at most `2q(s-1)<=2s+2`.
Thus the full diagonal q-sum is at most

    (257/256)(s-1)+(s+3)/2+2s+2
    = (897s+639)/256 <= 4(s+1).

Every AX prefix satisfies its required 4k bound. The prefix including MP
has sum at most `(385s+127)/256<=4s`. Thus the claim holds at every new
candidate boundary, completing induction.

Since `d<=2^d/2` for every nonnegative integer d, Lemmas 2 and 3 imply

    sum_{y<k} e(f(f(y))) <= 2k.                         (1)

## 3. Arbitrary skipped-candidate schedules

**Theorem.** Let V be any infinite increasing sequence of candidate numbers
whose consecutive differences are 1 or 2. Restrict V to a complete Cantor
diagonal s>=5. The concatenation of its selected W(n)'s has nonnegative
weight at every command prefix, relative to its initial balance.

No assumptions about why an index is skipped are made. In particular the
statement applies to either the correct one-candidate-lag bias recurrence
or any independently verified scheduler with the same gap bound.

There cannot be two consecutive omitted indices. In the first k AX positions
of the diagonal there are therefore at least floor(k/2) selected candidates.
An AX at y has total weight at least `10-e(f(f(y)))`. By (1), the sum over
any selected subset of the first k positions is at least

    10 floor(k/2)-2k >= 3k-5.                          (2)

At the very small boundaries k=0,1 this estimate is replaced by the exact
observation that no selected AX has run, or only the y=0 AX has run and
contributed exactly 10. For k>=2 the right side of (2) is nonnegative.

At a selected AX position y, the balance before it is at least `3y-5`.
After its initial AX and at every prefix of its suffix the balance is at least

    3y-5+10-e(f(f(y))) >= 3y+5-y/4 >= 0,

using `e(r)<=r` and `f(f(y))<=y/4`. Empty prefixes were covered by the
previous paragraph. Thus the entire selected AX portion is prefix-safe.

After all s-1 AX positions its total is at least `3s-8`. If selected, the
following MP can lose at most `e(f(s-1))<=(s-1)/2`, and the final S can lose
at most `1+D(s-1)<=s`. These are whole-word prefix-loss bounds, and also
bound their possible negative total weights. Consequently every prefix
through these final two words is at least

    3s-8-(s-1)/2-s = (3s-15)/2 >= 0.

This proves the theorem, including all nested continuations and every
possible skipped-candidate set with gaps at most two.

## 4. A hypothetical initial condition

Suppose an independently constructed implementation reaches a complete
command root with N=1, empty residual L, scratch bit b=1, theorem-valued
top/cache, and ten explicit native theorem heads above an arbitrary tail J.
This is an assumption about a hypothetical implementation, not a state
reached by the archived scratch-biased table. That table instead follows
the erroneous return into S and then halts, as explained above.

The intended abstract scheduler copies old N into the candidate pointer and increments N by
`1+b`, where b is the incoming bit before the new candidate starts. Hence
if n is the freshly loaded candidate and b is that incoming bit, the next
candidate is n+1+b, while the new bit is the indicator that W(n)'s last
command is MP or AX. This has one-candidate lag when expressed in terms of
previously completed words. Its gaps nevertheless lie in {1,2}, precisely
the hypothesis of Section 3.

The entire initial selected prefix below T_5=15 is:

|Candidate|Incoming bit|Command word|Cumulative weight|Next candidate|
|---|---:|---|---:|---:|
|1|1|MP|0|3|
|3|1|AX|10|5|
|5|1|S, MP|9|7|
|7|1|AX|19|9|
|9|1|S, S, S|16|11|
|11|0|AX|26|12|
|12|1|AX|36|14|
|14|1|S, AX|45|16|

Its minimum command-prefix weight is exactly 0. All subsequent selected
full diagonals satisfy Section 3; index15 is simply the first omitted
position of diagonal5. Therefore the infinite syntactic schedule has
nonnegative conservative weight at every command prefix from this startup.

**Abstract corollary.** If an implementation realizes the equations of
Section1 and this initial condition, all ten explicit theorem heads remain
as a conservative margin above arbitrary tail J. Before each S at least
one explicit theorem head is available. If S's only halt guard tests the
theorem-valued incoming cache and AX/MP have their stipulated contracts,
then halting of that hypothetical implementation implies a native
refutation. The archived scratch-biased source does not meet these premises.

The explicit-list invariant uses `unpair(P(x,w))=(x,w)` and does not assume
that the numerical stack uniquely encodes its length. It is valid even
when P(0,0)=0. Strong command/compiler completeness, cofinality, and a
correct implementation of the defining equations remain separate
obligations. This note supplies only the abstract protected-tail lemma.

## 5. Computational corroboration and scope

`biased_credit.py` independently expands the hypothetical first eight candidates
and checks the q-bounds through 500,000 natural candidates. Those finite
checks corroborate the index conventions; Sections 1-4 prove the unbounded
result for the abstract equations. The archived table's full exact-table
symbolic runtime replay proves that it implements its own literal source;
it cannot repair the source's incorrect command-return edge. Its literal
blank/AX-prefix match likewise does not establish the intended parser.
Neither record supports applying this lemma to that table. No calibrated
machine, new transition table, or proof-assistant endpoint is claimed here.
