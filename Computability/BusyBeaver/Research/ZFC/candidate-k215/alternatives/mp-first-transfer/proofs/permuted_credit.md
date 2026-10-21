# Independent protected-tail proof for MP=0, S=1, AX>=2

This note concerns the new tag-permuted three-command source, not the
unpermuted S=0/MP=1 scheduler. It proves the exact conservative initial
stack credit at next-candidate cutoff 1: **one theorem head suffices**.
The matched AX bootstrap supplies ten, leaving a permanent margin of
nine explicit theorem heads over its arbitrary numerical tail.

The proof assumes the separately checked command contracts and physical
source correspondence. It does not infer a binary runtime theorem from a
finite scheduling experiment.

## 1. Commands, fields, and the syntactic schedule

Let P(x,y)=(x+y)(x+y+1)/2+y and let f(n) be the second component of its
inverse. The command fields are exactly

    MP(x): [0,x],       S: [1],       AX(c;x,y): [c+2,y,x].

The theorem applies to either of two explicitly different transfer-pop
commands, both denoted S in the syntactic scheduling equations below:

- The single-guard command S halts exactly when cache h=1 and otherwise
  returns (h,w,d,z) from (t,[z;w],d,h). A source implementation is
  clear-top; copy-cache-to-top; old-NIP, provided the copy preserves cache.
- The composite command S' halts when h=1 or t=1 and otherwise has the
  same return map. Its source implementation is old-DROP; old-NIP;
  old-NIP. The first old-NIP tests old h, and the second tests saved old t.

The compiler and source bindings must identify which command a table
implements. This note does not silently replace one guard by the other.
MP and AX have their inherited contracts. The proof below depends only
on the common nonhalting stack effect; the two guards are handled in the
soundness and completeness discussion.
For stack-credit purposes either S or S' costs one explicit head, failed MP costs
zero, successful MP adds a theorem zero, and AX adds ten theorem heads.
We conservatively ignore the successful-MP extra head and assign

    weight(MP)=0, weight(S)=-1, weight(AX)=10.

Let W(n) be the finite command word parsed from freshly fetched candidate
n, continuing syntactically even where an actual semantic execution
might halt. Set R(0)=empty and R(r)=W(r-1) for r>0. If unpair(n)=(a,y),
then the exact recurrences are

    W(n)=MP;R(f(y))       when a=0,
    W(n)=S;R(y)           when a=1,
    W(n)=AX;R(f(f(y)))    when a>=2.

MP consumes its own payload field, S consumes none, and AX consumes two
payload fields after the selector. The outer minus one in R arises from
the scheduler's decrement before every continuation command. A freshly
fetched candidate has no such initial decrement.

Every residual r is <=n. When r>0, the recursive candidate is r-1<n;
therefore W(n) exists and has at most n+1 commands by induction. R(r)
has at most r commands, so every prefix of R(r) has weight at least -r.
This bound includes all recursively decoded continuations.

Write b(n) for the total weight of W(n), m(n) for its minimum prefix
weight, including the empty prefix, and B(k)=sum_{n<k}b(n). Define

g(0)=0 and g(r)=b(r-1) for r>0.

## 2. Cantor prefix pullback

If q(0),q(1),... has nonnegative initial partial sums, then so does
q(f(0)),q(f(1)),.... Indeed f in natural input order is the concatenation

    [0], [0,1], [0,1,2], ... .

Each initial segment consists of whole such blocks followed by one
initial part of a block. The corresponding q-sums are nonnegative.
Applying the lemma twice handles q(f(f(y))). The argument is finite at
every use and needs only the previously established partial sums that
occur in those blocks.

Use q(r)=g(r)+1. For k>=1 its first k terms sum to

    sum_{r<k}q(r)=k+B(k-1).

Thus the induction invariant B(j)+j>=0 implies nonnegative q-prefix
sums. Using g alone would be incorrect, since the initial schedule has
negative balance.

## 3. Every Cantor diagonal from index 2 is prefix-safe

Write T_s=s(s+1)/2. The first three words are

    W(0)=[MP],      W(1)=[S],      W(2)=[MP].

Hence B(0),B(1),B(2),B(3) are 0,0,-1,-1. These values establish
B(k)+k>=0 through k=3 and B(T_2)>=-1.

We induct over complete Cantor diagonals, maintaining both
B(k)+k>=0 for all candidate boundaries already passed and
B(T_s)>=-1. Fix s>=2. The diagonal candidates T_s+y, 0<=y<=s,
have selector a=s-y. Consequently the first s-1 candidates are AX,
the next is S (y=s-1), and the last is MP (y=s).

For the first k AX candidates, 0<=k<=s-1, the total balance is

    10k + sum_{y<k}g(f(f(y))) >= 9k.

This follows by applying the prefix-pullback lemma to q=g+1. Its
required earlier arguments are at most s-2, strictly smaller than
T_s. Thus the induction is not circular.

Before the AX candidate at position y, relative balance is at least
9y. Its initial AX adds 10, and every prefix of its continuation
R(f(f(y))) loses at most f(f(y))<=y. All its nonempty prefixes therefore
have relative balance at least 9y+10-y=8y+10>0. Its empty prefix has
balance at least 9y. After the whole AX part, balance is at least
9(s-1).

The S candidate has one initial cost -1 and continuation R(s-1),
which loses at most s-1 at any prefix. Throughout this candidate the
relative balance is therefore at least

    9(s-1)-1-(s-1)=8s-9.

The final MP has initial cost zero and continuation R(f(s)), which
loses at most f(s)<=s at any prefix. Its relative balance is at least

    8s-9-s=7s-9>0              for every s>=2.

Thus every command prefix of the entire diagonal is nonnegative
relative to its beginning, and its total balance is at least 7s-9.
Every new candidate boundary has B(k)>=-1. Since k>=3 here, it also
has B(k)+k>=0, completing both induction invariants.

## 4. Exact credit at cutoff 1

Starting at candidate 1, the exceptional initial segment is
W(1);W(2)=[S,MP], with minimum -1 and final balance -1.
Every subsequent diagonal has index s>=2 and is prefix-safe relative
to its own beginning. Therefore every prefix of the entire infinite
syntactic schedule beginning at 1 has balance at least -1.
The first S attains -1, so the required **conservative** credit is
exactly one. Actual successful MP steps can only improve this bound.

More generally, for any cutoff N choose s with T_s<=N<T_(s+1), and
set E(N)=max(3,T_(s+1)). The negative of the minimum prefix balance
of the finite word W(N);...;W(E(N)-1), or zero if nonnegative, is the
exact conservative credit for the infinite schedule. Every later
whole diagonal is prefix-safe; the finite segment includes its own
final boundary, so a later diagonal cannot introduce a lower minimum.
This is a finite exact formula justified by the infinite theorem,
not a heuristic truncation.

## 5. Explicit theorem heads protect an arbitrary encoded tail

Fix any numerical tail J. Represent the working stack as a finite
explicit list of native theorem codes above J, and assume the top and
cache are native theorems. If the initial list contains at least one
head at cutoff 1 with empty proof pointer, the credit theorem ensures
that its conservative length never becomes negative.

Immediately before a nonhalting S, the conservative length is at
least one: its subsequent length must remain nonnegative after the
cost -1. Thus the popped head belongs to the explicit theorem list,
not to J. S moves only theorem-valued cache/head data. AX prepends ten
theorem heads, and successful MP adds a theorem zero. The other MP
branch does not pop a head. For the single-guard S, a halt tests theorem-valued
cache 1. For the composite S', a halt can additionally test theorem-valued
top 1. Either case certifies a native refutation.

This argument counts explicit wrapper-list length, not the numerical
size of the Cantor code. It remains valid at the zero alias P(0,0)=0:
the exact identity unpair(P(x,v))=(x,v) allows one to remember and later
remove an explicit zero head even when its integer encoding is
unchanged. No uniqueness of list length is needed or asserted.

If an actual semantic execution halts, the reasoning applies to its
finite prefix. Defining W without semantic halts never assumes that
the real machine runs forever.

## 6. Application to the new physical bootstrap

For the already matched tag-permuted composite candidate, the separate
blank execution reaches, after 68,442 binary steps, the specified source
ordinal 55 with complete logical register vector [1,11,2,0,0,0,0,0,0]. This is an **interior AX frame**, not a
clean command root. The synthetic source-prefix check starts the
same AX at ordinal 25 with [1,0,4,0,0,0,0,0,0] and reaches that exact
interior frame after 174 source primitives. These are external exact
matching premises of the present note. For a later source implementing
the shorter single-guard command, the same argument applies if that
source's own physical startup and exact AX-prefix match are established;
the earlier measurements are not automatically inherited.

The unbounded AX contract therefore completes this shared suffix to
a command root with next candidate 1, empty proof pointer, top/cache
zero, and the stack

    [rho1,...,rho7,rho8,Q_0(0),0; 4],

with all axiom arguments zero. The gate is zero. Every displayed head
is a theorem. The numerical tail 4 contains falsity heads
(4=P(1,1), 1=P(1,0)), so it cannot be declared a theorem stack.
Instead the ten explicit theorem heads protect it. The one-head
credit bound leaves a permanent conservative margin of nine.

The strong transfer compiler is independent of raw command tag values.
Its original single-guard S blocks apply directly. Replacing every S by
S' preserves each "halts or returns exactly the required tuple" contract:
the two executions have identical stores until S' possibly halts on its
additional top-falsity guard. A newly emitted gate, implication, or
quantifier code is never 1, so the auxiliary exact PUSH/H/DISCARD
calculations also retain their stated behavior. Re-encode MP and the
chosen transfer command using the new field list. This is a proof for
both implementations, conditional on their own literal source bindings.
Its cofinal shell still begins with AX(0;1,Y), whose candidate number
is P(2,P(Y,P(1,R))) for the appropriately re-encoded finite suffix R.
These numbers dominate Y. Thus refutational completeness holds from
this cutoff and this protected arbitrary tail, while the preceding
invariant supplies soundness. The finite blank prefix, all-natural
primitive runtime, AX suffix contract, and inherited dominated
calculus/ZFC calibration are separate necessary premises.

## 7. Independent finite corroboration

`permuted_credit_check.py` is a new standard-library-only checker and
imports no repository code. It checks 500,000 recursively defined
candidate summaries, explicitly expands the first 1,000 command
words, and verifies all command prefixes of 997 complete diagonals.
It finds the global minimum -1 from cutoffs 0 and 1, credit 1 at
cutoff 1, and margin 9 for ten startup heads. The record is
`permuted_credit_result.json`. These finite results corroborate the
indexing and bounds; Sections 1-5 prove the all-natural theorem.
