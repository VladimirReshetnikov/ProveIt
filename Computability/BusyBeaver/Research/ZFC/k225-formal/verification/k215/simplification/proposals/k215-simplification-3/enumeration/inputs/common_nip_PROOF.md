# Complete sentinel compiler for the common-NIP command system

Date: 2026-10-21. Status: command-level proof. Source binding, physical
runtime, protected-credit proof, and blank initialization are separate.
The source proposal factors one old NIP after decoding and before every
command branch. Its advertised price is 201 source DAG nodes, not a claim
here of a calibrated 215-state machine.

## 1. Exact interface

Write a numerical stack as [z;v] using the bijective Cantor pairing.
Each command first performs old NIP: test incoming cache h for 1, then
consume z into cache without changing top t or counter d.

The remaining R branch is old DROP;NIP. Its complete equation is

    R(t,[z;v],d,h) = (z,v,d,t), unless h=1 or z=1, when it halts.

The remaining AX branch is the old AX body. Call the complete command A.
A(c;x,y), if h!=1, returns

    (g,[r1,...,r7,L,Q_d(z),t;v],0,0),
    U=d, A=d+x, B=z+y, C=c.

Its gate and eight row families are unchanged. Its ten emitted heads
are above v, so net credit is +9. All rows and g are implication codes
and not 1; Q has tag 2. Only the saved old top can be 1.

The remaining MP branch is the old MP body. Call the complete command M.
For M(b), let Y=d+b. If incoming h=1, it halts in the common NIP.
Otherwise

    if z=I(t,Y), return (Y,[0;v],Y,0);
    otherwise return (0,v,Y,0).

The compared major is the consumed stack head z, not the old cache.
Success has net stack credit 0 and failure -1. Both clear cache.

I(a,b)=4P(a,b) is injective including I(0,0)=0; Q_i(a)=4P(i,a)+2.
The exact row formulas are retained in the companion symbolic core and
the original numerical-calculus specification. No axiom is deleted or
weakened in this proposal.

## 2. H: top-preserving pop

Put D=A(0;0,0), and H=D;R^10. From (t,[z;v],d,h), H halts exactly when
h=1 or t=1. Otherwise it returns

    (t,v,0,Q_d(z)).

Indeed D consumes z and emits the eight implication rows, Q_d(z), and t.
The first nine rotations cannot halt. The tenth checks and loads t,
leaving Q_d(z) in cache. The consumed z is not itself tested for 1 by H.
The cache need not be zero, but is always a non-1 quantified value.

## 3. K: retain a zero sentinel while storing the old top

Let

    K = D; H^8; D; H^9.

For every natural X,w and k!=1,

    (X,[0;w],0,k) -> (0,[0,X;w],0,q3),
    q3 = Q_0(Q_0(Q_0(0))).

K never halts on these inputs, including X=1, and never reads w.
The first D consumes zero. With U=A=B=C=0 its gate is zero, and its
last three heads are L(0,0,0,0)=0, q1=Q_0(0), and saved X. The eight
H calls remove the eight implication rows while preserving top zero,
leaving [q1,X;w]. Each H has a non-1 cache on entry and preserves top 0.
The second D consumes q1; its gate is still zero because C=A=0. Its
last two fresh heads are q2=Q_0(q1) and saved top zero, followed by X.
Nine H calls remove the eight rows and q2, leaving [0,X;w]. The last H
sets cache Q_0(q2)=q3. All intermediate tested heads belong to fresh
non-1 rows or quantified codes. Neither X nor w is exposed.

At X=0, K duplicates the zero sentinel:

    (0,[0;w],0,k) -> (0,[0,0;w],0,q3).

At arbitrary X it stores X immediately below the retained leading zero.
This is the needed replacement for ordinary MP(0) padding, which does
not work after the common NIP has made MP consume a head.

## 4. Strong contract and parameter setting

For each theorem X construct a finite B_X with

    (0,[0;w],0,k) -> halt or (X,[0;w],0,k'),
    for every natural w and every k!=1, with k'!=1.

The sentinel zero is part of the contract, not an assumption about w.
The old tail w is arbitrary and is never read by the compiled blocks.
Counter zero and top zero are required at entry. Cache zero is NOT
required. If the input cache is a theorem, the actual-run invariant below
also proves the returned cache a theorem; the arbitrary-input completeness
contract itself needs only k!=1. Truth B_0 is the empty word.

At top 0, counter 0, and a leading zero, define the head-consuming setter

    J(0) = R,
    J(i) = M(i) for i>0.

Both send (0,[0;v],0,k) to (0,v,i,0), for k!=1. For i=0, R consumes
the zero and copies old top zero into cache. For positive i, the common
NIP loads major 0, but I(0,i)>0, so M(i) fails and consumes that zero.
Using M(0) for J(0) would succeed and restore the zero, so it is wrong.

## 5. Axiom extraction

For target parameters U=u,A=a,B=b,C=c with u<=a, begin

    K; J(u); A(c;a-u,b).

K doubles the leading zero. J(u) consumes the first; A consumes the
second. Thus A's actual B parameter is b, not an uncontrolled old head.
Its ten fresh heads above the original w are

    [r1,...,r7,L,Q_u(0),0;w].

For ordinary row families take u=0. For dominated L use u<=a.
To select row j, 1<=j<=8, append

    R^j; H^(9-j).

Exactly the first nine generated heads are consumed: the selected row
becomes top, and all remaining rows plus Q_u(0) are removed. The final
saved zero remains as the required sentinel. The result is

    (rj,[0;w],0,Q_0(Q_u(0))).

For an enabled bundle use j=0 and H^9, retaining its gate on top and the
same sentinel. A disabled gate simply gives truth zero. All gate and row
values are non-1. Every removed head is fresh, and w is never accessed.

## 6. Modus ponens, major first

Let M0=I(A0,B0), and suppose B_M0 and B_A0 satisfy the contract. Define

    B_B0 = K; B_M0; K; B_A0; K; R; R; M(B0); H.

The initial K gives an extra zero behind the sentinel. The successive
major states, ignoring permitted early halts, are

    (0,[0,0;w],0,q3)             after initial K
    (M0,[0,0;w],0,k_M)           after B_M0
    (0,[0,M0,0;w],0,q3)          after K
    (A0,[0,M0,0;w],0,k_A)        after B_A0
    (0,[0,A0,M0,0;w],0,q3)       after K
    (0,[A0,M0,0;w],0,0)          after first R
    (A0,[M0,0;w],0,0)            after second R
    (B0,[0,0;w],B0,0)            after successful M(B0)
    (B0,[0;w],0,Q_B0(0))         after H, unless B0=1 and it halts.

The second R may already halt if A0=1, which is permitted. The common
NIP of M consumes the exact major M0; MP then succeeds by equality.
The two zeros after M consist of its replacement zero and the initial
extra padding zero. H removes one and leaves the required sentinel.
This is why the initial K is necessary. Every recursive entry has top 0,
counter 0, leading zero, and non-1 cache.

At A0=B0=0, M0=0 and M(0) intentionally succeeds. The zero alias causes
no count error: it replaces the consumed major by one zero, and H removes
that zero. All equations use pairing constructors even when P(0,0)=0.

## 7. Generalization

For theorem X and index i, define

    B_Q_i(X) = B_X; K; J(i); A(i;0,0); R^9.

After B_X and K the state is (0,[0,X;w],0,q3). J(i) consumes precisely
the leading zero and sets counter i, giving (0,[X;w],i,0). A consumes X;
its parameters are U=A=C=i and B=X, so its gate is disabled. Its fresh
heads are

    [r1,...,r7,L',Q_i(X),0;w].

Nine R calls give (Q_i(X),[0;w],0,L'). The new cache L' is an implication
row and therefore non-1. It need not be quantified or zero. This is why
the induction contract allows every non-1 cache. At i=0, J(0)=R has the
required consumption; substituting M(0) would leave an extra zero and
invalidate the equation. X=1 is also covered: A quantifies it without
checking it, and all popped fresh rows are non-1.

Sections 5-7 and the empty truth block give structural induction over
every finite numerical proof. No old tail head is read, and every
successful return preserves the sentinel and tail exactly.

## 8. STORE and universal entry

Define

    STORE_i = D; R^8; M(i).

For arbitrary (t,[z;v],d,h), STORE_i halts exactly if h=1, and otherwise
returns

    (0,[t;v],i,0).

After D;R^8, top is L, cache is r7, and stack is [Q_d(z),t;v]. The common
NIP in M(i) tests the non-1 r7 and consumes major Q_d(z), which has tag 2.
Its MP comparison is against an implication code, so it must fail, with
counter i because D cleared d. This proof is independent of the old top,
old head, raw-zero aliases, and the old counter.

Consequently STORE_0;STORE_0 maps every arbitrary input, unless it halts,
to (0,[0;v],0,0): first it replaces z by t while clearing top, then it
replaces t by zero. This is the required universal sentinel entry.

If the numerical calculus proves 1, the word

    STORE_0;STORE_0;B_1;R;R

halts from every natural store. If B_1 returns, its top is 1 and the
first R consumes the known sentinel zero, putting 1 in cache; the next
R halts. No old tail is needed for that final argument.

The exact positive-pointer codec is important, especially for final zero
R fields. Define F_R(q)=P(0,q), F_M(b)(q)=P(1,P(b,q)), and
F_A(c;x,y)(q)=P(c+2,P(y,P(x,q))). The AX field order is [c+2,y,x].
Set Tail([])=0 and Tail(C::v)=1+F_C(Tail(v)). A fresh candidate for C::v
is F_C(Tail(v)), without the first +1. The scheduler decrements each
positive residual pointer before decoding the next command. Therefore
Tail([R])=1 and Tail([R,R])=3; the fresh candidate 2 executes R;R.
The I/P zero alias does not erase final R commands in this codec.

For explicit cofinal candidates, let r=Tail(R^8;M(0);STORE_0;B_1;R;R)
and set N_Y=P(2,P(Y,P(1,r))). The initial command
is A(0;1,Y). If it returns, the following R^8;M(0) still consumes its
Q_d(z) as a tag-2 major and fails, giving (0,[old top;old tail],0,0).
STORE_0 then creates the sentinel. Since N_Y>=Y, successful candidates
are cofinal in the unchanged ordinary increment-by-one enumeration.

## 9. Soundness and the separate machine obligations

Maintain that top, cache, and all protected stack heads are theorems;
counter d is unrestricted. The common NIP tests theorem cache and loads
a theorem head. R transfers theorem data. M compares a theorem major
against I(theorem minor,Y), producing theorem Y on success or truth 0 on
failure. A emits the unchanged axioms, theorem Q_d(z), and saved theorem
t. Thus all halt guards see theorem codes, and a halt yields theorem 1.
The changed compiler cache convention does not alter the numerical calculus.

The exact conservative command weights are R=-1, M=-1, A=+9. Successful
M has actual weight 0, but ignoring its replacement zero is conservative.
Every command needs a protected head at entry. A has an additional
transient -1 before adding ten heads. The separate all-natural diagonal
credit proof for these exact weights establishes, from next candidate 1,
sharp command-boundary debt 3 and full internal debt 4. Ten initial
protected heads therefore leave at least seven at every command boundary
and at least six even at the internal low point. The bounds are attained
conservatively by W1=M, W2=R;R, then the initial pop of the AX in W3.
These strictly positive margins justify every common-NIP read, not just
the R reads. The old +10/MP0 conclusion is not being reused.

Blank initialization is also separate. The old virtual complete-AX seed
(0,4,0,0) has stack head 1 because 4=P(1,1); entering the new common NIP
there would load untrusted falsity. Any dirty cache 1 would immediately
halt. A valid binary startup must establish a protected theorem frame,
possibly at an interior point of the unchanged old AX body, or use a new
safe prefix. Source size and this universal compiler do not prove startup.

Under exact source/runtime/startup, the correct protected-credit bound,
and the inherited numerical-calculus/ZFC comparison, this system halts
exactly when ZFC has a refutation. This note supplies the complete
command-level compiler, not those remaining physical premises.

## 10. Exact clean startup theoremhood for the new 70,506-step candidate

The fresh allocator reports the following source/body match, which must
remain pinned to its independent binary/source receipts:

    old AX body entry ordinal 51:
      (N,T,W,A,D,H,X,Y,L)=(1,0,2,0,0,0,0,0,0);
    after 177 source primitive steps, ordinal 84:
      (N,T,W,A,D,H,X,Y,L)=(1,0,0,0,0,0,0,18,0).

The binary blank trajectory reaches the latter frame after 70,506
transitions with the reported zero scratch-spare condition. This paragraph
uses that exact matching premise; it does not derive the physical receipt.

A clean complete A(0;0,0) virtual input for this body is

    N=1, L=0, (t,w,d,h)=(0,P(0,2),0,0)=(0,5,0,0),

with the remaining command parameters and scratch registers zero. The
common NIP consumes its explicit theorem head 0, tests cache 0, and arrives
at the old body with W=2 and H=0. The old body therefore has U=A=B=C=0,
disabled gate 0, and on completion yields

    t=d=h=0,
    w=[r1(0,0),r2(0,0,0),r3(0,0,0),r4(0,0,0),
       r5(0,0,0),r6(0,0,0),r7(0,0,0),L(0,0,0,0),Q_0(0),0;2].

The first seven heads are retained axiom instances; L(0,0,0,0)=0 is the
dominated axiom/zero alias; Q_0(0) follows by GEN from truth 0; the last
head is truth 0. All ten are theorems and none equals 1. Top and cache are
truth 0. The numerical tail 2 is deliberately opaque and is not declared
a safe theorem stack. Indeed 2=P(0,1) and 1=P(1,0), so it contains a raw
falsity below its first head.

Completing the matched old-AX suffix leaves next candidate N=1 and empty
residual pointer L=0, because the body leaves those scheduler registers
unchanged. Thus the exact remaining credit obligation is the ordinary
common-NIP schedule from cutoff 1 with ten explicit theorem heads above
an arbitrary fixed tail. No assertion about every possible blank-start
translation, tail 4, or a complete AX_N entry at W=2 is used.


## 11. Integrated conditional calibration theorem

Fix the exact common-NIP source and binary identified by the physical
packet, the exact 70,506-step blank-frame/source-prefix match of Section
10, the all-natural primitive implementation contracts, and the unchanged
ordinary parser. The completed initializer gives ten theorem heads above
opaque tail2. The dedicated credit theorem supplies boundary/internal
margins 7/6 for the entire remaining run. Section 9 then proves that any
physical halt yields a derivation of raw code 1 in the retained dominated
numerical calculus. Conversely, if that calculus derives 1, Sections 4-8
construct a universally halting suffix and cofinally many candidates
containing it, so the ordinary scheduler eventually halts.

The retained numerical calculus is exactly truth 0, the seven displayed
row families, full gated bundle with its original side conditions,
dominated L(A,B,C,U) with U<=A, numerical MP, and theorem-only GEN. No
syntactic well-formedness restriction on natural payloads is added.
The actual-run invariant is membership in this numerical theorem set,
not an unsupported claim that every natural code has a standard formula
meaning. Thus malformed/junk codes in the opaque tail are never licensed
as theorems, while every raw emitted axiom instance is admitted exactly
under the inherited numerical specification, including zero aliases.

The separate inherited calibration supplies equality of the dominated
and unrestricted numerical theorem sets (its retained finite certificate
has 3,728 proof nodes and 5,160 shared term nodes), and the ordinary
proof-theoretic comparison between unrestricted numerical refutation and
ZFC refutation. Those inherited premises are retained as premises, not
re-proved here and not advertised as a new Lean, Rocq, or other proof-
assistant endpoint. Under them and the exact physical premises above,
this candidate halts on blank tape exactly when ZFC has a refutation.
Equivalently, its blank nonhalting expresses Con(ZFC) in the same
formalization and metatheoretic scope as the inherited calibration.
