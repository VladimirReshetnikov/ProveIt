# DR215: local sampler change, repaired compiler, and startup bridge

This note concerns the exact files `source/dr215.sites.json` and
`machine/dr215.native.tm`, reconstructed from the pinned ST215 inputs in this
packet. It uses the inherited ST215 command contracts and native-calculus
calibration as predecessor mathematical theorems. It is an ordinary proof
formalizable in ZFC, not a new Lean or Rocq kernel endpoint.

## 1. Exact changed semantics

Use Cantor pairing

    P(x,y) = (x+y)(x+y+1)/2 + y,
    I(x,y) = 4 P(x,y),       Q_i x = 4 P(i,x)+2,
    N(x) = I(x,1),          Ex_i x = N(Q_i(N(x))).

All arguments are arbitrary natural numbers. No well-formed-formula premise
is imposed, and the exact arithmetic equality I(0,0)=0 is retained.

The source register vector is (N,T,W,A,D,H,X,Y,L). These register names are
boundary roles. During the closed sixth AX-row constructor, register 4 holds
parameter A, register 5 holds parameter B, and register 3 holds parameter C.
The edited interval is zero-based [887,1170), with two 26-primitive C-load
macros at [939,965) and [1117,1143). Swapping register indices 3 and 5 in these
loads gives the existing B-load macros exactly. The four actual changed
primitive occurrences are 958, 963, 1136 and 1141. All four change 3 to 5.

The inherited postfix constructor word

    aacQFIQFIcI

therefore becomes

    aabQFIQFIbI.

Here a,b,c load the respective parameters; F loads numerical falsity 1;
Q and I are the total numerical constructors above. The resulting sixth row
changes from Ex_A(Q_A C) -> C to Ex_A(Q_A B) -> B.

For the all-natural load lemma, uniformly permute register indices in the
inherited closed macro proof. Increment and guarded decrement commute with
that permutation; break and continue depend only on program location. The
same decreasing loop measures prove termination. The resulting register
effect copies B instead of C, and restores the parameter and scratch registers
as in the inherited macro. The intervening constructors do not touch either
parameter register. Thus this is a change to the retained formula code, not a
claim that the entire resulting store is unchanged.

The two source CFG resolvers verify all guarded successors and locate every
changed data effect. The full symbolic runtime binds every guarded primitive
to the exact new binary table for arbitrary natural register values, gap and
spare blocks. Hence the source argument applies to the physical machine.

## 2. The native calculus is unchanged

The original sixth axiom family is

    { Ex_a(Q_a c) -> c : a,c in N }.

The new sixth axiom family is

    { Ex_a(Q_a b) -> b : a,b in N }.

These are equal sets of natural numbers. All other axiom families, the gated
theory bundle, truth 0, numerical modus ponens and theorem-only generalization
are unchanged. Replacing each sixth-row axiom leaf by parameters producing
the identical code preserves every finite derivation node. Thus the old and
new native calculi derive exactly the same numerical codes. In particular
they have the same consistency assertion, including junk codes and the zero
alias. This does not assert equality of all outputs from a fixed AX tuple.

## 3. Actual three-command contracts

Write a command boundary as (t,w,d,h), with stack push [x;w]=P(x,w).
The command tags are S=0, MP=1 and AX(c; x,y)=c+2. Their fields are
[0], [1,x], and [c+2,y,x], respectively.

The direct transfer S is the inherited 35-primitive single-guard operation:

    if h=1, halt;
    otherwise, writing (x,v)=unpair(w), return (h,v,d,x).

MP(x) sets y=d+x. If I(t,y)=h it returns (y,[0;w],y,0), and otherwise it
returns (0,w,y,0). AX(c;x,y) sets U=d, A=d+x, B=h+y, C=c and returns

    (g(A,B,C), [r1,r2,r3,r4,r5,r6(A,B),r7,L(A,B,C,U),Q_U h,t;w], 0,0).

The gate g is zero when C=A or C=B, and the inherited bundle otherwise.
The dominated row L satisfies U<=A because x>=0. Only slot six is changed.
The eight logical rows and the gate are implication codes, divisible by 4;
the quantifier slot is 2 modulo 4. Thus none of those generated entries is 1,
even for arbitrary natural inputs.

Soundness follows from these exact contracts. S tests an incoming theorem,
MP implements the numerical inference rule or returns truth, and AX pushes
ten theorem heads whenever incoming top/cache are theorems. Its changed slot
is an allowed sixth axiom by Section 2.

## 4. Repaired selected-row compiler

Retain the inherited direct-transfer compiler notation

    D = AX(0;0,0),
    H = D; S^11,
    PUSH = D; S^9; MP(0),
    DISCARD = MP(1); AX(1;0,0); S^10; MP(0).

The predecessor proof establishes, for arbitrary natural t,w,

    H(t,[x;w],d,h) = (t,w,0,x), unless it halts because t=1;
    PUSH(t,w,0,0) = (0,[t;w],0,0);
    DISCARD(t,w,0,0) = (0,w,0,0), without halting.

Those identities use only AX's stack shape, the nonfalsity tags of generated
entries, the gate, and its unchanged saved top/quantifier slots. Replacing
the sixth entry by another nonfalsity implication code leaves all identities
and their all-natural proofs valid.

A strong block for theorem X starts from every (t,w,0,0) and either halts or
returns (X,w,0,0). The generic row selector after DISCARD is

    AX(c;a,b); S^(j+1); H^(9-j),     1<=j<=7.

It selects row j and restores the exact original w with d=h=0. For a desired
sixth axiom Ex_a(Q_a v)->v, use the repaired block

    DISCARD; AX(a; a,v); S^7; H^3.

After DISCARD, its AX parameters are A=a, B=v, C=a and U=0. Its sixth entry
is exactly the desired natural code. Setting C=A disables the bundle gate,
but the sixth row is unconditional, so this imposes no restriction on a,v.
After seven S operations the selected row is top, r7 is cache, and the stack
is [L,Q,0;w]. Three H operations preserve the selected top and leave cache 0
and stackw. All intermediate guarded entries are different from1. This
establishes the strong block for every natural instance of row six.

For the other rows the inherited selection blocks are unchanged. The full
enabled gate, dominated L, truth, theorem-only generalization and numerical
modus-ponens compilers remain valid: their proofs use the unchanged stack
shape and safe auxiliary entries rather than the previous value of row six.
In particular the inherited generalization and MP blocks preserve their
literal numerical conclusions. The dominated-to-unrestricted propositional
recovery certificate in `inputs/` is unchanged and is rechecked by verify.py.

Consequently the inherited derivation induction again supplies a strong
block B_X for every theorem X, and B_1;H halts from every (t,w,0,0).

## 5. Cofinal enumeration and the exact blank seed

The scheduler and command tags are unchanged. It parses nested Cantor fields,
decrements a positive residual before each later command, and enumerates
successive candidate numbers when a proof pointer is exhausted. Each
nonhalting candidate drains because every later positive residual strictly
decreases. The inherited padding AX(0;1,Y) resets d=h=0 from every incoming
boundary and is followed by the strong refutation block when a refutation
exists. The successful candidates are cofinal in N. Thus any finite initial
candidate cutoff still reaches a refutation when one exists.

The exact fresh startup certificate for DR215 is:

    blank transitions: 70506
    native state: 84; dense state: 81; head: -2
    source ordinal: 58; source address: 00110010010110010
    complete logical vector: [1,0,0,0,0,0,0,18,0]
    gap: 0; header: 62; 63 zero spare blocks; 100 one-cells in total.

The entire binary prefix, including the zero exterior, is replayed in native
and dense labels. An independent source execution takes exactly 177 primitives
from AX entry 25 and seed [1,0,2,0,0,0,0,0,0] to the same ordinal and register
vector. This is the partial execution of AX(0;0,0), whose complete output has
top/cache 0 and ten explicit theorem heads above arbitrary tail 2, with next
candidate N=1 and proof pointer0.

Sections 1–5 of `references/st215_protected_credit.md` prove an all-natural
protected-tail theorem for this exact S=0, MP=1, AX>=2 scheduler. Assigning
balances S=-1, MP=0 and AX=+10 gives exact conservative credit d(1)=2 for the
infinite future schedule. Its proof covers every complete Cantor diagonal,
all within-candidate prefixes and the zero alias. The actual ten theorem
heads therefore leave a margin of eight; tail 2 is never exposed or tested.
Since DR215 emits the same number of theorem heads and uses the same tags,
that theorem applies without change. The predecessor file's historical
tail 4/ordinal 55 example is not the actual DR215 bootstrap; the explicit data
in this section and the new complete certificate supply the current bridge.

Hence halt implies native theorem 1, and native theorem 1 implies eventual
halt. The inherited native-calculus calibration then gives, for this exact
machine M, an ordinary proof formalizable in ZFC of

    Halt(M,blank) <-> not Con(ZFC),
    not Halt(M,blank) <-> Con(ZFC).

This conclusion does not assert unconditional consistency or unconditional
nonhalting. The new work is the exact local composition with ST215, repaired
compiler, source/table binding, fresh runtime and startup verification.

## 6. Prior work and scope of novelty

Neither direct transfer nor the rho6 symmetry is claimed as newly invented.
Both are published predecessor ideas in the pinned repository. DR215 is their
new accepted combination: 201 distinct source subtrees, 4,732 primitive
occurrences, 215 working states, and changed numerical AX output. A frozen
comparison against 321 table occurrences representing 84 rooted graphs at the
pin finds no action-preserving rooted graph isomorphism, including global tape
reflection. This excludes a mere state renaming or reflection; it does not
prove behavioral inequivalence, and it does not constitute a 214-state result.
