# Stride-two theorem transfer: an equiconsistent three-command language

## Status and contribution

This note gives a new ordinary, all-natural command compiler and an infinite
stack-credit theorem for a command that removes **two** old stack heads at
once. It supplies five exact register-source variants of 202 distinct
subtrees and 4,801 primitive occurrences. A direct variant proved in Section
10 supplies five further sources with the same 202-node count and 4,758
primitive occurrences. It does not itself assert a
215-state allocation, an exact binary runtime proof, or a new
proof-assistant endpoint. Those are separate obligations.

The numerical calculus, axiom emitter, Cantor code conventions, and
dominated-rho8/ZFC calibration are inherited from ProveIt's accepted K215
and the incoming MP0-transfer215 packet. The new contribution here is the
stride-two compiler: parity is controlled by deliberate successful MP(0)
instructions. The old one-head transfer compiler does not apply unchanged.

## 1. Exact interpreter and theoremhood invariant

Let

    P(a,b) = (a+b)(a+b+1)/2 + b,
    I(a,b) = 4 P(a,b),             Q_i(a) = 4 P(i,a)+2,
    [x;S] = P(x,S),               truth = 0, falsity = 1.

All arguments are natural numbers; no well-formedness premise is imposed.
In particular I(0,0)=0 and [0;0]=0 are genuine aliases.

The work state is (t,S,d,h): current formula, encoded stack, additive
parameter, and cached formula. Retain the accepted MP and AX operations:

    MP(x): set y=d+x.
      If I(t,y)=h, return (y,[0;S],y,0).
      Otherwise return (0,S,y,0).

    AX(c;x,y): set U=d, A=d+x, B=h+y, C=c.
      Return (G(A,B,C),
              [r1,...,r7,L(A,B,C,U),Q_U(h),t;S], 0,0).

Here r1,...,r7 are the exact retained native logical rows, L is dominated
rho8, and G is the literal native theory bundle, set to zero when C=A or
C=B. Every generated r_j, L, Q and G differs from 1, independently of
whether the incoming t,h are theorems. Every emitted row is a theorem;
Q_U(h) is a theorem when h is; the gate produces either truth or an allowed
bundle. The domination U<=A holds because x>=0.

Replace DROP and NIP by the single command

    S2 = oldDROP ; oldNIP ; oldNIP ; oldNIP.

Its exact equation, writing S=[x,y;V], is

    S2(t,[x,y;V],d,h) = (h,V,d,y),

unless h=1, t=1, or x=1, in which case it halts. The second popped head y
is not tested until a later command. The tests are precisely the three
oldNIP tests: they see h, then the pushed t, then x. This is a two-head
shift of the current/cache window, not the previously investigated
rotating-pop NIP;DROP;NIP.

For soundness, assume t and h and every exposed stack head are native
theorems. Every command preserves theoremhood on a nonhalting return.
Every S2 halt explicitly identifies theorem 1. Successful MP is exact
native detachment; failure yields truth. This is a direct invariant and
does not require decoding junk codes into an object-language syntax.

## 2. A non-detachment lemma used by PUSH

The sixth retained row is

    r6(A,B) = I(I(Q_A(I(Q_A(B),1)),1), B).

It is positive: its antecedent is positive, because its outer consequent
is 1. The dominated row is

    L(A,B,C,U)
      = I(I(I(C,U),A), I(I(A,C),I(B,C))),   U<=A.

For every natural A,B,C,U with U<=A,

    I(r6(A,B),0) != L(A,B,C,U).                     (ND)

Proof. The left side is positive. If the right side is zero, they differ.
Otherwise Cantor injectivity applied to the outer implication would force

    I(I(A,C),I(B,C))=0.

The native zero law I(v,w)=0 iff v=w=0 then gives A=B=C=0.
Domination forces U=0, whence L=0, contradicting the positive left side.
The argument covers the collapsed zero implication; it does not silently
treat zero as a distinct truth constructor.

## 3. The two-head cleanup and stack-push macros

Write D0=AX(0;0,0). Define

    H2   = D0 ; S2^6,
    PUSH = D0 ; S2^4 ; MP(0) ; MP(0) ; S2 ; MP(0).

**Two-head cleanup.** On arbitrary (t,[x,y;V],d,h), H2 either halts or
returns (t,V,0,y). Its only possible halts are t=1 or x=1.

After D0 the packet is [r1,...,r8,Q_d(h),t,x,y;V]. Five S2 operations
remove its first ten entries and leave (r8,[x,y;V],0,t). The sixth tests
t and x and returns the stated result. All other tested new values are
constructor-safe. Thus H2 preserves the current theorem while removing two
old heads; it resets the numeric parameter but leaves the second removed
head cached. A subsequent application may halt if that head is 1, which
is permitted in the completeness contracts below.

**Push.** PUSH is total on every numerical (t,S,d,h), even if t or h is
1, and returns exactly (0,[t;S],0,0).

After D0 and four S2 commands, the state is

    (r6, [Q_d(h),t;S], 0, r8).

The first MP(0) fails by (ND), clearing top and cache. The second MP(0)
succeeds by I(0,0)=0 and pushes one zero. S2 removes that zero and the
quantified value, returning (0,[t;S],0,Q_d(h)). The final MP(0) fails
because a Q code has residue 2, whereas every implication code has
residue 0. It clears the cache. None of these steps examines t as a halt
test or reads S, so PUSH does not need a theorem or safety premise.

## 4. Reset and compiler interface

Use the following strong compiler contract for a theorem code X:

    B_X: (t,S,0,0) -> halt or (X,S,0,0),

for every raw t and S. The stack must be preserved as an encoded natural;
early halting is an allowed successful compilation outcome. Safety is
needed only when proving that actual executions cannot halt spuriously.

Define

    DISCARD = MP(1) ; AX(1;0,0) ; H2^5.

From cache zero, MP(1) necessarily fails because I(t,1)>0, giving
(0,S,1,0). The AX instance has U=A=C=1 and gate zero. It places ten safe
heads above S, the final one being old top zero. Five H2 applications
remove those ten heads while preserving current zero. The last removed
head is zero, so the result is exactly (0,S,0,0). No protected part of S
is read. This supplies the truth compiler.

Let J(0) be the empty word and J(u)=MP(u) for u>0, used after DISCARD.
Then J(u) sets d=u without changing the stack and leaves t=h=0.
Omitting J(0) is necessary: MP(0) at (0,S,0,0) deliberately pushes a
zero, and is used below precisely for that purpose.

## 5. Selecting every AX row by parity padding

Fix a desired dominated instance with parameters (A,B,C,U), U<=A.
Rows 1 through 7 ignore U and may use U=0. The ninth row is Q_U(h).
In this section incoming cache to AX is zero, so its ninth row is Q_U(0).

### Even positions j=2,4,6,8

The strong block is

    DISCARD ; J(U) ; AX(C;A-U,B)
      ; S2^(j/2+1) ; H2^((8-j)/2).

The initial AX saves old top zero. After j/2+1 shifts, top is r_j and
exactly 8-j generated entries remain over S. Their count is even.
The H2 suffix removes them in pairs, preserving r_j. If the suffix is
empty (j=8), the cache already holds old top zero; otherwise its final
second removed head is that zero. Hence the result is (r_j,S,0,0).

### Odd positions j=1,3,5,7,9

Insert a zero below the packet using MP(0) immediately after DISCARD.
After AX, insert exactly one further zero above its packet. Define

    PAD_G = MP(0)          if C=A or C=B,
            MP(0);MP(0)   otherwise.

The gate is zero exactly in the first case: when enabled, it is a positive
negation code. Therefore PAD_G always clears the current/cache and pushes
exactly one zero. In the second case the first MP fails, and the second
succeeds. This is a metalevel choice based on the literal known numeric
parameters, not an additional machine instruction.

The strong block is

    DISCARD ; MP(0) ; J(U) ; AX(C;A-U,B) ; PAD_G
      ; S2^((j+3)/2) ; H2^((9-j)/2).

Immediately after PAD_G the explicit prefix over S is

    [0,r1,...,r9,0,0;S].

It has length 12. The first zero shifts the parity so the odd r_j becomes
top. After (j+3)/2 shifts, 9-j heads remain, an even number. Pair cleanup
removes them, with final cache zero; for j=9 no cleanup remains and the
last directly popped head is the lower padding zero. Thus every native
row is selectable with the exact strong contract.

There is no assumption that an explicit [0;0] is distinguishable from
zero as an integer. The proof uses the exact two-sided pairing identity
unpair(P(a,b))=(a,b) at each step, including a=b=0.

### Theory bundle

A permitted bundle at (A,B,C) has the strong compiler

    DISCARD ; AX(C;A,B) ; H2^5.

The AX uses U=0 and saves old top zero. The cleanup removes its ten
generated heads and leaves the gate on top, with original S and zero
counter/cache. The raw-zero and failed-gate cases are also exact.

## 6. Generalization and modus ponens

The induction hypotheses below are inserted as complete command words.
They preserve whichever encoded stack is supplied to them; that stack
can include the temporary padding and stored premises.

### Generalization

Given B_X, a strong block for Q_i(X) is

    DISCARD ; MP(0) ; B_X ; PUSH ; MP(0) ; J(i) ; S2
      ; AX(i;0,0) ; MP(0) ; S2^6.

After DISCARD and MP(0), the protected stack is [0;S]. B_X produces X
over that stack unless it already halts. PUSH and MP(0) then give

    (0,[0,X,0;S],0,0).

J(i) sets the counter. S2 returns (0,[0;S],i,X): X is the second
popped head and is not tested at this step, even when X=1. The next AX has
U=A=C=i, so its gate is zero and its
ninth row is exactly Q_i(X). Its old current is zero. MP(0) inserts the
upper parity zero. The twelve-head packet is now the odd-selection
packet of Section 5 at j=9. Six shifts return
(Q_i(X),S,0,0). No unrestricted formula-substitution or quantifier
elimination rule is used.

### Modus ponens

Suppose B_M compiles M=I(A,B) and B_A compiles A. A strong block for B is

    DISCARD ; MP(0) ; B_M ; PUSH ; MP(0)
      ; B_A ; PUSH ; MP(0) ; S2 ; S2 ; MP(B) ; H2.

The first zero is reserved to cancel MP's eventual success push. Just
before the two S2 operations, the exact state is

    (0,[0,A,0,I(A,B),0;S],0,0).

The shifts leave (A,[0;S],0,I(A,B)), unless they halt earlier at A=1.
MP(B) succeeds, yielding (B,[0,0;S],B,0). H2 removes the two zeros and
resets the counter/cache while retaining B, or halts if B=1. Thus the
strong interface holds, including the raw case A=B=0 and I(0,0)=0.

By induction on finite dominated-calculus derivations, all native theorem
codes have strong compilers. The inherited 3,728-node dominated-rho8
calibration translates unrestricted native proofs into these derivations;
the native calculus is equiconsistent with ZFC by the stated inherited
comparison theorem. No new assumption about those calibrations is hidden
in the stack construction.

For a derivation of 1, append H2 to B_1. If B_1 has not already halted,
H2 tests the saved current 1 before inspecting any old stack head. The
word therefore halts from every (t,S,0,0). Prefixing AX(0;0,0) extends
this to every numerical work tuple, because AX resets d and h before the
strong word starts. This universal completeness assertion does not imply
soundness from arbitrary initial theorem data.

## 7. Wire format, termination and cofinality

The supplied source retains the MP-first ordering:

    MP(x): [0,x];   S2: [1];   AX(c;x,y): [c+2,y,x].

For a field list f and continuation r, let E(f,r) be right-folded P.
Encode continuation words by

    tail([])=0,
    tail(k::L)=1+E(fields(k),tail(L)).

A freshly enumerated candidate omits the outer successor on its first
command. Positive continuation pointers are decremented first, and each
subsequent field projection is at most its input. Thus every nonhalting
candidate drains finitely; arithmetic primitives terminate by the inherited
macro contracts. Inserting an additional closed NIP changes neither
scheduler nor field reads.

Let r be the continuation encoding of B_1;H2. The first command
AX(0;1,Y) resets d and h from every incoming work tuple. Its complete
fresh candidate has code

    n_Y = P(2,P(Y,P(1,r))) >= Y.

It therefore forms a cofinal family of successful candidates whenever a
native refutation exists. This is the ordinary unmodified increasing
enumerator; no skipped-candidate or scratch-biased scheduler premise is
introduced.

## 8. Two-head protected credit above arbitrary raw tails

Changing S to S2 doubles its net stack consumption, so the previous
one-head bound must be reproved. Assign conservative balances

    MP=0, S2=-2, AX=10.

Actual successful MP pushes a theorem zero and can only improve this
balance. Write f(n) for the right Cantor projection. The literal syntactic
candidate words satisfy, with R(0)=[] and R(r)=W(r-1) for r>0,

    W(P(a,y)) = MP ; R(f(y))       if a=0,
                S2 ; R(y)         if a=1,
                AX ; R(f(f(y)))   if a>=2.

The command count of W(n) is at most n+1; therefore every prefix of R(r)
has balance at least -2r. Let b(n) be total word balance and
B(k)=sum_{n<k}b(n), and put g(0)=0, g(r)=b(r-1) for r>0.

Use the Cantor prefix-pullback lemma: if q has nonnegative initial partial
sums, then q(f(n)) and q(f(f(n))) do also. It follows because f(n), in
increasing n, concatenates the lists [0], [0,1], [0,1,2], and so on.
Apply it to q(r)=g(r)+2. Its first k terms sum to

    2+B(k-1)+2(k-1),

nonnegative under the inductive bound B(j)+2j>=0.

Let T_s=s(s+1)/2. At diagonal s>=2 the candidates, ordered by their
right coordinate y=0,...,s, consist of s-1 AX-first words, then one
S2-first word, then one MP-first word. Joint induction on diagonals proves
B(k)+2k>=0, B(T_s)>=-2, and that every diagonal s>=2 is nonnegative at
every command prefix relative to its start:

* The first k AX words have total balance at least (10-2)k=8k by the
  double prefix pullback.
* Inside AX word y, relative balance is at least
  8y+10-2f(f(y)) >= 6y+10 > 0.
* Through the penultimate S2 word, it is at least
  8(s-1)-2-2(s-1) = 6(s-1)-2.
* Through the final MP word, it is at least
  6(s-1)-2-2f(s) >= 4s-8 >= 0.

All pullback indices are smaller than the current diagonal start, so the
induction is well founded. The base words are W(0)=MP, W(1)=S2,
W(2)=MP, with cumulative balances 0,0,-2,-2. Consequently the complete
infinite conservative schedule has minimum prefix balance exactly -2.
Starting at cutoff N=1 likewise requires exactly two conservative heads.

For clarity, the joint induction closes as follows. Assuming the claims
before diagonal s, the displayed prefix bounds give B(k)>=B(T_s)>=-2
at every candidate boundary in that diagonal. Thus B(k)+2k>=0 there,
and the diagonal-end bound supplies B(T_(s+1))>=-2 for the next step.
The pullback sums only use already established earlier B-values. The same
within-word bounds cover every command prefix, not only candidate ends.
The formula for the first k terms of g+2 is used for k>=1; its empty
partial sum is separately zero.

Therefore a matched startup with N=1, empty continuation, theorem current
and cache, and ten explicit theorem heads above an arbitrary numerical
tail has permanent conservative margin eight. Every S2 has both consumed
heads available above that tail. Its three guards test theorem values.
The exact encoded tail, even one beginning with 1, is never read. This
supplies soundness for the same kind of partial-AX startup as the parent
MP0 table, conditional on the exact new machine actually reaching it.

## 9. Literal source artifacts and checks

The source parent is the incoming MP0-transfer201 source

    SHA256 8ddb942f0f1d8e2e3b12ab7217c7232eb553cd288fca38dbf9b0eded73893dd5.

Its subtree at address 110101 is ((D,N),N), where D and N are the exact
closed 26-primitive oldDROP and oldNIP bodies. Replace it by any of the
five binary associations of D,N,N,N. The saved variants all have:

    202 distinct subtrees; 4,801 leaves; 6,245 guarded cases;
    maximum depth 44; maximum zero run 6.

Each block has zero escaping break and continue demand. N contains a
halt, which is deliberately retained. Closed sequential reassociation
preserves halting and normal return; it is not being licensed by a
halt-free-only optimizer. Both complete CFG resolvers agree for each
new source. The modified S2 loop body has the exact stated DNNN semantics;
all exterior source structure remains literal.

`check_stride2.py` supplies 79 symbolic interface checks, including all
row positions, gate-zero and positive-gate padding, zero-implication
alias cases, generalization, MP, arbitrary protected suffixes, and the
allowed early halts. It independently evaluates 11,232 exact numerical
instances of (ND), and corroborates credit through 100,000 candidates
and 444 full diagonals. These finite checks are not substitutes for the
ordinary all-natural arguments above. The script's HOLE substitutions
are exactly the induction hypotheses B_X, not asserted machine steps.

An eventual binary claim additionally needs a literal complete transition
table, a state count including initialization, every arbitrary-natural
primitive-runtime case for this exact source, and a complete blank trace
to a calibrated frame. This note by itself completes the logical compiler
and scheduler side only.

## 10. A shorter direct source command, with the same complete compiler

The 104-leaf DNNN body can be replaced by the following 61-leaf body:

    CLEAR_T ; COPY_H_TO_T_PRESERVING_H ; oldNIP ; oldNIP.

This adapts the incoming packet's direct one-head transfer prefix; the
new contribution here is its two-head use with the stride-two compiler.
The literal source expressions for the prefix are

    CLEAR_T = (CD1, CC1),
    COPY_H  = ((CD5,(CI1,(CI6,CC3))), (CD6,(CI5,CC2))).

Registers 1, 5, and 6 are current T, cache H, and scratch X. Under the
inherited command-boundary invariant X=0, CLEAR_T runs t positive
decrement/continue iterations and one zero test, leaving T=0. It takes
2t+1 source steps. The first COPY_H loop decrements H and increments
both T and X; after h iterations, T=h,H=0,X=h. The second loop restores
H by transferring X back, ending with T=H=h,X=0. Their respective step
counts are 4h+1 and 3h+1. Consequently the prefix terminates on all
natural t,h in 2t+7h+3 source steps, with exact effect

    (t,S,d,h; X=0) -> (h,S,d,h; X=0),

preserving every other register. This is an ordinary induction on unary
loop counters, including their zero cases.

OldNIP tests its incoming cache for equality to 1. If the test fails,
it unpairs the stack into its new cache and stack, leaves T and d
unchanged, and restores its scratches. Two such calls therefore give
the direct command's exact contract

    S2_direct(t,[x,y;V],d,h) = halt       if h=1 or x=1,
                             (h,V,d,y)  otherwise.

The old-current test t=1 is absent. This is not claimed to be two-way
behavioral equivalence with DNNN. The return equation and two consumed
heads are identical, so each compiler proof above applies directly:
PUSH and DISCARD still terminate; all displayed nonhalting equations
remain exact; any omitted early halt continues along those equations.
The critical terminal test is retained: after D0 and five direct shifts,
the state is (r8,[x,y;V],0,t), so H2's sixth shift tests incoming cache
t. Thus H2 still halts exactly when the saved top t=1 or first old head
x=1. In particular B_1;H2 detects falsity even though a single direct
shift does not inspect its old current. The two shifts in the MP compiler
still test A through cache, and the final H2 still detects B=1.

The two-head credit argument is identical, because command tags, field
readers, and stack balances have not changed. Its direct guards test
theorems by the same invariant. Removing the old-current test introduces
neither a new formula code nor a new way to reach the arbitrary buried
tail.

The five direct binary associations have 202 distinct subtrees, 4,758
primitive leaves, 6,187 guarded cases, maximum depth 44, and maximum zero
run six. The edited body has 2+7+26+26=61 leaves instead of 104, reducing
the full source by 43 primitive occurrences. This leaf reduction does not
establish any reduction in physical TM states. The builder checks both
complete CFGs and the same exterior transport for these exact sources.
The direct checker passes the same 79 interface cases and constructor and
credit checks. Literal execution of 81 direct command cases confirms 45
guarded halts and the stated return equation. These finite results
corroborate, but do not replace, the all-natural loop argument.
