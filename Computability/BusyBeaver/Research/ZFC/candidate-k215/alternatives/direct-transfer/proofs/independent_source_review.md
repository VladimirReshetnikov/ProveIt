# ST215: independent source, compiler, and protected-tail review

## Scope and exact candidate

This review concerns the new outer-reassociated **direct single-guard
transfer** source `theory_work/outer2_short.sites.json`, and the zero-refill
table `theory_work/st215.native.tm`. It does not concern the rejected
scratch-biased experiment. Exact hashes are:

```
source 212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9
table  d5237504325eee96b0040d4d9574731a1caf4bcda3d6a49e94827d9532a664e1
```

The table has 215 working states, 430 rows, start state0, and sole external
halting state254. In particular its refill row is `198 0 0 L 40`. The
initial scratch register is not deliberately biased, the candidate counter
advances by one, and the original S=0 / MP=1 / AX>=2 wire language applies.

The source analysis and finite exact blank replay below have been checked
independently. The all-natural physical primitive simulation is a separate
certificate; the final machine theorem uses that certificate and the
inherited numerical-calculus calibration as explicit premises. This note
does not claim a proof-assistant kernel artifact.

## 1. Exact control-flow preservation

In the archived short-transfer `context-root` source write

```
t = (A, ((B, C), D)),
A = (scheduler, read),
B = selector and AX/MP body,
C = clear-top loop,
D = (copy-cache-to-top, NIP).
```

The new source is exactly `(((A,B),C),D)`. No literal opcode or operand
changes relative to that source. All4,732 source addresses change.
Independent arithmetic successor/cut and subtree-interval resolvers agree
on all6,151 guarded primitive cases, and the complete ordinal CFG equals
both archived `simple` and `context-root` CFGs. Relative to `simple`, only
the return control instruction's operand/opcode differs; its graph edge
is identical. The tree is closed, with boundary demand `(0,0,true)`.

The resulting source has201 DAG nodes,4,732 leaf occurrences, maximum
depth44, and maximum zero run6. The decisive contexts are:

|Purpose|Ordinal|New address|Instruction|Actual successor|
|---|---:|---|---|---|
|AX/MP return|4696|00111|CC3|scheduler0|
|Clear incoming top|4697|010|CD1|4699 if zero,4698 if positive|
|S halt|4717|11101|CH|halt|

Thus the physical return entry receives its required suffix111, while
clear-top receives the preceding bit required by its register-selection
entry. This is a change to the contextual implementation, with complete
source control flow preserved. A decoder-prefix test alone would not prove
these physical contracts; the universal primitive certificate must still
check the entire tape and every represented register value.

The self-contained source receipt is `st215_source_audit.json`; its
producer `outer2_source_audit.py` additionally corroborates the direct-S
contract on14,400 finite stores. Those finite cases are not used as a
substitute for the all-natural argument next.

## 2. The exact single-guard S contract

Use logical registers `(N,T,W,A,D,H,X,Y,L)`. At a command boundary,
parser/scratch registers A,X,Y are zero. Write the work tuple as
`(t,w,d,h)=(T,W,D,H)`, and let `unpair(w)=(x,v)` for Cantor pairing

`P(a,b)=(a+b)(a+b+1)/2+b`.

The direct command begins at ordinal4697 and has35 leaves:

1. Ordinals4697--4698 clear T.
2. Ordinals4699--4702 decrement H, incrementing both T and X once per
   iteration. They finish with T=h, H=0, X=h.
3. Ordinals4703--4705 move X back into H. They finish with T=H=h, X=0.
4. The inherited NIP at4706--4731 tests whether H=1, clears H otherwise,
   unpairs W, leaves the tail in W, and moves its first projection to H.

All three preliminary loops terminate by a decreasing natural register.
In NIP, the one-unit X flag distinguishes H=1 from H=0 and H>=2: H=1
reaches CH4717, while the other cases clear the remaining H and X before
the inherited all-natural Cantor-unpair loop. T is not tested. Therefore

```
S(t,w,d,h) = HALT                         iff h=1;
S(t,w,d,h) = (h,v,d,x)                   if h!=1.
```

Every nonhalting execution leaves A=X=Y=0 and preserves N,L,D. The guard
is strictly the original single-guard transfer contract. In particular an
incoming top1 with cache0 does not itself halt. The previous composite
`DROP;NIP;NIP` had the extra incoming-top guard, which is absent here.

This change does not require weakening the compiler theorem: the strong
compiler was originally proved for this exact single-guard S. Its
subsequent extension to the composite command was an additional result.

## 3. Why the inherited strong compiler applies unchanged

The applicable primary proof is the incoming packet's
`reference/transfer-parent/proofs/transfer_compiler.md`, independently
reviewed in `proofs/independent_compiler_review.md`. It uses precisely the
single-guard S contract above, the inherited MP and three-parameter AX
contracts, and fields

```
S       [0]
MP(x)   [1,x]
AX(c;x,y) [c+2,y,x].
```

The numerical calculus is defined on all natural formula codes, including
nondecodable junk codes. Let D denote that native calculus, with truth0
and falsity1. The required inherited calibration is the proof, formalizable
in ZFC, that native refutability of1 is equivalent to inconsistency of
ZFC. No claim that all numerical theorem codes decode as ordinary formulas
is used here.

The strong compiler supplies, for every D-derivation of X, a command block
`B_X` such that from **every** top/stack pair `(t,w)` and counter/cache0 it
either halts or returns `(X,w,0,0)`. The arbitrary-store quantifiers matter:
the enumerator keeps old theorems and arbitrary protected tails between
candidates rather than resetting its entire stack.

Some essential macros, with `E=AX(0;0,0)`, are:

```
H       = E;S^11
PUSH    = E;S^9;MP(0)
DISCARD = MP(1);AX(1;0,0);S^10;MP(0).
```

`H` tests an incoming top for1 and, if it is not1, pops one stack head into
cache while preserving that top and clearing the counter. `PUSH` preserves
the incoming top as a new stack head and clears top/counter/cache.
`DISCARD` clears top/counter/cache while preserving the entire stack. These
are universal contracts; their literal S calls are single-guard calls.
The major-premise-first MP construction preserves the old stack and uses
an explicit final H-equivalent guard, so removal of the composite command's
extra guard does not lose completeness.

If D derives1, then `B_1;H` halts from every top/stack pair with
counter/cache0. An initial AX clears those two registers from any incoming
store. Let R be the encoded residual for that compiled refutation. The
fresh candidate family

`N_Y=P(2,P(Y,P(1,R)))`

begins with `AX(0;1,Y)` and then executes the same refutation suffix.
Since `N_Y>=Y`, these successful candidate codes are unbounded. The ordinary
scheduler exhausts every natural candidate above its initial cutoff, and
each positive residual strictly decreases after the scheduling decrement.
Consequently existence of a native refutation forces a finite halt,
regardless of the protected-tail contents.

## 4. Exact conservative protected credit: two heads

The applicable all-natural proof is the incoming packet's
`reference/transfer-parent/proofs/protected_credit.md`. Its statement
explicitly covers either the single-guard S or the composite extension;
the source CFG audit establishes that this machine has its ordinary
S=0, MP=1 scheduler.

Here is the proof's relevant argument, so the application does not depend
on a finite schedule experiment. Let f be the right Cantor projection,
`R(0)=[]`, and `R(r)=W(r-1)` for positive r. If `unpair(n)=(a,y)`, the
fresh-candidate words are exactly

```
W(n)=S;R(y)             if a=0,
W(n)=MP;R(f(y))         if a=1,
W(n)=AX;R(f(f(y)))      if a>=2.
```

Assign conservative weights S=-1, MP=0, AX=10. Successful MP's extra
truth-head push is ignored. Let b(n) be total weight and
`B(k)=sum_{n<k} b(n)`. Put `g(0)=0`, `g(r)=b(r-1)` for r>0. The right
projection sequence is the concatenation `[0];[0,1];[0,1,2];...`.
Consequently nonnegative prefix sums of a sequence are preserved by
pullback along f, once or twice.

Induct jointly on Cantor diagonals to prove `B(k)+k>=0`, starting with

```
W(0)=S, W(1)=MP, W(2)=S;S,
B(0),B(1),B(2),B(3)=0,-1,-1,-3.
```

Apply the pullback fact to `q(r)=g(r)+1`; its prefix sum through k is
`k+B(k-1)>=0`. On diagonal s>=2, the first s-1 candidates begin with AX,
then one begins with MP, and the last begins with S. The first k AX
candidates have total conservative balance at least9k. Before AX at
position y the balance is at least9y; after its initial +10, its suffix
can lose at most `f(f(y))<=y` because R(r) has at most r commands. Thus
every prefix through that AX is nonnegative. After all AX candidates the
balance is at least `9(s-1)`. The MP suffix can lose at most s-1, and the
last S and its suffix at most1+s. Their combined lower bound is

`9(s-1)-(s-1)-1-s=7s-9>0`.

Every complete diagonal s>=2 is therefore prefix-safe. The argument uses
only earlier diagonal bounds in the pullbacks, so it is not circular.
Starting at candidate1, the exceptional initial word is just
`W(1);W(2)=MP;S;S`, with minimum balance-2. Therefore the **exact
conservative initial debt is d(1)=2**, and no later prefix is worse.

Maintain an explicit finite list of theorem heads over a fixed opaque
numerical tail J. AX prepends ten theorem heads, MP pushes a theorem zero
on success and none on failure, and S removes one explicit head. With
two initial heads, an S always has one available, because the conservative
post-S count never drops below zero. Its sole guard tests theorem-valued
cache, so a halt implies D derives1. The list invariant is explicit;
`P(0,0)=0` does not invalidate it, since
`unpair(P(x,v))=(x,v)` holds even at zero. No uniqueness of encoded list
length is assumed.

## 5. Independent exact blank startup and its ten-head bridge

`st215_bootstrap_audit.py` parses only the literal native table as data,
simulates from state0 on an entirely zero tape, and constructs the whole
expected tape frame independently of the inherited frame decoder. It
checks that at exactly70,506 transitions the machine has:

```
dispatcher84, head -2, header62, extra gap0,
source address00110010010110010, ordinal58,
(N,T,W,A,D,H,X,Y,L)=(1,0,0,0,0,0,0,18,0),
63 spare blocks, all value0,
exactly100 one-cells, all listed in st215_bootstrap_audit.json.
```

The same script uses the independently resolved source CFG to execute
exactly177 source primitives from AX entry25 and seed

`(N,T,W,A,D,H,X,Y,L)=(1,0,2,0,0,0,0,0,0)`.

It reaches ordinal58 with exactly the same complete logical store. This
is an exact partial execution of `AX(0;0,0)` with incoming work tuple
`(0,2,0,0)`, not an inferred eventual frame or a partial register match.

The all-natural AX contract now supplies termination of the remaining AX
and its result: top/counter/cache0, N=1, empty residual L, all parser
scratch zero, and ten explicit native theorem heads above opaque tail2.
These are seven retained axiom rows, one dominated/generalized row, a
generalization of incoming truth0, and saved truth0. The enabled-bundle
gate is0 because its parameters coincide. Section4 requires only two
heads, leaving a permanent conservative margin of eight above tail2.

The opacity is substantive: `2=P(0,1)` and `1=P(1,0)`, so its ordinary
unpairing eventually exposes falsity1. The protected-credit theorem is
what prevents the enumerator from exposing that arbitrary tail. No
theoremhood assumption is made about its buried elements.

## 6. Resulting machine theorem and remaining certificate boundary

Assume the exact-table all-natural primitive simulation certificate and
the inherited source arithmetic/AX/MP and native-calculus calibration
proofs. Then all components above are finite combinatorial arguments or
induction over natural numbers, formalizable in ZFC. They establish:

```
ZFC proves: ST215 halts on the blank tape iff ZFC is inconsistent;
equivalently, ST215 never halts iff Con(ZFC).
```

For the forward implication, the exact bootstrap supplies ten safe heads;
the credit invariant maintains theorem-valued top/cache; and the only
halt guard certifies native theorem1. Native calibration supplies a ZFC
refutation. For the reverse implication, native calibration supplies a
native refutation; the universal strong compiler and cofinal candidate
family force its eventual execution and a halt. The exact physical
simulation transfers both source conclusions to the literal table.

The independent checks in this note establish source control, the finite
blank frame and AX-prefix match, and applicability of the inherited
compiler/credit proofs. They should be packaged alongside the universal
runtime certificate, not advertised as replacing it. The new construction
is a repaired215-state implementation of the direct35-leaf, single-guard
transfer command. It is not a214-state result.
