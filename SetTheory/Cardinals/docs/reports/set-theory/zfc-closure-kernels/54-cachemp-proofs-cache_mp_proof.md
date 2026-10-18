# A different successful-MP interface for the complete C254 search

Research contribution, 17 October 2026. Source pin:
`43026ff42f0939f09b9e95495248cfadcad38e38` in VladimirReshetnikov/ProveIt.

## Result and its scope

There is a one-edge edit of the complete 219-node structured register program
that changes successful modus ponens into a destructive transfer of its result
to the cache. It retains all twelve numerical proof rules, all eight logical
rows, native equality, both freshness gates, the full CP/GIC bundle, and the
existing formula/proof/stack encodings. The altered proof enumerator has the
same refutation criterion as the original: it halts exactly when C254 derives
the fixed falsity code 1. This section supplies an ordinary mathematical proof,
including the persistent enumerator's completeness; it is not a new
kernel-checked Lean theorem.

The concrete edit is `Dag254.nodes[130].right := ENode 197`, replacing
`ENode 166`. No new source node is needed. The existing helper 197 transfers
the numeric parameter into the cache and clears the parameter. Its source is

```
197 = (EDecnz 4, ENode 191)
191 = (EInc 5, EContinue 2).
```

The complete one-edge binary counterpart found by the construction lane is
old-label row `204/read1: (1,R,113) -> (1,R,151)`. Its source-program image is
the complete successful-MP subtree at prefix `111111`, replaced by the
already existing destructive-transfer subtree. The generated table still has
252 states before any further minimization. Its 8,361 affine instruction
checks pass under the four preserved register-operation contracts. A separate
bootstrap audit has now found a register-selector permutation of this
252-state runtime with a complete Safe root from blank. The literal table is
`agents/proof_audit/mp-cache252-census-next12288/hit-2799.tm`, with SHA-256
`9ba862d15e0f689525281e1c96083acf7f389157bd56d6a2676f223106dc07a9`;
the adjacent JSON file contains its finite certificate. After 707,393 moves
from old state 0 on a blank tape, the machine reaches old root state 96 with
head -13, marker -14, header 27, gap 40, logical registers
`[N,T,W,A,D,H,X,Y,L] = [6,0,0,0,2,0,0,0,0]`, and 295 zero spare
registers. The physical register map is `[4,5,0,8,6,2,1,7,3]`.
This is the successful permuted table, not the earlier old-label
`mp-cache252.tm`, whose shorter bootstrap census had no hit.
A separate exact source-binding audit has also completed the changed
structured-program to literal-decoder correspondence. Its checker is
`agents/proof_audit/source-binding/verify_source_binding.py` and its
certificate is `source_binding_certificate.json` in the same directory
(SHA-256
`e79c6efa1e697fadeb7b317ba129960eb4f47d99dcf17dc7b8bc0a454b5f73f9`).
It checks 2,998 related instruction sites and 5,995 branches, with at most
five increment/control steps per segment. The proof allows different
orders of independent register increments, comparing the exact nine
increment counts before the same test/halt event. The edited literal tree
is checked against the exact specified subtree replacement, and structured
well-formedness is checked separately. This supplies an ordinary finite
simulation argument; no new kernel-checked Lean endpoint or additional
state fold is claimed.

The idea differs materially from the repository's earlier successful-MP
dummy-push deletion. That change retained the additive parameter and copied
the conclusion back into the current-formula register. Here the success
continuation does not need either that copy or its restoration loop: the
conclusion lives in the cache, and the additive parameter is reset.

## 1. Exact numerical interface

Use the original Cantor pairing

\[
 P(a,b)=\frac{(a+b)(a+b+1)}2+b,
 \qquad I(a,b)=4P(a,b).
\]

The working registers are \((t,s,d,h)\): current formula, theorem stack,
additive parameter, and cached formula. The stack is an unshifted stream:
\(P(x,s)\) pushes \(x\), while zero denotes the infinite stream of zeroes.
The contradiction target is the actual code \(F=1\).

An MP command carries an additive operand \(x\) and sets \(b=d+x\). The
original success branch, when \(I(t,b)=h\), returns

\[
 (b,P(0,s),b,0).
\]

The proposed branch returns

\[
 \boxed{(0,s,0,b)}.
\]

Both versions have the same failure branch, \((0,s,b,0)\). DROP, NIP and AX
are unchanged, including the timing of NIP's halt test: it tests the incoming
cache before popping the stack. In particular,

\[
\begin{aligned}
 \operatorname{DROP}(x)(t,s,d,h)&=(h,P(t,s),d+x,h),\\
 \operatorname{NIP}(x)(t,s,d,h)&=
 \begin{cases}\text{halt},&h=1,\\
 (t,s',d+x,a),&\operatorname{unP}(s)=(a,s'),\ h\ne1.
 \end{cases}
\end{aligned}
\]

No prepared proof witness is supplied on the blank tape. The command words
are still enumerated by the original natural-number candidate counter.

## 2. Why the actual register program implements this change

The original MP routine is the composition

```
node150 = (node161, node151)
node161 = (node166, node119)   # copy parameter, then construct implication
node151 = (node216, node130)  # move implication into scratch1, then compare
node130 = (node123, node166)  # compare, then old success action
```

`L2Macros254.par1` and `cons` show that node161 preserves the underlying
theorem stack and replaces the top with \(I(t,d)\). The transfer theorem for
node216 moves that top into scratch1 and clears the top. Therefore the
destructive comparison enters with top zero, scratch1 \(I(t,d)\), cache
\(h\), unchanged stack and parameter, and scratch2 zero.

The existing `L2Control254.ifeq_eq` and `ifeq_ne` theorems have an exact
interface: both scratch1 and cache are zero after the comparison. On equality
the result is a normal exit; on inequality it breaks past the right child of
node130. Thus only the equality branch executes the replacement helper.

The existing theorem `L2Lib254.loop197` states, for **every** input record,

\[
 (d,h)\longmapsto(0,h+d),
\]

preserving all other fields. Its success input has \(h=0\), so it gives
exactly the displayed new MP contract. In particular it leaves both scratch
registers zero, the selector unchanged, and the remaining command pointer
and next-candidate register unchanged. The source proof is a composition of
already proved local contracts, with a fresh induction over the changed
node130 and its three callers. It is not justified merely by interpreting
the helper's informal name.

## 3. Soundness

Retain exactly the existing invariant

\[
 \operatorname{Safe}(t,s,d,h)
 := C254(t)\land\operatorname{Good}(s)\land C254(h),
\]

where `Good` means that every head in the unshifted stack stream is a C254
theorem. The parameter \(d\) is unrestricted.

If MP succeeds, the current formula and cache supply \(C254(t)\) and
\(C254(I(t,b))\); the actual numerical MP rule gives \(C254(b)\). The new
current formula is zero, which is the primitive truth theorem. The stack is
unchanged and the new cache is \(b\). Hence Safe is preserved. The failure
branch has two zero formula fields and the unchanged good stack. The old
DROP, NIP and AX invariant proofs apply without modification.

The only command that halts is still NIP with incoming cache 1. At a safe
boundary that cache is a theorem, so halting implies \(C254(1)\). Starting
from zero registers establishes Safe. This induction does not claim that
arbitrary initial formula values or an arbitrary stack are sound.

## 4. The exact successful-inference contract

For the new command interpreter, define the same strong contract as
`Enum254.Contract`:

\[
 \mathcal C(p,X):\quad
 \forall T,S\quad
 \operatorname{exec}(p,(T,S,0,0))=\text{halt}
 \ \text{or}\ (X,S,0,0).
\]

Neither \(T\) nor \(S\) is required to be a theorem. This strong interface is
what makes a single contradiction candidate work after arbitrary preceding
candidate executions.

Let \(p_A,p_{A\to B}\) satisfy the contracts for \(A\) and \(I(A,B)\).
Use the block

\[
\begin{split}
 p_A;\ &\operatorname{DROP}(0);p_{A\to B};\\
 &\operatorname{NIP}(0);\operatorname{DROP}(0);\operatorname{NIP}(0);\\
 &\operatorname{MP}(B);\operatorname{DROP}(0);\operatorname{NIP}(0).
\end{split}
\]

This is the original premise arrangement followed by a new three-command
tail. It replaces the original tail containing an additional AX and thirteen
cleanup commands. To verify it, assume neither premise block already halts.
The exact successive working states before MP are

\[
\begin{array}{c|c}
\text{point}&(t,s,d,h)\\\hline
\text{after }p_A &(A,S,0,0)\\
\text{after DROP}&(0,P(A,S),0,0)\\
\text{after }p_{A\to B}&(I(A,B),P(A,S),0,0)\\
\text{after NIP}&(I(A,B),S,0,A)\\
\text{after DROP}&(A,P(I(A,B),S),0,A)\\
\text{after NIP}&(A,S,0,I(A,B)).
\end{array}
\]

If \(A=1\), the last NIP shown halts already, which is permitted by the
contract. Otherwise the displayed last state follows from
\(\operatorname{unP}(P(u,v))=(u,v)\).

The final three commands have the exact effects

\[
\begin{aligned}
 (A,S,0,I(A,B))&\xrightarrow{\operatorname{MP}(B)}(0,S,0,B)\\
 &\xrightarrow{\operatorname{DROP}(0)}(B,P(0,S),0,B)\\
 &\xrightarrow{\operatorname{NIP}(0)}(B,S,0,0),\quad B\ne1.
\end{aligned}
\]

For \(B=1\), the final NIP halts instead. Thus the block satisfies
\(\mathcal C(p,B)\) in every case, including \(A=0\), \(B=0\), and the
zero-stream pairing alias. There is no hidden assumption that formula codes
are positive or that a finite stack has an injective list representation.

## 5. Every derivation still has a uniform command block

The remaining cases of the original derivation-to-block proof are unchanged:

* The truth block is `discard = MP(1); AX(1,0,0,0); NIP(0)^10`.
  It begins at parameter/cache zero, and \(I(T,1)>0\), so its MP is always a
  failure. The changed success branch is never used there.
* The eight logical rows and the gated bundle use discard followed by the
  original AX emitter and the original stack-selection sequence. They
  contain no further MP.
* The generalization block executes its inductively supplied premise block
  and then the original DROP/NIP/AX selection sequence. Its suffix has no MP.
* The MP case is the block proved above.

Induction on the full twelve-constructor C254 derivation therefore gives
\(C254(X)\Rightarrow\exists p\,\mathcal C(p,X)\). This retains both
freshness inequalities in the bundle constructor. It neither replaces the
logical calculus nor relies on the defeated equality-free frontend.

## 6. Persistent enumeration and cofinal completeness

A finite programmable trace alone is insufficient here: the enumerator does
not reset the four working registers between candidate words. The strong
contract supplies the missing uniformity.

Suppose \(C254(1)\), and choose a block \(p\) with \(\mathcal C(p,1)\).
For every natural padding value \(u\), the word

\[
 Q_u=\operatorname{AX}(0,1,1,u);p;
 \operatorname{DROP}(0);\operatorname{NIP}(0);\operatorname{NIP}(0)
\]

halts from **every** four-register working state. The initial AX resets the
parameter and cache to zero; its resulting top and stack are arbitrary
arguments allowed by \(\mathcal C\). If \(p\) returns, its current formula
is 1. The last three commands store 1, retrieve it into the cache, and test
it. The padding \(u\) affects only disposable axiom data before \(p\); the
uniform contract absorbs that change.

The actual command-word packing is unchanged:

\[
\begin{aligned}
\operatorname{pack}(\operatorname{MP}(x),r)&=P(0,P(x,r)),\\
\operatorname{pack}(\operatorname{AX}(c,x,y,u),r)&=
P(c+3,P(x,P(y,P(u,r)))).
\end{aligned}
\]

The first command is decoded from the candidate itself; a positive later
pointer \(r\) is decoded from \(r-1\). The child inequalities for Cantor
unpairing imply strict decrease of a nonzero remaining pointer. MP's new
success action does not touch that pointer, the next-candidate counter,
or either scratch register. Thus every candidate finishes after finitely
many root iterations unless it halts, and the next-candidate counter
advances by exactly one. This is the same structural draining proof as the
original `step_pl`, `drain`, and `reach` arguments.

The candidate codes of \(Q_u\) are unbounded because \(u\) is a literal
Cantor component of the first command and \(P(a,b)\ge a,b\). Consequently
some \(Q_u\) lies beyond any initial candidate cutoff. After an arbitrary
initial partial word drains, the persistent enumerator eventually reaches
that candidate unless it has already halted. Its uniform property then
forces halting. This proves completeness from every clean command-boundary
state, even with arbitrary initial formula fields; the latter freedom is
used only for completeness, not for soundness.

Combining this with soundness from a safe initial boundary gives

\[
 \operatorname{Halts}(\text{cache-MP enumerator})
 \quad\Longleftrightarrow\quad C254(1).
\]

This is a finitary syntactic proof transformation, so its ordinary proof can
be formalized in ZFC. The transport from C254 to the chosen arithmetization
of Con(ZFC), and the changed binary table's bootstrap and simulation, must
still be stated at their actual proof strength. An external Lean model
calibration should not silently be advertised as an already completed
internal ZFC proof-code translation.

## 7. A separate exact simulation macro

For debugging or an alternative proof transport, the original successful MP
state can be reconstructed from the new success state. From \((0,S,0,b)\)
execute

\[
 \operatorname{DROP}(b);\operatorname{DROP}(0);\operatorname{MP}(0);
 \operatorname{NIP}(0);\operatorname{DROP}(0);\operatorname{NIP}(0).
\]

The result is \((b,P(0,S),b,0)\), or an earlier valid halt for \(b=1\).
The internal MP compares \(I(b,b)=8b(b+1)\) against \(b\). It fails when
\(b>0\); when \(b=0\) it succeeds, and the new zero-result success action
has the same required intermediate effect. This exact macro is useful
evidence that the discarded parameter and dummy truth entry can be recovered.
The shorter inductive construction above is the primary completeness proof,
so no branch-dependent resynchronization theorem is assumed.

## 8. Reproducible checks and source references

`cache_mp_verifier.py` parses the exact pinned `Dag254.v` as finite data and
checks its SHA-256 before mutation. It interprets the structured RM with the
actual asymmetric break/continue semantics, compares both complete MP
subroutines with their respective four-register specifications, checks all
nine final registers, separately checks helper197, and tests the full new
MP-contract tail and six-command repair with exact integers. Its large-value
tests include 4,097-bit formula parameters. A fuel exhaustion raises an
error; it is never treated as rejection or as a passed theorem.

Run:

```
python cache_mp_verifier.py --dag Dag254.v --output cache_mp_results.json
```

The relevant primary repository files, all at the stated pin, are:

1. `lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v`,
   original structured program, SHA-256
   `538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3`.
2. `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Control254.lean`,
   `ifeq_eq`, `ifeq_ne`, `mp_branch` and exact destructive-comparison exits.
3. `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Lib254.lean`,
   especially `loop197` and the all-field transfer contract.
4. `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Macros254.lean`,
   parameter push, implication constructor, and stack contracts.
5. `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean`,
   exact command interface, Safe, Contract, leaf/gen/MP proof blocks, and
   draining/enumeration proofs.
6. `Computability/BusyBeaver/Research/ZFC/mp_dummy_push_partial_cost.md`,
   the prior distinct deletion and why its unchanged state count does not
   cover this new destructive/cache interface.

Mira-Cult's machine and calculus, Jeff Ketchersid and contributors'
verification, Andrew James Wade's compiler, mira-emmy's 253 reduction, and
ProveIt's register-permutation bootstrap retain their original attribution.
