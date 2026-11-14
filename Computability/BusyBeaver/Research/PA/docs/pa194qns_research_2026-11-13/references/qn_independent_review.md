# Independent review of PA194QN

## Result and scope

The proposed Q + no-push composition has a sound preservation argument relative
to the supplied separate-head calculus/PA calibration. I found no new logical
gap in combining these two source transformations. This review does not supply
or claim a new end-to-end Lean/Rocq formalization of the PA equivalence, nor an
iPRA equivalence. The inherited proof-producing translations between the
separate-head calculus and PA must remain explicitly identified.

The literal candidate reviewed is the 194-working-state table with SHA-256
`d1cf0f6e7a3c8f999d045694efc107dd1f9a03d45dd6c15e3d197ff7754c7231`.

## Independent checks actually run

`audit_qn.py` imports no builder, compiler, or symbolic physical simulator. It
checks the Q grammar's 190-token AX word against the original AX word; only
the half-open token interval `[102,121)` changes. It symbolically executes both
19-token blocks in a free constructor algebra. Each block pushes the incoming
top, leaves the older stack unchanged, and emits its exact claimed head.

The script expands the candidate's saved node definitions with the Q grammar
and obtains exactly its 3,654 saved primitive sites. An independent resolver
using ordinal subtree intervals reproduces all 3,654 saved instruction rows.
Comparing that instruction graph with the N candidate gives exactly 79 changed
instruction rows, all between zero-based indices 1,953 and 2,067 inclusive.
The no-push splice is separately checked as `node163 = (node6,node54)`.

Finally, a flat replay verifies the supplied premise-exchange certificate:
61 lines, 17 K instances, 14 S instances, and 30 modus-ponens steps, with no
assumptions. K and S remain inherited derived rules of the unchanged dominated
implication basis; checking a K/S certificate does not by itself reprove that
derivation from the numerical basis.

These checks are recorded in `qn_review_receipt.json`. They supplement the
construction and independent physical checks performed by the main task.

## Exact logical change

Use Cantor pairing `p(a,b) = (a+b)(a+b+1)/2 + b`, implication
`I(a,b) = 4p(a,b)`, and universal coding `U(i,B) = 4p(B,i)+2`.
For AX parameters `D,A,H`, write

* `P = U(D,A)`;
* `Q = U(D,I(A,H))`;
* `R = U(D,H)`.

The original sixth logical head is `I(P,I(Q,R))`; the Q head is
`I(Q,I(P,R))`. No parameters or stack positions are exchanged. All other
heads, the numerical tags, the guarded separation formula, and the inference
rules are unchanged.

The unchanged dominated implication basis proves the unrestricted exchange
scheme `(a -> (b -> c)) -> (b -> (a -> c))`. This uses neither version of the
quantifier-distribution head. Applying it once at `(a,b,c)=(Q,P,R)` recovers
the old head from the new one; the opposite substitution recovers the new
head from the old one. Replacing each affected axiom leaf and recursively
translating MP/generalization nodes gives primitive-recursive, conclusion-
preserving translations between the two numerical calculi. PA proves these
translations correct by induction on finite proof trees.

The code-zero alias `I(0,0)=0` causes no issue: the numerical MP equality is
preserved. An arithmetic formula translation should give a proof of the
instancewise equivalence for implication at this alias, rather than assert
literal syntax equality with the translation of truth.

## Why the N command compiler remains valid

The Q emitter produces the same ten stack entries in the same positions,
except for the internal form of `q2`. The crucial endpoint entries are
unchanged: `q8` is the dominated implication head, `q9=U(d,h)`, and the
tenth entry is the saved old top. The gate and `q1,...,q8` have residue zero
modulo four; `q9` has residue two and is at least two. None of these generated
values is one.

PA194QN uses N's original sum guard and its no-push MP, on store `(t,w,d,h)`:

* Shift halts exactly when `t+h=1`; otherwise it returns
  `(h,tl(w),d,hd(w))`.
* Put `b=d+x`. Successful `MP_x` returns `(b,w,b,0)`; failure returns
  `(0,w,b,0)`.

Consequently all of N's proof words and their proofs apply unchanged. In
particular, with `A0=AX_Q(0,0,0)`, use `Push=A0;S^9;MP_0`,
`Pop=A0;S^11`, and `Discard=MP_0` on stores with `d=0`.

The exact contracts are

* `Push(t,w,d,h) = (0,[t;w],0,0)`;
* `Pop(t,[a;w],d,h) = (t,w,0,a)`;
* `Discard(t,w,0,h) = (0,w,0,0)`.

Pop is total even when the saved top equals one: its eleventh Shift tests
`U(d,h)+t`, which is at least two. This is the essential difference from
the cached-controller Pop calculation in the Q packet.

For `1<=j<=7`, the selector
`Discard;AX_Q(A,D,H);S^(j+1);Pop^(9-j)` returns the selected `qj` on the
original arbitrary underlying stack with `d=h=0`. Thus the changed sixth
head is selected in the same slot as before. The gate and dominated-head
selectors and the generalization word also retain their original N proofs.

For MP, reserve a zero below the premise computations and use

`Discard;Push;C(I(a,b));Push;C(a);Push;S;S;MP_b;Pop`.

If neither recursive proof word halts early, the state before the two Shifts
is `(0,[a,I(a,b),0;w],0,0)`. If `a=1` an early halt is acceptable. Otherwise
the successful MP gives `(b,[0;w],b,0)`, and the total Pop returns
`(b,w,0,0)`, including `b=1`. The reserved zero is required to clear the
outgoing cache while preserving the arbitrary tail. One must not replace
the final Pop by the single Shift used by Q's cached-controller compiler.

The Cantor identities `hd([a;w])=a`, `tl([a;w])=w`, and `[0;0]=0` suffice
for every displayed contract. No free-list assumption is being made.

## Completeness, soundness, and the inherited boundary

Induction on numerical derivations gives a finite word `C(e)` that, from
any `(t,w,0,0)`, either halts or returns the conclusion on the same tail with
`d=h=0`. If `e` proves one, `A0;C(e);S` halts from every incoming store.
This all-store property is necessary because unsuccessful scheduler trials
retain the current store. A cofinal family is obtained by prefixing the
word with `AX_Q(k,0,0)`; the increasing fresh counter therefore eventually
tests a suitable candidate even though it starts at two.

For soundness, annotate the top, cached head, and canonical live stack with
numerical derivations. Q's AX heads are valid in the Q calculus, successful
MP produces its conclusion, failed MP produces truth, and Shift transports
annotations. If `t+h=1`, natural arithmetic gives either `(t,h)=(1,0)` or
`(0,1)`, hence an annotated refutation. Offset `d` need not be a theorem code.

The Q exchange translations, these N source-word transformations, and the
positive physical source simulation together establish the preservation
theorem. Composing with the inherited separate-head-calculus/PA refutation
translations gives the ordinary mathematical PA equivalence claimed in the
report. Finite traces are used to bind initialization and explicit
certificates; they are not extrapolated to infinite nonhalting.

## Search result from this review task

A completed radius-six blank-reachable window contraction search on latest
PA194HS covered 269,607 abstract state/window configurations and 28,755,456
trial row actions. It found zero accepted pair contractions, with zero
pair-combination skips. A radius-nine search restricted to pairs involving
the root guard control 68 covered 10,719,423 abstract configurations and
297,984 trial row actions and again found zero, with zero skips. Both searches
use a 64-step local simulation horizon and forbid exiting the observed
window. These are negatives for precisely these local interfaces, not state
lower bounds. The radius-eight abstraction also assigned a nonempty context
to every state/read row (3,097,013 configurations), so it did not expose a
provably unused transition row for a new helper. This does not prove that
every row occurs in the actual blank-tape run.

The copied contraction code is inherited from the PA194ZR packet, with the
guard-focused version differing only by its pair restriction. Its provenance
must be retained if it is included in the final archive.
