# Independent review of the PA194NQ composition

This review concerns the candidate with dense transition-table SHA-256
`d1cf0f6e7a3c8f999d045694efc107dd1f9a03d45dd6c15e3d197ff7754c7231`.
The comparison corpus is ProveIt commit
`3cc7fbf75ba111a0da696ef2f6001dd528891bd5`.

## Result and scope

The NQ construction is a defensible new composition of two previously
published changes: the current-top, no-push MP controller of PA194N and the
premise-exchanged distribution head of PA194Q. Its source has 3,654
instructions; exactly 79 resolved instructions differ from the delivered N
source. The 190-token emitter was independently expanded in a free
constructor algebra, without importing the compiler or tape validator. All
ten pushed entries, all six symbolic parameters, the current top, and the
final guard suffix match the exchanged calculus. The full finite K/S/MP
exchange certificate was independently replayed.

Exact rooted action-graph comparison against all 34 existing 194-state
classes found no match, including at every spanning root and after
reflection or global symbol exchange. This includes the auxiliary and
rejected classes conservatively. The graph comparison proves a structural
nonduplication statement, not a theorem about semantic originality.

The ordinary PA-provability argument composes successfully, provided that
the inherited separated-head calibration and the separately checked
source/tape simulation are included with their existing mathematical
justification. This review does not claim a new end-to-end Lean or Rocq
theorem, nor either direction over iPRA.

## The exact logical change

Use the unchanged numerical constructors

\[
 p(a,b)=\frac{(a+b)(a+b+1)}2+b,\quad
 I(a,b)=4p(a,b),\quad U(i,a)=4p(a,i)+2.
\]

At the sixth retained head, put

\[
 P=U(D,A),\quad Q=U(D,I(A,H)),\quad R=U(D,H).
\]

Replace the old axiom instance `I(P,I(Q,R))` by `I(Q,I(P,R))`.
No other generated head, guarded separation formula, parameter-read order,
or stack position changes. In top-first order, the modified head remains
q2; q1 is the separate Gamma(A) head, q8 the dominated rho head, q9 the
generalization U(d,h), and q10 the saved old current top.

The ordinary implication calculus proves the closed exchange formula

\[
 I(I(P,I(Q,R)),I(Q,I(P,R))).
\]

The supplied finite certificate is parametric in P,Q,R and uses only K,
S, and MP. It replays successfully. Those K and S schemes are derived
solely from the unchanged restricted rho basis: the pinned
`jamesyc-upstream/pa196/PA196/Logic/ImplicationBasis.lean` supplies `row`
using `.r8`, and its `rules` record uses MP, that row, reflexivity of
numerical <=, and the two bounds on I. It imports no h6 derivation into
this record. In fact that file already exports a direct `exchange`
derivation from the same restricted basis.

Let C and C_Q denote the old and exchanged numerical calculi. Translate a
C derivation recursively, replacing each old h6 leaf by the new h6 leaf
followed by exchange with P and Q interchanged. MP and generalization are
preserved, as are all other axiom leaves. The converse transformation uses
exchange in its displayed orientation. Both transformations preserve the
numerical conclusion, are primitive recursive on coded finite proofs,
and have PA-provable correctness by induction on those proofs. They do
not require injectivity of formula decoding: numerical aliases such as
I(0,0)=0 are harmless because each step is a constructive derivation with
the intended numerical conclusion. Thus refutations translate in both
directions.

## Why the N compiler survives the emitter replacement

Import the no-push command compiler from N, not the cached-head command
compiler from Q. The NQ MP and Shift effects are exactly

\[
 \mathsf{MP}_x(t,w,d,h)=
 \begin{cases}
 (d+x,w,d+x,0),&I(t,d+x)=h,\\
 (0,w,d+x,0),&I(t,d+x)\ne h,
 \end{cases}
\]

and Shift halts when t+h=1, otherwise returns
`(h,tl(w),d,hd(w))`.

The N compiler's Push, Pop, Discard, Offset, selectors, and generalization
proofs use only the following facts about the AX output:

1. There are nine generated stack entries and the saved old top.
2. Their positions do not change.
3. q1 through q8 and the gate are 0 modulo 4; q9 is 2 modulo 4 and at
   least 2.
4. The last generated entry is exactly U(d,h), and the saved top is
   unchanged.

All four facts hold after premise exchange: the changed head is still an
implication. In particular all AX-Shift sequences used for Push, Pop and
selection remain nonhalting over arbitrary natural stores, independent of
consistency. The old proof that literal Cantor-zero aliases cause no stack
ambiguity applies unchanged.

For the MP compiler, recursively compiled premises leave

\[
 (0,[a,I(a,b),0;w],0,0)
\]

before the two Shifts. Either a Shift halts early, or MP succeeds and
returns `(b,[0;w],b,0)`; the total Pop removes the reserved zero and clears
the offset, giving `(b,w,0,0)`. Nothing in this argument refers to h6's
internal expression. Hence a C_Q proof compiles to a word returning its
conclusion with the stack framed and caches cleared, or halting earlier.

To compile an old C proof, first translate its h6 leaves into C_Q as above.
The resulting compiler is still primitive recursive and still works from
every incoming store after the inherited AX clearing prefix. The cofinal
prefix family used by N ensures the unchanged carried-store scheduler
eventually tests a halting word whenever a refutation exists; a reset
between failed scheduler trials is unnecessary.

For soundness, annotate current top, cache, and canonical live stack
entries by C_Q derivations, and use the same command invariant as N. The
changed axiom is a C_Q axiom, or equivalently an old-C theorem obtained by
exchange. Successful MP annotates its conclusion; failure supplies truth;
Shift transports annotations. A successful t+h=1 test gives a refutation
because one of the two annotated natural codes is 1. Compose with the
primitive-recursive C_Q-to-C translation and the inherited C-to-PA
translation. These are syntactic proof transformations, not a truth
predicate or an application of PA reflection.

Together with the ordinary separated-head PA calibration this proves both
finite syntactic reductions between a PA refutation and a source halt.
The separately checked positive source/tape simulation and exact blank
seed then transport them to the literal table. Classical reasoning inside
PA yields the claimed nonhalting/Con(PA) equivalence.

## What makes this more than relabeling

Two independent recurrent semantic witnesses distinguish the composition
from its parents:

* Against N, at D=0,A=0,H=1 the old h6 numerical code is 4,331,850,108 and
  the exchanged h6 code is 198,492. These are different formulas emitted
  during ordinary AX execution, and the axiom-proof translator is needed.
* Against Q's cached-head controller, MP_2 on `(0,0,0,20)` gives
  `(2,0,2,0)` in NQ and `(0,0,0,2)` in Q. The successful MP contract and
  continuation compiler differ.

The control graph is also absent from the old corpus under the explicit
conservative equivalences tested above. It is appropriate to call this a
new 194-state design combining two established transformations. It would
overstate the result to claim a new exchange theorem, a newly invented
no-push principle, a lower Busy Beaver state threshold, or an exhaustive
lower bound ruling out 193 states. Whether a new composition meets a
particular informal standard of "materially different" is partly a matter
of scope; the recurring formula emission and command-store changes are
concrete, rather than cosmetic graph renamings.

## Reproduction and limits

`check_nq_emitter.py` takes explicit paths for the Q grammar, candidate NQ
instructions and table, the baseline N instructions, and the frozen Q
exchange certificate. Its receipt is `nq_emitter_review.json`.
`nq_novelty.json` records the independent full-tuple graph comparison;
`check_novelty.py` reruns it from the frozen comparison tables.

The emitter checker assumes the separately proved numerical semantics of
the named source macros. It proves the resulting formula identity for all
parameters in a free algebra; it does not verify those macros on physical
tape. The exchange checker replays the finite K/S/MP certificate; it does
not replay the inherited restricted-rho derivations of K and S. The
ordinary PA claim therefore rests on a fully identified composition of
written proof arguments and finite certificates, not on an exported
trusted-kernel endpoint for the exact new machine.
