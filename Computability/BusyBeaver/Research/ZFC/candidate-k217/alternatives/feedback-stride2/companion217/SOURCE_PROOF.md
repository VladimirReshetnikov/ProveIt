# Common-footer global bias: exact source binding

Source SHA256: ab25e03f724b45011660aeecb120a27b896a5f5dca0cb3848dbfde49bccd42d8.
This note establishes source semantics, not a physical machine calibration. In particular, the first tested216-state allocation failed a CD1 runtime case and must not be promoted.

The independent owned checker audit_global_bias_source.py resolves all4734 leaf control-flow instructions twice: once using the existing continuation-stack reader and once using a new interval/ancestor resolver. It verifies exact equality of the MP and AX bodies with the previously calibrated transfer source and of the whole short-transfer body with the predecessor implementation.

There are exactly two old return edges: ordinal4696 is the common MP/AX branch return, and the zero branch of CD6 at4729 ends the short-transfer pop's restore loop. Both formerly targeted0 and now target4732. No other old edge changes. The return instruction at4696 is retagged from CC to CB, with its new address making the target exactly4732. At4732 CI6 increments scratch X, and at4733 CC3 returns to ordinal0. Thus every completed command, not merely MP/AX, executes the unique common footer exactly once. A halting command does not execute it.

## All-natural command boundaries

Let registers be (N,T,W,A,D,H,X,Y,L), with selector A and temporary X,Y initially0 at command dispatch after Read. The unchanged arithmetic command contracts give A=X=Y=0 at each normal command exit. Short transfer returns (T,W,D,H)=(old H,tail(old W),old D,head(old W)), halting only if old H=1. MP and AX retain their exact old equations. The footer therefore establishes A=Y=0 and X=1, preserving all other registers, at every next scheduler root.

## All-natural prelude

Schedule and Read are literally unchanged closed subtrees. Their standard loop invariants extend to arbitrary incoming nonnegative X=b:

- If L>0, Schedule decrements L once and leaves N and X=b unchanged.
- If L=0, Schedule copies N to L while accumulating/restoring the inherited scratch. Its complete result is L=old N, N=old N+b+1, X=0, with all other live registers unchanged.
- Read, beginning with selector A=0, scratch X=b, Y=0 and proof cursor n, computes unpair(n+P(b,0)), stores its left component in A and right component in L, and clears X,Y. In the only boundary cases needed here b=0 or1, P(b,0)=b. The inner successor operation sends (x,y) to (x-1,y+1) when x>0 and to (y+1,0) when x=0. Direct substitution in Cantor pairing shows each operation raises P(x,y) by1. Induction on the consumed cursor proves the claim for every n.

Consequently, at the invariant b=1:

- A continuing positive cursor L is first decremented, then biased back by1 in Read. The net decoding is exactly unpair(old L), not unpair(pred(old L)).
- An exhausted cursor refills from old N, advances candidate counter by2, and reads ordinary unpair(old N), because refill clears the bias.

All loops terminate by their usual finite unary counters. The changed numerical scheduler therefore has an exact all-natural source interpretation. Its own protected-credit and cofinal-encoding proof is still required, as are physical runtime and blank startup. The finite1209 prelude/footer probes in the audit corroborate these invariants but do not replace the induction.
