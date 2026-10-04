# Independent repeated-firing recurrence and legality review

Date: 2026-10-04. Verdict: **the stated arithmetic recurrence, selected-legality clause, and existential event-time target test are sound and complete under their stated masks and the inherited no-wrap spatial-shift lemma. No mathematical gap was found in these components.** This is a mathematical review, not a source-DAG or macro-expansion audit.

The prior binary audit was read as data at `/workspace/shared/sandpile-target-independent-audit-20261004/AUDIT.md`. No upstream program, submitted builder/checker, or Lean program was executed. `check_recurrence.py` is a new independent finite probe written for this review.

## 1. Hypotheses and mask ranges

Let b=2^m, K>=1, N>=1, b>=64(K+1), Q=b^N, and R=sum_{0<=t<K}Q^t. Let I=sum_{j in J}b^j for a set J contained in {0,...,N-1}, representing the spatial interior.

Write Sub(M,x) for binary bit containment of x in M. Assume

- Sub(IR,E)
- Sub((b-1)IR,Apre)
- Sub((b-1)I,V)
- Q(Apre+E)=Apre+Q^K V

Because b is a power of two, the masks contain disjoint blocks of bits. Consequently E=sum_t E_t Q^t with E_t=sum_j e_(t,j)b^j, e_(t,j) in {0,1}, and e_(t,j)=0 outside J. Independently of any recurrence argument, 0<=Apre<Q^K and 0<=V<Q. The full-digit mask does **not** yet imply that Apre+E is carry-free; that assertion must wait until the uniqueness proof below.

## 2. Recurrence soundness without presupposing small candidate counts

Define canonical cumulative counts only from the already-binary event stream:

h_(t,j)=sum_{0<=s<t}e_(s,j), for 0<=t<=K,

H_t=sum_j h_(t,j)b^j,

Astar=sum_{0<=t<K}H_t Q^t, and Vstar=H_K.

Here 0<=h_(t,j)<=t<=K<b, so these are genuine radix-b digits, H_t<Q, 0<=Astar<Q^K, and Vstar<Q. They are supported on J. In particular the canonical tableau satisfies both full-digit masks. This uses only the event mask and the radix bound, not a bound on the candidate Apre.

Since H_0=0 and H_(t+1)=H_t+E_t as integers,

Q(Astar+E)=sum_{1<=t<=K}H_t Q^t=Astar+Q^K Vstar.

Subtract this identity from the candidate recurrence:

(Q-1)(Apre-Astar)=Q^K(V-Vstar).

The integers Q-1 and Q^K are coprime. Hence Q^K divides Apre-Astar. Both Apre and Astar lie in [0,Q^K), so |Apre-Astar|<Q^K, forcing Apre=Astar. The displayed identity then gives V=Vstar.

Thus the candidate has exactly the desired digits:

- Apre_(t,j)=sum_{s<t}e_(s,j)<=t
- V_j=sum_{s<K}e_(s,j)<=K
- Apre_0=0
- Apre_(t+1)=Apre_t+E_t for t<K-1
- V=Apre_(K-1)+E_(K-1)

Only **after** this proof may one say that Apre+E is carry-free: every digit is <=K<b. There is no self-starting history, cyclic time, malicious spatial carry, or malicious frame carry. For this lemma alone, b>K suffices. K=1 and an empty interior are included.

The range for Apre is essential to the short uniqueness argument. The terminal V mask is compatible and useful as an explicit interface, although once Apre's range and E's mask hold, recurrence uniqueness already forces V to be canonical.

## 3. Selected legality: exact coefficient bounds

Retain the inherited geometric fact that all six shifts of an interior-supported Apre remain in the same spatial frame and give precisely the six physical neighbor counts. In particular exact negative-shift quotients exist, and there is no row, plane, or time-frame wrap.

Let eta_j be the initial heights, with 0<=eta_j<=20. In frame t let a_(t,j)=Apre_(t,j), and define

c_(t,j)=eta_j+sum_{w adjacent to j}a_(t,w).

Then

0<=c_(t,j)<=20+6t<=6K+14<b.

Therefore the packed stream C=initial*R+six shifted Apre has exactly these radix-b digits with no carries. This includes shell destinations; sources have interior support.

Let Csel=AND(C,(b-1)E), Asel=AND(Apre,(b-1)E), and require

Sub((b/2-1)E,L),

Csel=6Asel+6E+L.

Since b=2^m, the first mask fills all m bits precisely at event slots. The second fills the lower m-1 bits precisely at event slots. Thus selected C and A digits are c and a, all other selected digits vanish, and L has an independent digit ell in [0,b/2-1] at each event and zero elsewhere.

At any selected slot, the **largest possible coefficient before carrying on the right side** is

6(K-1)+6+(b/2-1)=6K+b/2-1.

It is <b because 6K<=b/2 follows from b>=64(K+1). Every unselected coefficient is zero. The equality is therefore digitwise and says

c_(t,j)=6a_(t,j)+6+ell_(t,j)

at every event. Equivalently,

eta_j+sum_{w adjacent to j}a_(t,w)-6a_(t,j)>=6.

This is exactly instability immediately before the layer. Prior own firings are correctly subtracted by 6Asel; the clause neither ignores their depletion nor counts current/future events.

Conversely, for a legal event the required slack is

ell=c-6a-6>=0,

ell<=14+6t-6a<=6K+8.

The declared radix ensures 6K+8<=b/2-1, so the complete slack range fits the mask. These inequalities also show that b>=12K+18 would suffice for this particular combination of recurrence, C carry control, RHS carry control, and slack completeness. The larger stated bound is safe. This observation is not a recommendation to alter another part of the construction that may need the larger bound.

## 4. From layers to a legal repeated-firing sequence and back

Every event layer is a finite set, with at most one event per site in that layer. The legality equation proves that every member is unstable at the start of the layer. Serialize its members in any order. Before a member fires, earlier distinct members of the same layer can only add chips to it; they cannot deplete it. It therefore remains unstable. Induction through the layers gives a finite legal sequence with exactly the canonical cumulative counts, allowing a site to recur in later layers.

Conversely, a finite legal sequence containing the target can use one singleton layer per firing, with K its length. Choose a power-of-two b>=64(K+1) and a sufficiently large legal box so every firing lies strictly inside. The canonical event/count streams satisfy the masks and recurrence, the exact spatial shifts give C, and the legal slacks above satisfy the selected equation. Thus these clauses capture unrestricted finite legal prefixes, rather than only binary prefixes. No stabilization or maximality hypothesis is involved.

## 5. Existential target time

Suppose the target point is correctly encoded as point=b^j with 0<=j<N. Let tau be a natural and POWER enforce S=Q^tau. The clause

Sub(E,point*S)

means that the low bit at position j+N*tau occurs in E. Since E<Q^K=b^(NK), containment of this positive single bit implies

j+N*tau<NK,

and hence tau<K. No additional explicit upper bound on tau is needed. The interior event mask also excludes a shell target. Conversely, any target event in any of the K layers supplies its own tau.

The assumption that j is the correct bounded mixed-radix spatial index remains necessary: the implicit tau bound does not replace the original physical coordinate bounds or prevent spatial aliases when those bounds are omitted.

## 6. Genuine remaining dependencies / scope limits

No gap was found in the recurrence, carry bounds, selected legality, or implicit target-time bound under the hypotheses above. The complete certificate still needs its existing independent obligations:

- b is genuinely a power of two and the explicit inequality b>=64(K+1) is enforced
- R and Q^K have their stated exact values
- Sub and AND have their proved natural-number semantics
- The physical initial stream is correct and has digits <=20 in radix b
- The six shifts satisfy the interior-face no-wrap lemma
- The target has its correct bounded spatial exponent
- The emitted polynomial/source implements all clauses and macro domains exactly

These are interfaces, not newly discovered flaws in the requested arithmetic lemma. This review does not audit the new variable-radix physical loader or emitted source and makes no new claim about those components.

## 7. Fresh tests

`python -I check_recurrence.py` passed:

- 334,026 arbitrary full-digit candidate tableaux across several small power-of-two radices, masks, frame widths, and horizons; all 148 satisfying recurrences had exactly canonical Apre and V
- 37,494 two-event-slot selected-legality cases, including a vacant middle slot; packed acceptance agreed exactly with both coordinatewise legal thresholds
- 7,814 target cases, including tau=K and tau=K+1; acceptance agreed exactly with an event at the target in a valid layer
- A deliberate undersized-radix counterexample b=2,N=2,K=2,Apre=4,E=5,V=2, demonstrating that a repeated count can masquerade as a neighboring digit if one omits the large-radix premise

These finite probes corroborate but do not replace the all-integer proofs above. The receipt is `receipt.json` in this directory.
