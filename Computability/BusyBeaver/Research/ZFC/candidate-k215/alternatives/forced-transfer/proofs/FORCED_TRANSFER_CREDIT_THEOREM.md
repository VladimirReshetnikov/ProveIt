# Exact seven-head debt for one forced transfer before every candidate

## Status and required scheduler

This is an all-natural resource theorem for the abstract sequence

    S;W(0); S;W(1); S;W(2); S;W(3); ... .

Here W(n) is the ordinary three-command candidate word, with fields S=[0], MP(x)=[1,x], AX(c;x,y)=[c+2,y,x]. Within a candidate, a positive continuation cursor is decremented before its next first-field read. This is not either of the earlier biased-cursor schedules.

The exact CFG audit of `research215_round6_calculus/zero_st.sites.json` is a separate binding obligation. The source auditor reports that the added CB1 forces a direct S after refill and before decrementing/decoding the copied counter, giving the displayed sequence from scheduler counter1. Full binary runtime and literal startup remain separate obligations.

Use conservative balances S=−1, MP=0, AX=+10. A successful MP may additionally push a theorem zero, which is deliberately ignored.

**Theorem.** Every finite command prefix of the displayed infinite sequence has conservative balance at least−7. Equality is attained immediately before candidate3, at its forced S. Consequently ten initial theorem heads above an arbitrary opaque tail leave at least three safe heads throughout every nonhalting run.

The debt is seven, not six: after the first three blocks the balance is−6, and the next forced S executes before the positive AX root of candidate3.

## 1. Ordinary candidate recurrence

Let P(a,b)=(a+b)(a+b+1)/2+b and f be its right projection. Let s(n) count S commands in W(n). Define

    g(0)=0,
    g(r)=s(r−1) for r>0,
    A(N)=sum_{n<N}s(n).

The zero value means an exhausted cursor ends the current candidate; it does not execute W(0). Direct parsing gives

    s(P(0,y)) = 1+g(y),
    s(P(1,y)) = g(f(y)),
    s(P(a,y)) = g(f²(y)) for a≥2.

In particular s(0)=1, even though g(0)=0. Every recurrence argument is smaller than the current positive candidate number, by strict decrease of positive right projections and the predecessor wrapper.

## 2. All-natural counting theorem

We claim A(N)≤N for all natural N. Prove this by strong induction. A(0)=0, A(1)=1, and A(2)=1 are direct.

Put T_q=q(q+1)/2, and let r(L) be the number of nonempty Cantor diagonal blocks among indices below L: for L>0 it is the least r with T_r≥L, and r(0)=0. The sequence f(0),f(1),... splits into consecutive blocks

    (0), (0,1), (0,1,2), ... .

If u(0)=0 and every relevant positive prefix sum of u is at most its length minus one, then

    sum_{y<L}u(f(y)) ≤ L−r(L).

Each full or nonempty partial block enumerates a prefix of u and saves at least one relative to its length. All prefix lengths required below are smaller than the induction target.

For g,

    sum_{j<L}g(j)=A(L−1)≤L−1   (L>0).

Thus the pullback bound applies to g, and then again to g composed with f. Write

    H(L)=sum_{y<L}g(f(y)),
    H2(L)=sum_{y<L}g(f²(y)).

Both satisfy H(L),H2(L)≤L−r(L).

At a triangular boundary T_q with q≥2, decompose all complete diagonals by their root commands. The q S roots contribute q plus their suffix counts A(q−1); the MP roots contribute H(q−1); the AX roots contribute the successive H2 sums. Exactly,

    A(T_q)=q+A(q−1)+H(q−1)+sum_{l=1}^{q−2}H2(l)
          ≤T_q−D_q,
    D_q=sum_{l=1}^{q−1}r(l)−(q−1)≥0.

Every induction index is below T_q. The q=1 boundary was handled directly.

For a general N=T_q+j, 0≤j≤q, a partial diagonal begins with q−1 AX roots and then one MP root, with the S root last. If j≤q−1, its additional cost is H2(j)≤j. If j=q, its additional cost is

    H2(q−1)+g(f(q−1))
    ≤q−1−r(q−1)+f(q−1)
    ≤q−1.

Here g(m)≤A(m)≤m for m>0, and g(0)=0. Also f(q−1)≤r(q−1). Every nonzero induction argument remains smaller than N; q=1,N=2 is a direct base. Therefore A(N)≤N for all N.

## 3. Uniform large-candidate prefix bound

Consider any point in the forced S preceding candidate n or any point inside W(n). The earlier ordinary candidates0,...,n−1 have completed. There are n of them.

If n lies on Cantor diagonal q, at most2q+1 of all indices through n have a non-AX first command. Thus at least n−2q−1 earlier candidates have already completed a root AX, supplying at least10(n−2q−1) credits. A negative lower estimate is harmless. No positive credit from an unexecuted current AX is borrowed.

There have been at most n+1 forced transfers through this point. The total ordinary S cost is at most A(n+1)≤n+1, even counting the unexecuted remainder of the current candidate. Ignoring every inner AX and successful-MP push gives the valid lower bound

    10(n−2q−1)−(n+1)−A(n+1)
       ≥8n−20q−12
       ≥8n−20sqrt(2n)−12.

At n=32 the last expression is84>0, and its derivative is positive thereafter. Therefore every prefix associated with candidate n≥32 has positive balance. Only candidates0,...,31 remain.

## 4. Exact finite base and sharpness

The owned checker `check_forced_transfer_credit.py` expands the exact ordinary candidate words and checks each command prefix, including each forced transfer, for n=0,...,31. It obtains minimum−7 and exit balance155. Its finite certificate is `FORCED_TRANSFER_CREDIT_BASE.json`.

The first four blocks begin

    forced S; S;       [candidate0, cumulative−2]
    forced S; MP;      [candidate1, cumulative−3]
    forced S; S; S;    [candidate2, cumulative−6]
    forced S; AX; ...  [candidate3, first reaches−7, then recovers].

Thus−7 is attained and is the exact global minimum, not merely an upper bound on required credit. The all-natural argument above justifies the finite cutoff; the separate200,000-candidate S-count check in the receipt is only corroboration.

## 5. Protected-stack soundness

Track an explicit finite wrapper of theorem heads above a fixed opaque numerical tail, together with theorem-valued top and cache. Short S halts soundly if its incoming cache is theorem1; otherwise it consumes one safe wrapper head, moves the old theorem cache into top and the consumed theorem head into cache. MP applies numerical modus ponens or supplies truth0; successful-MP zero pushes only improve the wrapper balance. AX contributes ten theorem heads and resets its auxiliary parameters according to the inherited command contract.

The balance estimate applies to every nonhalting command prefix. Starting with ten safe heads, wrapper depth stays at least10−7=3. Hence no head of the opaque tail is exposed, including at forced transfers. An earlier intended halt is already sound, since the tested cache is theorem-valued.

This wrapper length is a proof invariant, not a claim that finite list length is uniquely recoverable from the natural-number stack code. The alias P(0,0)=0 is harmless.

For the proposed initial AX over tail2, the ten generated heads are safe because its incoming top/cache are theorem0 and its parameter restrictions are satisfied. Tail2 itself is not safe:2=P(0,1) and1=P(1,0), so a later decoded head would be refutation1. The margin-three theorem is therefore a genuine required protection, not a finite-simulation observation.

## 6. Scope

This proof establishes resource safety for the exact schedule starting with W(0), one forced S before each candidate, ordinary internal predecessor decoding, and the displayed S/MP/AX effects. It does not establish a binary state count, physical simulation, source CFG, blank startup or logical calibration by itself. Those separately checked obligations are necessary before promoting a candidate.
