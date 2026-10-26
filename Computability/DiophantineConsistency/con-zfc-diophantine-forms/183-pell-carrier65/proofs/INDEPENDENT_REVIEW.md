# Independent mathematical audit of the trace-congruence reduction

Delivery paths: the reviewed mathematical graph is equation/carrier65.json, with locally rebased coefficient metadata. The final replay authenticates its delivered bytes. This rebasing changes no arithmetic row or coefficient value.

Reviewer: independent research agent `/root/direct_construction`.
Review date: 25 October 2026 (client date).
Source pin: `02a78a08603cbae248c19c23a75907c6c6bd6443`.

## Verdict and scope

The proposed fourteen-positive-variable polynomial is sound and complete relative to the exact inherited P66 calibration, provided its four fixed coefficients satisfy the pinned scalar interface. The new reduction itself needs no new primality, order, native-language, or controller assumption. It retains the entire coefficient tuple; its coefficient-specific calibration must be supplied separately.

This is an ordinary mathematical audit. It is not a new Lean/Rocq run or an external human review. The independent checks below establish the new unbounded argument and the exact degree calculation by hand; they do not replace the old native/Pell/refutation theorem.

## Inspected sources

1. `Computability/DiophantineConsistency/equation.tex`, at the source pin above.
2. `Computability/DiophantineConsistency/research/admissible942-independent/PROOF.md`, entire file, especially sections 4 and 12.
3. `Computability/DiophantineConsistency/con-zfc-diophantine-forms/174-start-marker-compositions/compact66/calibration/P66_POSITIVE_PROOF.md`, entire file.
4. The collection README's comparison of existing fourteen-positive forms and its explicitly rational-leaf 65-operation P66 evaluator.
5. Source170's quotient-carrier README, which uses a different eliminated quotient and auxiliary combined-root carrier.

The first two files use the admissible942/radix47 constant specialization. The source174 calibration is a uniform arithmetic proof with a separately bound historical radix67 tuple. No equality between those tuples is asserted or used.

## The change

Use the exact parent abbreviations, but remove positive unknowns h and tau and introduce one positive unknown n. Set

    tau_hat = E*n+k-R.

Remove the factor Nk=k-hE-R. The new equation is

    N0_hat*N1*Na*Nt*Ns-Delta=0,
    N0_hat=tau_hat^2-ell*(ell+k).

Every other definition, coefficient and domain is unchanged. Fourteen independent positive coordinates remain. The expression is an ordinary integer polynomial.

## Full sign recovery before using tau_hat positivity

For every positive input, Delta=(a+2)^2-1>0 and

    Ns=Delta*(f^2-Delta*i^2*c^4).

After cancellation, the five integer factors N0_hat,N1,Na,Nt and the normalized Ns multiply to 1. Each is therefore plus or minus one.

The coefficient in N0_hat is m(m+1), where m=EY>1 and ell=mk. The negative equation u^2-m(m+1)v^2=-1 has no integer solution for m>1. One elementary proof chooses a solution with least positive v. The cases v=1 and v=2 lie strictly between consecutive squares. For v>=3, put

    u'=(2m+1)|u|-2m(m+1)v,
    v'=(2m+1)v-2|u|.

Both are positive, 0<v'<v, and their norm is again -1. Positivity of u' follows by squaring: v^2>=9>4+1/[m(m+1)]. The other inequalities follow from m v<|u|<sqrt(m(m+1)) v<(m+1/2)v. This contradicts minimality.

Delta is 0 or 3 modulo 4. A difference x^2-Delta*y^2 cannot be -1 modulo 4, so both N1 and normalized Ns are +1. Finally, Na is congruent to y^2 modulo 4 when S is even and to V^2 when S is odd. Thus Na cannot be -1. It follows that all four norm factors and Nt are +1. No sign of tau_hat or C has been assumed.

## Derivation of the rank bound from Nt=1

Assume only the pinned scalar boxes

    beta>=31, K>0, 0<MC<beta<MF<2beta,

where MF is the source mask with its one beta shift. Put q=beta*J+1.

If C<=0 then (K+w)C<=0, while F,z>=1 imply q-F-z(q-1)<=0. This contradicts Nt=1. Hence C>0.

Write u=q-F. Since C=u-alpha>0, we have

    2<=u<=q-1, 1<=alpha<=u-1.

For P=(q-1)u+alpha, these give

    2q-1<=P<=q^2-q-1.

The coefficient term obeys

    0<(MC+q*MF)*J<(1+2q)(q-1).

Consequently the actual rank satisfies the stronger bounds

    q(q^2-1)<R<q^4-q^3<q^4-2.

Also E=sw*q^4>=q^4. Therefore

    tau_hat=E*n+k-R>=E+k-R>k+2>0.

This proof order eliminates a possible circularity: positivity of tau_hat is obtained after Nt=1, not before the norm sign argument.

## Restoring the omitted quotient

The positive solutions of

    tau_hat^2-m(m+1)k^2=1

have the form

    tau_hat=chi_(2m+1)(r), k=2*psi_(2m+1)(r), r>=1.

Indeed (2m+1,2) is the least positive Pell solution; a solution with k=1 is impossible, and the usual multiplication by its inverse decreases every solution with k>2. Hence the standard recurrence classifies all positive solutions.

Since 2m+1=2EY+1 is 1 modulo E, the Chebyshev/Pell recurrence yields tau_hat=1 modulo E. The defining tau_hat equation gives k-R=1 modulo E, so

    h=(k-R-1)/E

is an integer. Because R<E-2 and k>=2, its numerator is strictly greater than -E, whence h>=0.

If h=0, then k=R+1<E-1. At rank r=1 we have k=2 and therefore R=1, contradicting the lower rank bound. At r>=2,

    k>=2*psi_(2m+1)(2)=4(2m+1)=8EY+4>E,

also a contradiction. Therefore h>0. Restoring tau=tau_hat gives a positive parent tuple with Nk=1 and exactly the original remaining factors. Parent soundness applies.

## Converse and witness maps

A finite refutation has the parent theorem's canonical positive P66 witness with Nk=Nt=1. In particular k-R=1 modulo E and tau^2-m(m+1)k^2=1. Its positive Pell trace also satisfies tau=1 modulo E and tau>k. Thus

    n=(tau-k+R)/E

is a positive integer. Substituting it gives tau_hat=tau and the new equation.

If the parent theorem's all-zero sign recovery is invoked, these constructions are inverse maps on the entire positive zero sets:

    new -> old: h=(k-R-1)/E, tau=E*n+k-R;
    old -> new: n=(tau-k+R)/E.

Without that all-zero sign recovery, the canonical completeness witness alone already suffices for equivalence of zero existence. The proof must not call the maps ambient positive-coordinate bijections; their domains are the zero sets.

## Exact operation and degree checks

The old circuit computes Nk with one multiplication and two subtractions and multiplies Nk into the output once: four operations disappear. Computing tau_hat requires one multiplication, one addition and one subtraction: three operations appear. Every other gate remains. The count is 66-4+3=65 integer-leaf binary operations.

The new tau_hat has degree 7, so its square has degree14. The dominant term of N0 remains -ell^2 of degree22. The remaining factor degrees are 18,62,2,46. Their sum is150; subtracting Delta, degree12, cannot alter the leading form.

Let q0=beta*J and k0=eta+zeta. Dividing the independently inspected parent leading form by the old leading factor -h*w*s*q0^4 gives the complete new leading form

    8*q0^87*gamma*i^4*k0^13*w^12*s^25*T^2*f^4
        *(w*(q0-F-alpha)-z*q0).

It is nonzero for every beta>0. For example its coefficient at

    J^88*z*gamma*i^4*eta^13*w^12*s^25*T^2*f^4

is -8*beta^88. Thus the total degree is exactly150, not merely bounded by150.

## Comparison and limitations

The change improves the matched parent simultaneously from 15 to14 positive unknowns, 66 to65 integer arithmetic operations, and degree157 to150, without increasing its fixed coefficients. This is a concrete improvement of that construction. It is not a proof of global minimality.

The collection's earlier 65-operation P66 evaluator explicitly used rational leaves and retained15 variables. That is not the present result. Source170's quotient carriers are conceptually related but absorb another quotient through an auxiliary root carrier and require additional scaling; the inspected formulas are not this trace-congruence substitution. No exhaustive literature-wide novelty claim has been checked.

## Independent finite DAG verification

The separate standard-library checker `check_carrier65_independent.py` was run successfully on the literal `carrier65.json`. It imports no producer code. Its receipt is `CARRIER65_INDEPENDENT_RECEIPT.json`.

The checker validates the exact variable list and positive domain, integer-only leaves, operation syntax and topology, and liveness of every gate, unknown and fixed port. It checks 23 formal polynomial identities at the displayed definition boundaries in an independently implemented sparse ring. It separately checks the main-norm cancellation identity. A full univariate expansion after a specified positive linear specialization has degree 150 and a nonzero coefficient agreeing with the hand-derived complete leading form. Together with the proved global upper bound of 150, this authenticates the exact degree of the literal graph.

The checked graph has 37 multiplications, 16 additions and 12 subtractions. Its SHA-256 at the time of review was `eb5e99dea2514e1b4aef3bdfda260b72e178468dcbc7a47e8ca0d39be251e4d2`; changing nonmathematical packaging metadata can change that file hash without changing the circuit. No random finite test is used as a substitute for the unbounded proof above.

