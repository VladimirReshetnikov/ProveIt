# Independent semantic review of the final 608-variable direct quartic

The reviewed construction is frozen in `research/optimized/final`. It has
608 nonnegative integer unknowns, 491 quadratic residuals, and a single
quartic formed by their squared sum. Its exact expanded polynomial has
7,582 nonzero monomials and maximum absolute coefficient 79,824,571.
The raw builder contains 25 power graphs, 20 shared Pell-index certificates,
14 binomial graphs, and two factorial graphs.

I found no arithmetic or existential-dependency gap in the reviewed source,
shared-radix, self-bounding-factorial, and shared-Pell interfaces. The
following is an ordinary mathematical review, with independent finite
interface checks. It does not assert a completed Lean or object-ZFC proof.
The simultaneous Pell existence theorem and terminal-wire elimination
receive separate independent reviews; this note checks their actual
interfaces and the hypotheses required by their use here.

## Positive powers: no hidden zero case

Every raw arithmetic gate uses nonnegative constants, addition, and
multiplication. All raw witnesses range over naturals. Therefore every
base, exponent, and auxiliary gate value is nonnegative before any
semantic theorem is invoked.

The first power is `2^L`, with `L=L0+1`. Thus its base and exponent are
positive immediately. Its actual modulus row is

    4 A = T + 5,       T = output + gap + 1.

Since `T>=1`, this proves the common `A>=2` without assuming correctness or
positivity of the output. The common bound row is literally

    W = sum_j (n_j+k_j),

with all 25 distinct power pairs included exactly once. Consequently
`W>=3`, and for every call `W>=n_j,k_j`, regardless of whether a later
call's arguments have yet been proved positive. The common growth norm is

    A^2 = 1 + W^3(W+2) Z^2.

It follows that `Z>=1` and `A>W`. This justifies the natural-to-integer
subtraction rewrite `A dot-minus n=A-n` at every call.

For a call with positive exponent k, its shared index has
`Y=k+yk>=1`, `B=1+4Y(q4+1)>=5`, and `V=Y^2(vd+1)>0`.
The three actual norms and congruences therefore satisfy every side
condition of the inherited nonzero Pell-index criterion. The common
auxiliary norm forces `U>0`. The one-sided quotient equations imply
the original congruences. The selected positive-power criterion applies
to that call and proves its output is the true positive power.

The static checker proves positivity of all 25 calls in actual macro order.
It computes lower bounds only from the semiring gates, literal added ones,
previously justified positive-power outputs, and completed factorial
identities. It never marks a binomial output positive: such an output may
vanish when its lower argument exceeds its upper argument. Both factorial
outputs have lower bound zero before their own semantic lemma is applied.

This ordering is valid with the self-bounding factorial radius. If its
proposed output f is initially zero, the radius `f*n^2` is still natural,
the binomial upper argument `f*n^2+n` is positive because n is positive,
and the numerator base `f*n^2+1` is positive. Hence no factorial output
positivity is assumed in order to justify the powers used to determine it.

## Shared radix: the upper bounds are actual equations

The final construction uses one radix `q=2^L+1` and one global row

    L = N_1 + ... + N_14.

The `N_j` are exactly the fourteen literal binomial upper-argument nodes.
They are natural, so this equation entails `N_j<=L` for each j. It replaces
the earlier fourteen separate upper-bound slacks. No unattached maximum,
oracle bound, or external assumption occurs in the final polynomial.

For each graph, all coefficients of `(q+1)^n` are at most `2^n<=2^L<q`.
The actual graph consists of

    (q+1)^n = q^k (q*h+c) + r,
    q^k = r+rs+1,
    q = c+cs+1.

The latter two rows impose the exact remainder and digit ranges. Base-q
expansion therefore proves `c=binom(n,k)`, including `c=0` for `k>n`.
The audit checks each of these literal interfaces and its corresponding
shared numerator/denominator power nodes. No individual radix graph is
silently left disconnected.

For completeness, first choose the proof/CRT data and true factorial
outputs, then form the fourteen semantic upper arguments. For the final
self-bounding factorial graphs these are

    H!*H^2+H, t!*t^2+t, Q+t, A_1,...,A_11,

where `Q=(1+(t+1)T)^t+2`, `T=H!`, and the `A_j` are the chosen positive
CRT coordinate representatives. All are independent of the digit radix.
Set L to their sum and `L0=L-1`, which is natural since every argument
is positive. Then choose the true radix, digit powers, and all division
witnesses. The binomial and factorial identities recover precisely the
true arithmetic outputs used in choosing L.

The checker verifies this dependency claim on the literal data: replacing
each macro by its proved semantic function of its stated inputs produces
an acyclic graph. All fourteen binomial argument pairs are independent
of `digit.limit_minus1`. All 25 power argument pairs depend only on the
explicit source/CRT parameters and that digit-limit parameter, and on no
private Pell index, quotient, or shared-environment coordinate.

Thus the global Pell bound can also be chosen after all intended true
power bases and exponents are known. Sharing Pell witnesses introduces
no circular size demand into the source parameters or digit limit.

## Self-bounding factorial: uniqueness, including the initially zero output

For n>=1 and candidate f>=0, put

    rho=f*n^2,
    c=binom(rho+n,n),
    P=(rho+1)^n.

The literal rows are `P+c=cf+r+1` and `c=r+s+1`. Since `c>0` and `P>0`,
they give `c(f-1)<P<=cf`, so `f=ceil(P/c)>=1`. Moreover

    P/c = n! product_(i=1)^n (rho+1)/(rho+i) <= n!.

Thus f<=n!. If n=1, the ratio is exactly 1. Suppose n>=2 and f<n!.
Writing `a_i=(i-1)/(rho+i)`, one has

    sum a_i < n(n-1)/(2*rho) = (n-1)/(2*f*n) < 1/(2*f).

The elementary product inequality gives

    P/c > n! (1-1/(2*f))
        >= (f+1)(1-1/(2*f))
        = f + 1/2 - 1/(2*f) >= f,

contradicting `P/c<=f`. Hence f=n!. Conversely, with f=n!, the same
estimate gives `0<=f-P/c<1/2`, so `ceil(P/c)=f` and the exact natural
division witnesses exist. This proves the self-bounding factorial graph
without assuming the proposed output is correct or positive in advance.

The positive-input restriction matters: this source calls factorial only
at t and H, which are positive. No unproved extension to an arbitrary
zero-input positive-power graph is used.

## Source and envelope bindings

The literal numerical-calculus module is identical, as a parsed Python AST,
to the inherited source except for deleting its two beta remainder-range
equations. The new bounds `S,S'<=y` make those equations restorable; the
cofinal beta-code proof supplies such codes for every finite trace.

The independent checker reconstructs the actual source semiring DAG,
matches all 486 nodes of its envelope certificate, and checks the exponent
recurrence yielding 6,893,164. The bound used for CRT is therefore attached
to the actual source polynomial. The larger modulus does not change
solvability because the CRT theorem is proved for every valid upper bound.

## Exact finite audit scope

`audit_final_semantics.py` checks 221 literal semantic-interface rows. This
includes all 25 positive-power terminal interfaces; all 20 index norm,
congruence, and divisibility interfaces; all 14 digit graphs; both factorial
graphs; the common Pell environment; and both exact global sums.

It reconstructs the raw builder and compares its full variable list, all
1,424 raw rows, all 41 macro records, all power/index inventories, and
the shared environment against the frozen `raw_builder.json`. It also
independently expands the final 491 quadratic residuals, recovering
exactly the delivered 608-variable quartic and all its stated metrics.
The separate row-elimination certificate is the remaining finite bridge
between the raw and final systems; that bridge is audited independently
by the parent task.

Normal and optimized Python runs pass. These checks do not determine
whether the consistency equation has a solution. They validate the
concrete interfaces required by the unbounded mathematical arguments.
The original C222/ZF/ZFC calibration and Pell-Matiyasevich theorems remain
named mathematical dependencies, with source pins in the complete package.
