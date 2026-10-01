# Canonical word bounds recover the four matrix histories

The [four-register interface](group_four_register_history.md) can recover
its state digits without assuming their positivity or individual range.
Increase its radix from `4q^2` to `8q^2` and pay one scalar bound on the
sum of the four history words. The resulting component costs
**47=15 multiplications+32 additions/subtractions**, with **five equations**
and **21 positive history fields**, apart from the ordinary input and the
two geometric parameters q,P. The bound needs one positive witness.

The converse uses the height of the actual shear word, rather than a
digit bound imposed on a proposed history. Once earlier digits have been
recovered, the next actual digit and the next canonical supplied digit
both lie between zero and the radix. Their difference cannot produce a
carry. This closes the history-range obligation under the stated geometry.

Physical selector typing, exact digitwise selected-source products, regular
macro control, and duration/height geometry remain separate obligations.
In particular47 is not a complete universal Diophantine bound.

## 1. Geometry and the paid scalar bound

Use the physical letters and action order of the preceding packet: each
of the eight nonidentity letters adds or subtracts one coordinate's mate,
and the ninth letter is identity. Retain the chosen fixed regular macro
language. Assume, for some t,

    t>=2, q>=2^t, D=q^2, B=8D, P=B^t.                (1)

Equality q=2^t is sufficient but is not required by this theorem. The
47-operation source computes D and B; the inequality relating q to t and
the power P=B^t are external hypotheses. If a later component needs B
dyadic, one may specialize q to a power of two. This packet does not
supply that arithmetic certificate.

Supply positive integers H0,H1,H2,H3 and a positive history_bound, with
the single comparison

    H0+H1+H2+H3+history_bound=P.                     (2)

It follows immediately that 0<H_i<P. Therefore each has a unique
length-t base-B expansion

    H_i=sum_(j=0)^(t-1) X_i(j)B^j,
    0<=X_i(j)<B.                                    (3)

These canonical digits may initially include zero or values at least
B/4. No per-digit inequality is an additional supplied condition.
Mathematical base expansion in the proof is not a free arithmetic gate:
the selected-source relation below specifies exactly where these digits
enter the component's external interface.

## 2. Selectors, changes and the ordinary-input boundary

Retain eight Boolean selector words of the common length t. At each
position at most one selector is one; all zero means identity. Their
selected physical word belongs to the fixed regular macro language.
For i=0,...,3, write

    S_i+ = sum_j s_i+(j)B^j,
    S_i- = sum_j s_i-(j)B^j,
    Z_i+ = sum_j s_i+(j)X_(i xor 1)(j)B^j,
    Z_i- = sum_j s_i-(j)X_(i xor 1)(j)B^j.           (4)

Supply their positive hats S_hat=S+1 and Z_hat=Z+1. In particular (4)
uses the canonical digits (3), even before the recurrence proves that
they form a genuine history. These are exact digitwise products, not
ordinary word multiplication.

Compute the same paid differences as the43 source:

    delta_i=(Zhat_i+ - Zhat_i-)
              -D(Shat_i+ - Shat_i-).                (5)

All hat offsets cancel. Thus delta_i has coefficients equal to the
proposed signed update at each position. They need not themselves be
canonical base-B digits or positive numbers.

Keep the ordinary numerical input x>0 and fixed positive compiler
numerals alpha,beta. Put r=alpha*x+beta, and use the unchanged ten-gate
boundary

    input_product=alpha*x; r=input_product+beta;
    D=q*q; c0=D+q; d0=D+1;
    rq=r*q; z=rq+1; U=c0+z;
    rz=r*z; V=d0-rz.                                 (6)

The initial values I_i alternate c0,d0 and the terminal values E_i
alternate U,V. Impose the four scalar comparisons

    B(H_i+delta_i)=H_i+E_i P-I_i.                    (7)

Computed V can be negative on arbitrary assignments. It is not treated
as an extra positive witness; the proof recovers its positive value on
an accepted trace.

## 3. Soundness by recovering the actual history

Independently follow the selected physical word from `(q,1,q,1)` in
ordinary integer arithmetic. Let v_i(j) be this actual signed state and
put Y_i(j)=D+v_i(j), including j=t. A product of j>=1 signed unit shears
or identities has each entry bounded by 2^(j-1), by the column-sum proof
in the preceding packet. Hence, for all j<=t,

    |v_i(j)| <= 2^(j-1)(q+1)
              <= q(q+1)/2 < D                       (j>=1).

The initial state also has absolute coordinates less than D. Therefore

    0<Y_i(j)<2D=B/4                                  (8)

holds for the actual word, regardless of the proposed histories and
regardless of the ordinary input r. It uses only (1) and the correctly
typed physical letters.

Expand each residual in (7) as an integer sum of powers of B. Its
constant coefficient is `I_i-X_i(0)`. By (3),(8), its absolute value is
less than B. Since the residual vanishes, reduction modulo B forces
X_i(0)=I_i=Y_i(0), simultaneously for all four coordinates.

Suppose positions through j-1 have been recovered in every coordinate.
All lower coefficients of all four residuals are then exactly zero.
The coefficient at position j, for 1<=j<t, is

    X_i(j-1)+change_i(j-1)-X_i(j).

The induction hypothesis and (4) identify its first two terms with the
actual next state Y_i(j). This coefficient is therefore

    Y_i(j)-X_i(j).

By (3),(8) it lies strictly between -B and B. After dividing the
residual by B^j, reduction modulo B makes this coefficient zero.
This proves X_i(j)=Y_i(j) for every i and completes the simultaneous
induction. It does not estimate the change from arbitrary candidate
digits; its estimate uses the already recovered genuine history.

Only the coefficient of B^t remains. It is Y_i(t)-E_i, so (7) forces
the terminal values exactly. No prior sign or size hypothesis on E_i
was needed. All recovered digits and the actual endpoint now satisfy
the strict bounds (8).

Finally, the same one-vector lemma as before works under the weaker
inequality q>=2^t. For either final matrix block M, its upper-right
entry has absolute value at most 2^(t-1)<=q/2. Equality
`M(q,1)=L_r(q,1)`, where `L_r=[[1+r,1],[-r^2,1-r]]`, first forces its
upper-right entry to1 and its upper-left entry to1+r. Determinant one
then forces the second row, since `(1+r)q+1` is nonzero. Thus the two
blocks are both L_r. The retained regular macro controller gives the
desired fixed-subgroup membership, not arbitrary ambient shear products.

## 4. Positive completeness

Conversely take an accepted physical word of length t satisfying the
regular macro controller, and choose any integer q>=2^t. Use its actual
shifted states Y_i(j) to construct all four histories and (4). Every
history is positive because its initial digit is positive. At each cell,

    sum_(i=0)^3 Y_i(j)<8D=B.

Summing in radix B yields `sum_i H_i<P`, with no carry. The explicit
witness `history_bound=P-sum_i H_i` is therefore strictly positive and
proves (2). All selector and selected-source hats are positive, even
when an entire field is zero. Telescoping the actual recurrence proves
all four equations (7). The ten-gate loader uses the ordinary x and
the same fixed program numerals as before.

This establishes both directions for arbitrary t. It also explains the
choice B=8D: four genuine histories jointly fit below P, allowing a
single positive bound at the same four additions that four separate
upper bounds would have cost.

## 5. Exact ledger and the remaining interfaces

Take the literal43 schedule, change only its paid B multiplier from4
to8, and append

    history_sum01=H0+H1;
    history_sum012=history_sum01+H2;
    history_sum=history_sum012+H3;
    history_bounded=history_sum+history_bound.

Compare history_bounded=P. This gives47=15M+32A and five comparisons.
The positive history fields are four H words, eight S hats, eight Z
hats and history_bound:21 in total. The external q,P and the ordinary
x are not included in that conditional history-field count.

The [masked-selection component](native_binary_masked_selection65.md)
can supply (4). Its general binary-mask identity permits zero digits,
so the canonical bounds (3) suffice for its soundness. The single-bound
specialization likewise extracts its output chunks from a paid scalar
bound; its half-radix condition is needed for completeness, not for that
extraction. Actual histories satisfy the stronger (8), so the specialized
positive output bound is available on every genuine trace.

Thus a composed proof can first use canonical history bounds and exact
selection, then recover every positive state digit by Section3. It need
not add a separate per-cell state-range predicate. It still needs the
duration/height geometry, physical selector typing and exclusivity, the
selected-source certificate itself, and the finite regular controller.
No sum of these partial ledgers is claimed as a complete universal bound.

## 6. Executable evidence

The [stdlib checker](group_four_register_canonical_history47.py) rebuilds
the exact47 DAG from the preceding literal schedule and compares its
deterministic [receipt](group_four_register_canonical_history47.json).
It checks full residual formulas on512 positive scalar assignments,
including negative computed terminal values. It enumerates every physical
word of lengths two through four, tests the genuine height and summed-word
bounds, and checks the resulting residuals against independent terminal
states. Non-dyadic q values are included for the relaxed height theorem.

Further fixtures use arbitrary canonical histories, including zero digits
and digits at least B/4. They compare aggregate acceptance with the actual
recurrence and boundary conditions. Actual accepting targets include the
fixed ordinary-input prefix24x+12. Mutations rebuild the selected-source
fields from the changed history rather than keeping stale selection data.
These exact finite tests supplement the uniform induction proof; they do
not implement the still-external geometry or controller certificates.

Two independent full proof/source/default reviews passed without findings.
One separately checked1,024 complete residual identities, including negative
computed terminal values,39 actual target traces and156 mutations with
independently rebuilt selector products. The other checked2,048 independently
implemented mutation fixtures, including zero and half-radix candidate
digits and non-dyadic q. Both verified the simultaneous induction, the
late endpoint recovery, the relaxed height bound and the exact47 ledger.
These finite checks supplement the parametric proof above.
