# A finite-period obstruction for guarded one-field convolution

The proposed equation

    (K+X-1)U=lambda*J_B+z*(q-1)                         (1)

does not compile arbitrary local computation under the common strategy of
using wide inner guards to eliminate all carries and all within-cell wrap.
Under the precise hypotheses below, every admitted cell word has a period
bounded by a fixed constant independent of its length and temporal shift.
A unique Start marker then bounds the entire word length.

This is an obstruction for a stated layout class, not for every one-field
compiler. It does not cover deliberate carries, cyclic feedback between
inner positions, more than one independent computation equation, or the
already refuted untyped interleavings. No lower bound for the general
51-operation mask interface is claimed.

## 1. The exact guarded layout

Fix an inner radix R>=3, a cell length L, and B=R^L. Let E be a fixed
nonempty subset of{0,...,L-1}. At each allowed inner position e, supply
a digit u_(i,e) in a fixed alphabet A_e contained in{0,...,R-1}, of
size at most M. At
positions outside E, the digit is0. These are genuine typed digits;
for example the one-field mask can restrict binary digits inside an
R-digit. Write

    U=sum_(i=0)^(N-1) sum_(e in E) u_(i,e)*R^e*B^i,
    q=B^N, J_B=(q-1)/(B-1), X=B^h modulo(q-1).

The ordinary indices i are cyclic modulo N. The typing condition is not
inferred from a decomposition of an untyped sum.

Suppose the fixed multiplier has a specified decomposition

    K=sum_(j=0)^J K_j(B)*R^j,

where the K_j(T) are fixed integer polynomials, J>0, and K_J is not the
zero polynomial. Require the guard condition

    max(E)+J<L.                                          (2)

Thus multiplication by K never wraps an occupied inner position into the
next cell. Horizontal shifts from the powers of B in K_j are permitted.
Put P(T)=K_J(T), and let D be its exponent span: its largest exponent
minus its smallest exponent with nonzero coefficient. D can be0.

Represent the fixed right-hand numeral as
lambda=sum_(e=0)^(L-1) lambda_e R^e, with fixed integer coefficients
lambda_e. After reducing ordinary cell shifts cyclically, require that
the coefficient residuals

    c_(i,e)=sum_(j=0)^J [K_j(S)u_(e-j)]_i
              +[S^h u_e]_i-u_(i,e)-lambda_e              (3)

satisfy |c_(i,e)|<=R-2. Here S cyclically shifts cells by one, and a
missing inner column is identically zero. This is the explicit sufficient
no-carry hypothesis; a compiler must prove it from its actual typed
digits and fixed coefficients. Unselected coefficient positions are
included in (3), rather than discarded as irrelevant garbage.

Equation(1) implies every residual in(3) is zero. Indeed their base-R
weighted sum is0 modulo R^(LN)-1 and has absolute value strictly less
than R^(LN)-1. It is therefore zero as an integer. Its units coefficient
is a multiple of R with absolute value less than R, so it is0. Divide
by R and repeat. This argument also checks the cyclic wrap quotient;
it does not assume that a congruence is an equality of individual digits.
The bound R-2 is intentional: R-1 at every position would be a nonzero
residual vector representing q-1.

## 2. The fixed period bound

Let k=|E|. Every word satisfying the preceding hypotheses and(1) has a
common period p for all its columns, where

    p divides N and p<=M^(D*k).                          (4)

If P is a monomial, D=0 and every column is constant across all cells.

Order the allowed positions from highest to lowest. For the highest e,
look at equation(3) at position e+J. The J-term is P(S)u_e. Every
j<J term uses position e+J-j>e, hence is zero at this first stage.
Also e+J>e, so the temporal difference at that position is zero. Thus

    P(S)u_e=constant.

At a later stage, the same equation is

    P(S)u_e=v,                                          (5)

where v is determined by higher columns already considered, their fixed
horizontal shifts, their temporal shifts by h, and a constant. If these
higher columns have common period p dividing N, then v has period p,
independently of h. This is the step at which a temporal shift of an
already periodic column cannot introduce an arbitrary new row.

Factor a monomial from P and shift the forcing accordingly. Its two
extreme coefficients are nonzero, and its degree is D. For D>0, (5)
determines the next digit uniquely from its previous D digits and the
phase modulo p: solve using the nonzero extreme coefficient. The result
may be nonintegral or outside A_e, in which case that state is forbidden.
There are at most p*M^D states. A cyclic solution lies on a deterministic
cycle, whose length ell is at most p*M^D, is a multiple of p because
the phase is included, and divides N. This ell is a common period of
the old columns and the newly added one. For D=0, the new column is
uniquely determined by its forcing and retains period p.

Start with p=1 above the top column and descend through k columns.
Each step multiplies the bound by at most M^D, proving(4). Keeping the
phase and the divisibility p|N is necessary; the proof does not incorrectly
assert that a lower column under periodic forcing has period at most M^D
by itself.

## 3. Consequence for a computation compiler

Any property of an individual encoded cell repeats with the common period
p. In particular, if a valid encoding requires a Start cell at exactly one
of the N positions, then p=N and

    N<=M^(D*k).

Thus a fixed guarded layout of this form cannot supply accepting diagrams
with a unique Start and unbounded length. If it also uses the established
raw marker bridge W=2^b*B^(2x)<q, then 2x<N and its admitted ordinary
inputs are bounded as well.

The conclusion concerns genuine guards and a coefficientwise equation.
To escape it, a proposed single-field compiler must change a hypothesis:
for example prove that carries implement additional state, or allow a
cycle of within-cell dependencies that violates(2). Merely adding more
unselected coefficient positions with finite typed alphabets does not
help: they become further columns in the same descending argument.
Likewise a proof that only the desired coefficient bands are correct is
insufficient; (1) constrains all bands.

## 4. Evidence

The [checker](native_controller_single_field_guard.py) exhausts bounded
binary-column words for several fixed multipliers, including horizontal
polynomials of exponent span0,1,2 and signed coefficients. It compares the
actual modular integer equation against all coefficient equations, checks
the explicit residual bounds, and verifies the claimed common-period
bound for every admitted tuple. A separate recurrence audit tests periodic
forcing and confirms the phase-inclusive period estimate. These finite
tests corroborate the proof; they do not decide the remaining general
one-field compiler question.

The [receipt](native_controller_single_field_guard.json) is compared by
default. Independent full proof, source, and default-replay review passed.
No universal operation bound
is improved by this obstruction.
