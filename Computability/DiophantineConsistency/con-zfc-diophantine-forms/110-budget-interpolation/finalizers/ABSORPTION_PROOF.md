# Bounded-guard absorption: 15 integers, degree 176, 125 operations

## Result and scope

`absorbed15_degree176.json` and its literal arithmetic DAG define one fixed
integer polynomial in the same fifteen unrestricted integer variables as the
incoming `parity15_unit_product.json`. Its exact total degree is 176 and its
live binary arithmetic count is 125 (24 additions, 29 subtractions, 72
multiplications). The incoming comparison is degree 204 and 128 operations.
No extra quantified coordinate, hidden inequality, or finalizer is present.

The new equation has an integer zero if and only if the retained incoming
17-integer calibrated parent has an integer zero. Composing with that parent's
identified ordinary native/Pell/refutation theorem gives the same ordinary
ZFC-provable equivalence between nonsolvability and syntactic Con(ZFC).
This does not prove consistency, assert a worldwide optimum, or provide a new
end-to-end proof-assistant certificate.

## 1. A universal upper bound on the positivity certificate

Use the exact incoming abbreviations. Set

    a0 = cone_A*F, b0 = cone_B*C,
    G = a0*b0 - (q-a0-b0)^2,
    Z = eta*(k-eta),
    B = G*Z - (t^2-G-Z+1)^2 - 1 - p1^2 - p2^2.

All variables here are real for the inequality, so no previous Pell residual
or positivity assumption is being used. Direct completion of squares gives

    4(q^2-3G) = (3(a0+b0)-4q)^2 + 3(a0-b0)^2,
    4Z = k^2 - (2eta-k)^2.

Thus G <= q^2/3 and Z <= k^2/4. If G and Z are nonnegative,
GZ-(t^2-G-Z+1)^2 <= GZ <= q^2*k^2/12.
If GZ <= 0, the same conclusion holds because the left side is nonpositive.
In the remaining case both G and Z are negative. Write G=-g, Z=-z with
positive g,z. Then t^2-G-Z+1 >= g+z+1, and its square exceeds gz.
Again the left side is negative. Consequently, universally,

    B <= q^2*k^2/12 - 1.                                  (1)

This upper bound is much smaller in degree than the guard's unrestricted
absolute value: the latter has a negative square of degree 44.

## 2. Absorb the two retained residuals

Let

    r_main = D^2 - Delta*c^2 - 1,
    r_strong = I^2 - Delta*(f^2-1),
    S = r_main^2 + r_strong^2,
    B_abs = B - q^2*k^2*S,
    B_guard = 4B_abs+1.                                    (2)

For integer inputs, if B_guard is an integer square, its congruence 1 modulo
4 makes it at least 1, and hence B_abs >= 0. If qk=0, (1) makes this
impossible. If S>=1, (1) gives

    B_abs <= q^2*k^2(1/12-S)-1 < 0,

also impossible. Thus squarehood of B_guard alone forces S=0, so both retained
Pell residuals vanish. Once they vanish, B_abs=B and the original positivity
square certificate is unchanged. No separate unit product or sum of squares
is required.

## 3. The parity norm still forces the square certificate

Keep the incoming definitions

    A = 4A4+1,
    Q = I^2, delta=Q-1, r_aux=QV^2-1, Caux=delta*r_aux,
    x=2t_parity+1,
    U=t_parity(t_parity+1)-A4-B_guard+4Caux,
    M=U^2+4x^2*Caux-A*B_guard,
    N=M^2-16x^2*U^2*Caux.                                 (3)

The exact polynomial identity is

    256N = product over all eight signs of
           (x +/- sqrt(A) +/- 2sqrt(B_guard) +/- 4sqrt(Caux)).

Its algebra is unchanged by substituting the modified B_guard in (2).
If N=0, a signed root sum is rational. Both A and B_guard are odd and hence
nonzero. In a nonrational squareclass containing the A term, its odd square
coefficient cannot cancel the even coefficients of the other terms. In a
class containing B_guard but not A, its coefficient is twice an odd integer,
which cannot cancel the multiple of four from Caux. A class containing only
Caux cannot cancel unless its radical is zero. Thus A and B_guard are positive
integer squares, and Caux is a nonnegative integer square.

Importantly this argument explicitly permits Caux=0: omit the zero radical.
This removes a potential circularity. One does not invoke the retained strong
row to establish Caux nonzero before deriving S=0. The incoming statement's
nonzero hypothesis on Caux was unnecessary for its squareclass argument.

By Section 2, the square B_guard first forces r_main=r_strong=0. The incoming
unconditional scale bound then gives Delta>1 and the strong row excludes Q=1;
therefore delta!=0. The incoming adjacent-coefficient Pell descent applies to
e^2=Caux and proves y=e/delta integral when Q>1. For Q=0 it is immediate.
Restore the original coordinates by

    tau=2sqrt(A)-2P+k,
    y_gap=y-V,
    pair_pos3=(sqrt(B_guard)-1)/2.

Signs of roots may be chosen independently. Each restored coordinate is an
integer, and all five parent residuals vanish. This proves soundness.

Conversely, any parent zero has r_main=r_strong=0, so the modification in
(2) vanishes. The incoming parent-to-parity construction supplies integral
roots u,d,e of A,B_guard,Caux and sets

    t_parity=(u+2d+4e-1)/2.

The numerator is even because u and d are odd, and (3) vanishes. This proves
completeness using every parent zero, not merely canonical witnesses.

## 4. Exact degree and circuit

The old residual degrees are 14 and 14, so deg(S)=28. The scale q^2*k^2
has degree 16. Therefore the added penalty has degree 44, exactly the old
positivity radicand's degree. The norm degree upper bound remains 176.
Using the authentic six fixed coefficient payloads and the explicit line
listed in `ABSORPTION_METRICS.json`, the degree-176 coefficient is
179645231 modulo 1000000007, nonzero. Together with the upper bound this
proves exact total degree 176 after the coefficient ports are specialized.

The DAG contains only topologically ordered add, sub, and mul gates. Fixed
numeral leaves and register reuse are free; squaring and scalar multiplication
are charged. The count is 125, with all 15 inputs explicitly listed.
`build_absorption.py` reconstructs the packet, DAG, and degree certificate;
`check_absorption.py` independently checks syntax, liveness, the specialized
leading coefficient by finite differences, guard inequalities on finite test
sets, and zero/negative-radicand diagnostics. The inequalities and squareclass
argument above, not finite sampling, establish the universal theorem.

## 5. Provenance

The mathematical and literal source is the incoming archive
`docs/incoming/con-zfc-parity-norms-2026-10-23.zip` from the ProveIt tree
reviewed at commit 7e533c33819ee1f703b69f2778a767cdc069940d. The copied package's
own internal source pin is cfbf118b4ad9b2c651fe96b571d9415261766328. Its parent,
coefficient binding, ordinary calibration, license, and complete restoration
proofs are retained unchanged under `source/con-zfc-parity-norms-2026-10-23/`.
Only the bounded-guard substitution (2) and removal of the finalizer are new.
