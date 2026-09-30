# The strong auxiliary unit lowers the 89-operation polynomial to degree162

The [eight-factor universal polynomial](complete75_norm_product89.md) can
be changed at one multiplication gate to lower its exact degree from166
to **162**, retaining **89=48M+41A operations and19 positive witnesses**.
The two polynomials have exactly the same integer zero set, even before
restricting the supplied coordinates to be positive. Thus the full
ordinary-input universality theorem and fixed compiler numerals carry over.
The best comparison-certificate bound remains75.

The [reversed auxiliary successor](complete75_reversed_auxiliary89.md)
also changes the auxiliary root and linear-unit sign, attaining degree160
at the same89 operations. Its proof preserves positive solution sets;
the single substitution here has the stronger integer-zero-set
equivalence established below.

This is a degree improvement, not an operation-count improvement. It uses
the already computed strong auxiliary expression in one more place; no
equation or positivity condition is deleted.

## 1. The replacement

Use every definition, coordinate and fixed constant from89. In particular

    A=a+2, Delta=A^2-1,
    c=(eta+zeta)Y+eta, T=i*c^2, U=jc-R,
    K=Delta*(f^2-1), N4=1+T^2-K.

The old auxiliary factor is

    N3=T^2*(U^2-y^2)+y^2.

Replace only this factor by

    N3_new=K*(U^2-y^2)+y^2.                         (1)

Keep N0,N1,N2,Nk,Nt,N4,Nl unchanged. The output is

    P162=N0*N1*N2*N3_new*Nk*Nt*N4*Nl-1.             (2)

The literal source changes register `L17` from
`ic22*aux_square_gap` to `R16*aux_square_gap`. Here `ic22=T^2` and
`R16=K` are both already paid: the strong factor still uses both of them.
Reordering the acyclic schedule to make K available earlier introduces
no operation or supplied coordinate.

## 2. Exact integer zero-set equivalence

For arbitrary integers A,T,f, the value N4 cannot equal-1. Such an
equality would require

    T^2+2=(A^2-1)(f^2-1).

Modulo4 the right side is0 or1, since each factor is0 or3. The left
side is2 or3. Hence there is no integer solution. This argument has
no positivity, index, packing or kernel hypothesis.

At any integer zero of either the old or new product polynomial,
each of its eight factors is an integer unit. Its unchanged factor
N4 is therefore1, so T^2=K. Equation(1) then gives N3_new=N3 and the
two entire product values coincide. This proves both implications:

    P162=0 if and only if P89=0                     (3)

on every integer assignment. Restricting to the same19 strictly positive
witnesses preserves that equivalence. The old proof now recovers all
other equations, the positive old transport quotient, the original
compiler coordinates and the same accepted ordinary input x. Conversely
every canonical old positive compiler solution gives the new zero with
no coordinate change.

The modified factor also has its own unconditional negative-unit
obstruction: K is0 or1 modulo4, and

    N3_new=K*U^2+(1-K)*y^2

is congruent respectively to y^2 or U^2. It cannot be-1. This observation
is compatible with the ordered proof above; it does not assert that
T^2=K on arbitrary assignments away from the zero set.

In general, if a product factor `1+r` cannot be-1 over the integer
domain, then the equation that the whole product equals1 forces r=0.
Other factors may be replaced by polynomials congruent modulo r. The
equivalence must be checked in both directions with that forcing factor
retained. Here the replacement is particularly cheap because K is an
existing register.

## 3. Off-zero identities and arithmetic ledger

Write Q=T^2-K and H=U^2-y^2. The exact polynomial identity is

    N3_new=N3-QH,
    P162-P89=-QH*(N0*N1*N2*Nk*Nt*N4*Nl).             (4)

This does not claim equality of the polynomials away from the zero set.
With the original nineteen residuals r_i and coordinate substitutions
from89, Q=r12 and N3=1+r13. Consequently the full source computes

    (1-r5)(1+r11)(1+r17)(1+r13-r12*(U^2-y^2))
      *(1+r8)(1+r2)(1+r12)(1+r14)-1.                (5)

No new operation is needed for the proof expression r12*(U^2-y^2);
the actual source evaluates(1), not the expanded identity(5).

The unchanged ledger is

    certificate:88=48M+40A, one equation,
    polynomial:89=48M+41A,19 positive witnesses.     (6)

Every binary arithmetic operation, including multiplication by a fixed
numeral, remains charged. The [source](complete75_strong_reduction89.py)
and [receipt](complete75_strong_reduction89.json) include the reordered
full DAG and verify that exactly one register definition changed.

## 4. Exact degree

Give the input x and all supplied witnesses degree one. Put

    Qtop=(B-1)J, ktop=eta+zeta, Gtop=rho+sigma,
    Ctop=Qtop-F-Z-alpha-2d*x.

The top of Delta is `w^2*s^2*Qtop^12`, so K has degree18 and top
`f^2*w^2*s^2*Qtop^12`. The unchanged U has degree6 and top
`j*ktop*s*Qtop^3`. Therefore N3_new has exact degree30 and top

    f^2*j^2*ktop^2*w^2*s^4*Qtop^18.                 (7)

The competing terms -K*y^2 and y^2 have degree at most20. The eight factor degrees
are now26,22,42,30,9,5,22,6. Their sum is162, and multiplying their
nonzero highest forms gives

    -32*(B-1)^105*h*Gtop*delta^2*i^2*f^2*j^3
       *ktop^10*w^13*s^22*J^105*Ctop.               (8)

This is nonzero for every admissible B>1: Ctop has coefficient-1 on F.
Hence the degree is exactly162, not merely an upper bound.

## 5. Verification and scope

Default execution recomputes and compares the adjacent receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_strong_reduction89.py

The checker audits the one changed multiplication, the entire count,
512 original-source identities(5), independent factor formulas and the
full difference identity(4). Cases include signed supplied assignments,
zero restored old quotients, and negative computed input roots despite
positive supplied coordinates. Signed cases verify algebraic identities;
the universal representation retains the stated positive domain.

Three weighted and offset univariate specializations check all eight
factor degrees and the coefficient(8). The factor-difference identity
is also checked symbolically. All64 residues for the N4 obstruction
and256 residues for the modified N3 obstruction are checked exactly.
The proofs of(3) and the degree formula are parametric; the finite
checks support the implementation and do not replace those proofs.

An independent final proof/source/default review passed without findings.
It also checked256 signed full-polynomial difference identities using
direct K,T,U formulas, the89-operation histogram, and a separate weighted,
offset degree162 specialization at B=128,d=7 with the coefficient(8).
A second independent proof/source/default review also passed, with512
original19 corrected-product identities, including four negative computed
mu values and175 zero restored quotients, and three weighted, offset
degree162 leading-form checks.

No real-zero equivalence, global arithmetic optimum, or proof-assistant
formalization is claimed.
