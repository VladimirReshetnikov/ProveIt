# Positive first-root coordinates give94/84,93/118 and92/122

The fixed complete75 compiler has the following three single-polynomial
representations, each with **19 strictly positive existential witnesses**:

| Polynomial operations | Multiplications | Additions/subtractions | Exact degree | Certificate operations | Equations |
|---:|---:|---:|---:|---:|---:|
| **94** |48|46|**84**|80|5|
| **93** |48|45|**118**|79|5|
| **92** |48|44|**122**|81|4|

The94-operation result improves the preceding96-operation bound at
degree84. The93 and92 results improve the respective degrees128 and136
of the [earlier auxiliary degree tradeoffs](complete75_auxiliary_degree_tradeoffs.md).
At those two operation totals, one multiplication becomes an addition.
The construction applies the [positive first-root coordinate](complete75_positive_root89.md)
to those retained-auxiliary sources and chooses new groups of unit factors.
The change of root is a bijection of positive solution sets, rather than
an assertion that the polynomials agree at unchanged witness coordinates.
The fixed compiler numerals, ordinary positive input and complete
comparison-certificate bound75 are unchanged.

## 1. Definitions and the positive coordinate change

For93 use the positive source coordinates of
[norm product91](complete75_norm_product91.md); for94 and92 use those of
[norm product90](complete75_norm_product90.md). Replace only the supplied
positive first root tau with a positive coordinate g, named `tau_gap` in
source. The former quotient is z for93 and zplus for94 and92. There are nineteen
supplied positive coordinates in each case.

Keep all paid definitions of the appropriate parent, in particular

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, Delta=A^2-1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    kappa=2d*x+b+delta*Delta, mu=W+a*kappa+rho*H.

The masks and definitions of C,W,R are those of the corresponding parent.
Both eta and zeta remain strictly positive supplied witnesses, retaining
both sides of the main ratio bound. No new assumption on a computed
coordinate is imposed.

Put V0=XY^2, and replace the old first factor by

    N0new=g^2+(E*kY)*(2g-k).                          (1)

For every integer assignment, reconstructing

    tau_old=V0*k+g                                   (2)

gives the exact identity

    tau_old^2-(E^2+X)(kY)^2
      =(V0*k+g)^2-V0*(V0+1)*k^2
      =g^2+V0*k*(2g-k).                              (3)

For positive supplied coordinates, V0,k,g are positive, so(2) is positive
without using any equations. Conversely, in every positive91 or90
solution the old first factor equals1. Thus

    tau_old^2-(V0*k)^2=V0*k^2+1>0.

Since tau_old and V0*k are positive, g=tau_old-V0*k is strictly positive.
Equations(2) and this inverse give a bijection on the full positive
solution sets, with every other supplied coordinate unchanged. The old
root occurs only in the first factor. The signed intermediate 2g-k is
allowed: it is a computed expression, not a positive witness.

## 2. The retained auxiliary equations and factors

Use the already computed expressions

    T=i*c^2, U=jc-R, V=of-c, K=Delta*(f^2-1),
    Qs=T^2-K, Ql=U-V.                                (4)

Both Qs=0 and Ql=0 remain separate equations. In particular, the actual
strong square (ic^2)^2 is still computed and compared with K.

The other factors are

    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3new=K*(V^2-y^2)+y^2,
    Nk=k-R-hE.                                       (5)

Compared with the old auxiliary factor N3=T^2*(U^2-y^2)+y^2, the exact
identity valid on every integer assignment is

    N3new-N3=-Qs*(V^2-y^2)-T^2*Ql*(U+V).              (6)

Hence the old and new factors coincide on the two retained equations.
No sign of U or V is used in(6). The integer N3new also cannot equal-1
unconditionally: K is0 or1 modulo4, so N3new is congruent to y^2 or V^2.
This observation does not remove either retained equation.

For93 the transport residual is

    Qt=(DC+B*DR+X)C-F-z(q-1).                         (7)

For94 and92 use the shifted quotient and transport factor

    Nt=(DC+B*DR+X)C+(q-F)-zplus*(q-1).                (8)

These definitions retain their fixed input and mask numerals exactly.

## 3. Complete positive-witness equivalences

The93 polynomial is the sum of squares of the five residuals

    Qt, Qs, Ql, N0new*N2-1, N1*N3new*Nk-1.            (9)

At a positive integer zero, all five residuals vanish. Equation(2)
restores a positive old root, and(3),(6) identify the old first and
auxiliary factors. Multiplication of the two group equations gives
`N0*N1*N2*N3*Nk=1`. Along with Qt=Qs=Ql=0, these are precisely the
four equations of91. Its complete theorem restores every earlier
positive coordinate and the same ordinary input. Conversely, every
positive91 solution has all five factors equal1, so the positive inverse
coordinate g and identity(6) make every residual(9) zero.

The92 polynomial is the sum of squares of the four residuals

    Qs, Ql, N0new*N2*Nt-1, N1*N3new*Nk-1.             (10)

At a positive integer zero, use(2),(3),(6) again. Multiplication gives
`N0*N1*N2*N3*Nk*Nt=1`, which together with Qs=Ql=0 is exactly the90
source. Its established conditional sign and index proof applies:
weak transport gives C>=0 and the packing bounds; strong auxiliary and
linear equations permit index recovery; the negative index branch is
excluded; and z=zplus-1 is restored strictly positive. This argument
does not assume that Nk or Nt excludes-1 independently. Conversely,
every positive90 solution has all six factors equal1 and both retained
auxiliary equations, and its positive inverse g verifies(10).

The94 polynomial keeps the same six factors and two retained auxiliary
residuals as92, but uses three groups. Its five squared residuals are

    Qs, Ql, N0new*N1-1, N2-1, N3new*Nk*Nt-1.         (10a)

At a zero, multiplying the three group equations gives exactly the same
six-factor product used in the92 proof. Reconstruction(2) and correction(6)
therefore restore the90 source in the same order. Conversely, every
positive90 solution has all six factors equal1 and gives every residual(10a)
zero under its positive inverse coordinate. The possible negative unit
signs of Nk and Nt are resolved by the complete90 theorem; this grouping
does not assume their individual sign exclusion for free.

Thus each new polynomial's positive solutions are in bijection with the
entire positive solution set of its corresponding complete parent.
All fixed-compiler completeness, low-dummy alignment, ordinary-input
coverage and strict positive-domain requirements are inherited. No
finite fixture is used as a substitute for either implication.

## 4. Literal schedules and exact counts

The [checker](complete75_positive_root_degree_tradeoffs.py) builds the
appropriate parent partition schedule and applies the same two
auxiliary gate changes as the historical degree-tradeoff packet:

| Register | Old instruction | New instruction |
|---|---|---|
| `H2` | `H17*H17` | `aux_u_rhs*aux_u_rhs` |
| `L17` | `ic22*aux_square_gap` | `R16*aux_square_gap` |

These two changes preserve the operation types and both retained
comparisons. It then makes the following six-gate replacement, with
UM=E, ksn2=kY and R10b=k:

| Old first-factor block:4M+2A | New first-factor block:3M+3A |
|---|---|
| `tau_square=tau*tau` | `tau_square=tau_gap*tau_gap` |
| `UM2=UM*UM` | `first_root_base=UM*ksn2` |
| `scaled_norm_coefficient=UM2+wn2` | `twice_tau_gap=tau_gap+tau_gap` |
| `ratio_product2=ksn2*ksn2` | `first_signed_gap=twice_tau_gap-R10b` |
| `L9=scaled_norm_coefficient*ratio_product2` | `first_cross=first_root_base*first_signed_gap` |
| `norm_first=tau_square-L9` | `norm_first=tau_square+first_cross` |

The old root in(2) is a proof reconstruction; the new polynomial does not
need to evaluate it as an extra gate. All new gate dependencies are
ordered explicitly and every register is checked. No derived expression
is introduced as an uncounted witness.

The93 factor definitions cost76=40M+36A; the two groups require three
products. The94 and92 factor definitions cost77=40M+37A; their three and two groups
require respectively three and four products. The complete ledgers are

    94 certificate:80=43M+37A, five equations;
    94 polynomial:80+5 residuals+5 squares+4 sums
                 =94=48M+46A.                       (11a)

    93 certificate:79=43M+36A, five equations;
    93 polynomial:79+5 residuals+5 squares+4 sums
                 =93=48M+45A.                       (11)

    92 certificate:81=44M+37A, four equations;
    92 polynomial:81+4 residuals+4 squares+3 sums
                 =92=48M+44A.                       (12)

Binary additions, subtractions, squares and multiplications by fixed
numerals are all charged. The [receipt](complete75_positive_root_degree_tradeoffs.json)
contains the full polynomial schedules and comparison lists. The final
polynomials have no hidden residual constraints.

## 5. Exact degrees and highest forms

Give x and each new supplied witness degree one; fixed numerals have
degree zero. Set Q=(B-1)J, k0=eta+zeta, gamma0=rho+sigma and

    Ctop=Q-F-Z-alpha-2d*x.

The highest forms of the factors in order are

| Factor | Degree | Highest homogeneous form |
|---|---:|---|
| N0new |14| `w*s^2*k0*Q^9*(2g-k0)` |
| N1 |22| `8*gamma0*k0*w^2*s^3*Q^15` |
| N2 |42| `-4*delta^2*w^5*s^5*Q^30` |
| N3new |28| `f^2*k0^2*w^2*s^4*Q^18` |
| Nk |9| `-h*w*s*Q^6` |
| Nt |5| `w*Q^3*Ctop` |

For94, the group degrees are36,42,42. The separate strong and linear
residuals have degrees22 and6. The highest polynomial form is the sum
`N2_top^2+(N3new_top*Nk_top*Nt_top)^2`, explicitly

    16*delta^4*w^10*s^10*Q^60
      +h^2*f^4*k0^4*w^8*s^10*Q^54*Ctop^2.            (12a)

It cannot vanish as a polynomial: the first term contains delta^4 and
the second contains no delta. This proves exact degree84. Every partition
contains the degree42 factor N2 in some group; no grouping of these
factors can have largest group degree below42. This construction attains
that bound, also checked by enumeration of all65 three-group partitions.

For93, the group degrees are56 and59. The three separate residuals Qt,
Qs,Ql have degrees5,22,6, so the unique highest contribution to the
polynomial is `(N1_top*N3new_top*Nk_top)^2`, namely

    64*(B-1)^78*h^2*(rho+sigma)^2*f^4*(eta+zeta)^6
      *w^10*s^16*J^78.                               (13)

This is nonzero for each admissible fixed B, proving exact degree118.

For92, the group degrees are61 and59. The residual degrees22 and6 are
smaller; the unique highest contribution is
`(N0new_top*N2_top*Nt_top)^2`, namely

    16*(B-1)^84*delta^4*(eta+zeta)^2*w^14*s^14*J^84
      *Ctop^2*(2g-eta-zeta)^2.                       (14)

Neither Ctop nor 2g-eta-zeta is the zero polynomial (their F and g
coefficients are-1 and2). Thus(14) is nonzero, proving exact degree122.

The checker enumerates all15 two-group partitions of the five factor
degrees14,22,42,28,9 and all31 of the six factor degrees14,22,42,28,9,5.
The minimum largest group degrees are respectively59 and61, attained
by(9),(10). These finite bounds and the94 bound concern only partitioning these
particular factors in the stated literal product-and-squares circuit;
no global arithmetic or degree optimum is claimed.

## 6. Verification and scope

Default execution recomputes and compares the deterministic receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_root_degree_tradeoffs.py

The checker verifies(6) symbolically and reuses the symbolic identity(3)
and384 positive component Pell-coordinate bijection fixtures. Per new
construction, it evaluates512 assignments:384 with positive supplied
coordinates and128 with signed supplied coordinates. It reconstructs
tau_old independently as XY^2k+g, compares the full old-coordinate
polynomial with the new one, and independently evaluates all original
nineteen source residuals. Those residuals give corrected auxiliary
factors through(6), from which it reconstructs the complete new grouped
sum of squares. The audits include negative computed C,R,mu and four
deliberately negative input-root cases per construction. These are
algebraic identity checks, not asserted accepting compiler witnesses.

Three weighted and offset univariate specializations per construction
check all factor degrees and highest coefficients, the complete
polynomial degree, and the explicit forms(12a),(13),(14). Register, comparison,
count and all two- and three-group partition audits are recorded separately.
The proof above supplies the unbounded positive-domain result.

The degree reduction changes the first-root coordinate. The auxiliary
factor changes away from Qs=Ql=0, and these two full equations remain
present and paid. No real-witness equivalence or proof-assistant
formalization is claimed. The historical93/128 and92/136 files are kept
unchanged as the preceding constructions.

An independent proof/source review also passed all three constructions.
Supplemental checks covered384 direct-factor identities across four
compiler bases, an additional weighted degree/top specialization for each
variant, and the restricted partition minima42,59,61.
