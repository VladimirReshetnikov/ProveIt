# Lower-degree universal polynomials at93 and92 operations

The fixed complete75 compiler has two further explicit single-polynomial
representations, each with **19 strictly positive existential witnesses**:

| Polynomial operations | Multiplications | Additions/subtractions | Exact degree | Certificate operations | Equations |
|---:|---:|---:|---:|---:|---:|
| **93** |49|44|**128**|79|5|
| **92** |49|43|**136**|81|4|

These lower the degrees of the earlier93/136 and92/138 constructions.
Both the full strong auxiliary square and its linear auxiliary equation
remain separate comparisons. Using their already computed right sides
inside the auxiliary factor lowers that factor's degree without adding
arithmetic. A new grouping of the unit factors gives the stated results.
The fixed compiler numerals, ordinary positive input and complete
comparison-certificate bound75 are unchanged.

## 1. Source definitions and the two unchanged auxiliary comparisons

The93 construction uses the positive coordinates and paid definitions of
[norm product91](complete75_norm_product91.md); the92 construction uses
[norm product90](complete75_norm_product90.md). Their only coordinate
difference is the positive old quotient z versus the positive shifted
quotient zplus. In either case there are19 supplied positive coordinates,
and all derived expressions are substituted into the circuit.

Keep their notation

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    A=a+2, H=4a+3, Delta=A^2-1,
    D=X+ac+(rho+sigma)H,
    kappa=2d*x+b+delta*Delta, mu=W+a*kappa+rho*H.

The definitions of C,W,R, all masks and the fixed numerals remain exactly
those of the respective parent source. Define the following abbreviations
for already paid registers:

    T=i*c^2, U=jc-R, V=of-c,
    K=Delta*(f^2-1),
    Qs=T^2-K, Ql=U-V.                                 (1)

In both constructions **Qs=0 and Ql=0 are retained**. The actual strong
square T^2=(ic^2)^2 is still computed and compared with K. These equations
have not been weakened or replaced by an informal sign assumption.

The old auxiliary unit factor was

    N3=T^2*(U^2-y^2)+y^2.

Use instead

    N3new=K*(V^2-y^2)+y^2.                            (2)

The exact polynomial correction, valid on every assignment, is

    N3new-N3=-Qs*(V^2-y^2)-T^2*Ql*(U+V).              (3)

Consequently N3new=N3 wherever the two retained auxiliary comparisons
hold. No positivity of U or V is assumed to prove this identity.

There is also an unconditional integer sign observation: K is0 or1
modulo4, because each of A^2-1 and f^2-1 is0 or3 modulo4. Thus N3new
is congruent to y^2 or V^2 modulo4 and cannot equal-1. This observation
does not remove either comparison in(1), which is still needed for the
equivalence with the complete source used here.

## 2. The93-operation construction

Use the five factor definitions from91, except for(2):

    N0=tau^2-(E^2+X)(kY)^2,
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3new=K*(V^2-y^2)+y^2,
    Nk=k-R-hE.

Write the unchanged transport residual as

    Qt=(DC+B*DR+X)C-F-z(q-1).

The five comparison equations are

    Qt=0, Qs=0, Ql=0,
    N1*N2=1, N0*N3new*Nk=1.                           (4)

The polynomial is the sum of their five squared residuals.

Suppose positive supplied coordinates make this polynomial zero. Then
every equation(4) holds. By(3), the auxiliary factor equals the old N3.
Multiplying the two group equations gives
`N0*N1*N2*N3*Nk=1`. Together with Qt=Qs=Ql=0, these are precisely
the four equations of91. Its soundness theorem restores all preceding
complete75 coordinates with their required positive domains and accepts
the same ordinary input.

Conversely every positive91 solution has Qt=Qs=Ql=0 and all five
old factors equal1. Equation(3) gives N3new=1, so every equation(4)
holds. Thus this transformation preserves the **entire positive solution
set of91** on the same nineteen coordinates. Its canonical compiler
completeness and dummy-alignment proof are inherited unchanged.

## 3. The92-operation construction

Keep the shifted quotient zplus and transport factor of90:

    Nt=(DC+B*DR+X)C+(q-F)-zplus*(q-1).

The four comparison equations are

    Qs=0, Ql=0,
    N0*N2=1, N1*N3new*Nk*Nt=1.                        (5)

Again take the sum of squared residuals. At a positive integer zero,
(3) restores the old auxiliary factor. Multiplying the two group
equations gives `N0*N1*N2*N3*Nk*Nt=1`, which, together with the first
two equations, is exactly the90 source.

The complete90 proof therefore applies in its established order: the
weak transport unit gives C>=0 and the packing bounds, the unchanged
strong auxiliary equations permit exact index recovery, the negative
index branch is excluded, and the old quotient z=zplus-1 is restored
strictly positive. No new claim that Nk or Nt excludes-1 independently
is needed for this grouping; both are in the second group.

Conversely every positive90 solution has all six old factors equal1
and Qs=Ql=0. Equation(3) then verifies(5). This gives the identical
positive solution set of90 on its nineteen retained coordinates.
In particular the ordinary input and fixed compiler constants are
unchanged in both directions.

## 4. Exact literal operation counts

The [checker](complete75_auxiliary_degree_tradeoffs.py) generates each
parent partition source and changes exactly two gates:

| Register | Old instruction | New instruction |
|---|---|---|
| `H2` | `H17*H17` | `aux_u_rhs*aux_u_rhs` |
| `L17` | `ic22*aux_square_gap` | `R16*aux_square_gap` |

Here H17=U, aux_u_rhs=V, ic22=T^2 and R16=K. The source is reordered
topologically; no arithmetic is added or deleted by these two changes.
Both strong and linear comparisons remain literally present. No derived
coordinate is introduced as an uncounted witness.

For93, the five ungrouped factors cost76=41M+35A, and the two groups
in(4) require three products. Hence

    certificate=79=44M+35A, five equations;
    polynomial=79+5 residuals+5 squares+4 sums
              =93=49M+44A.                           (6)

For92, the six ungrouped factors cost77=41M+36A, and the two groups
in(5) require four products. Hence

    certificate=81=45M+36A, four equations;
    polynomial=81+4 residuals+4 squares+3 sums
              =92=49M+43A.                           (7)

All binary additions, subtractions and multiplications are charged,
including multiplication by a fixed numeral. The
[receipt](complete75_auxiliary_degree_tradeoffs.json) records each
complete polynomial DAG, comparison list and output register. There
are no external residual conditions on the final polynomial.

## 5. Exact degrees and leading forms

Give the ordinary input x and all nineteen witnesses degree one, and
the fixed compiler numerals degree zero. Put Q=(B-1)J, k0=eta+zeta
and gamma0=rho+sigma. The unchanged five-factor leading forms are
listed in91. The change here is

    N3new_top=f^2*k0^2*w^2*s^4*Q^18, degree28.         (8)

Indeed K=Delta*(f^2-1) has degree18 with highest form
`w^2*s^2*f^2*Q^12`. The root V=of-c has degree5 with highest form
`-k0*s*Q^3`; its square dominates y^2. Their product gives(8).
The factor degrees in order N0,N1,N2,N3new,Nk,Nt are therefore

    26,22,42,28,9,5.                                  (9)

For93 omit Nt. The two group degrees are64 and63, while the remaining
transport, strong and linear residuals have degrees5,22 and6. Thus
the unique highest contribution is `(N1_top*N2_top)^2`, namely

    1024*(B-1)^90*delta^4*w^14*s^16*J^90
      *(eta+zeta)^2*(rho+sigma)^2.                    (10)

It is nonzero for every admissible fixed B, proving exact degree128.
The five factor degrees sum to127, so no two-group partition can have
largest group degree below64. This grouping attains that bound.

For92, the group degrees are68 and64. The other residual degrees22
and6 are smaller. The unique highest contribution is
`(N0_top*N2_top)^2`, namely

    16*(B-1)^96*delta^4*w^14*s^18*J^96
      *(eta+zeta)^4.                                  (11)

This is nonzero, proving exact degree136. Enumeration of all31
two-group partitions of the six factors confirms that the minimum
largest group degree is68. These optimality statements concern only
these particular factors and two-group product-and-squares circuits.
They are not lower bounds for other equivalent polynomial encodings.

## 6. Verification and limits

Default execution recomputes and compares the complete deterministic
receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_auxiliary_degree_tradeoffs.py

The checker verifies(3) symbolically, audits both local gate changes,
register availability, unchanged comparison lists and operation counts.
For each construction it restores the original nineteen-equation source
on256 arbitrary positive supplied assignments across several bases.
Its old auxiliary factor `1+r13` is corrected using the original strong
and linear residuals r12,r14 exactly as in(3). It then checks the entire
new grouped polynomial against those independent original-source values.
These assignments include negative computed C,R and four deliberately
negative computed input roots per construction. They are polynomial
identity checks, not claims of full accepting witnesses.

Three weighted, offset univariate specializations per construction
check every factor degree, all highest coefficients, and the exact
final leading coefficient. Both two-group partition families are
enumerated separately. The symbolic identity and the positive zero-set
proof supply the unbounded result; these finite audits supplement them.

The auxiliary factor generally differs from its predecessor away from
Qs=Ql=0. The construction does not delete, weaken or assume either
comparison for free. No global arithmetic optimum, real-witness
equivalence, or proof-assistant formalization is claimed.

Two independent complete proof/source/default reviews passed without
findings. They checked the corrected original-source identities, both
positive tuple equivalences, exact operation ledgers and all leading
exponents. One separately evaluated128 direct mathematical formulas per
variant across bases16,32,128,512, and independently enumerated the15
and31 two-group partitions, confirming minimum largest degrees64 and68.
