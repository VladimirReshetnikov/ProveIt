# Retaining the strong comparison gives 91/130 and 93/90

The [coupled 88 construction](complete75_coupled_index_linear88.md) yields
two additional universal polynomial tradeoffs, each with **19 strictly
positive existential witnesses** and the ordinary positive input x:

| Polynomial operations | Multiplications | Additions/subtractions | Exact degree | Certificate operations | Equations |
|---:|---:|---:|---:|---:|---:|
| **91** |48|43|**130**|83|3|
| **93** |48|45|**90**|82|4|

These retain the full strong norm as a separate equation and group the
other seven unit factors before taking a sum of squares. They improve
the degree at 91 operations and the previous 93/118 tradeoff. The 88/151,
89/148, 92/122 and 94/84 constructions remain distinct options. The best
comparison-certificate bound remains 75.

## 1. Definitions and full positive equivalence

Use exactly the nineteen supplied coordinates, fixed compiler constants
and computed definitions of coupled 88. In particular its mask conditions
are retained:

    B=2^d, d>=4, 0<MC,MF<B-1,
    MC=2 modulo4, MF=4 modulo8,
    popcount(MC)+popcount(MF)=d.

These conditions are part of the complete compiler contract; the coupled
sign proof is not asserted for arbitrary masks. Write the strong residual
and the seven retained factors as

    Qs=T^2-K,
    N0=g^2+E*(kY)*(2g-k),
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3=K*(V^2-y^2)+y^2,
    Nk=k-R-hE,
    Nt=(K0+X)C+(q-F)-zplus*(q-1),
    Lnew=V-jc+k-hE.                                  (1)

The supplied first-root gap g, both ratio slacks eta,zeta and all other
positive domains are unchanged. T=ic^2 is still computed and its full
square T^2 is still compared with K=Delta*(f^2-1).

The 91 polynomial is

    Qs^2+(N0*N2*Nk-1)^2+(N1*N3*Nt*Lnew-1)^2.         (2)

The 93 polynomial is

    Qs^2+(N2-1)^2+(N0*N3-1)^2
        +(N1*Nk*Nt*Lnew-1)^2.                       (3)

More generally consider Qs=0 and any partition of the seven factors
into groups whose products are 1. Multiplication gives the product of
all seven factors equal 1. Since Qs=0 makes the omitted strong unit
`N4=1+Qs` equal 1, this is precisely the single product equation of 88.
Its complete theorem, including the compiler-specific packing
contradiction for the negative index sign, therefore applies unchanged.
It establishes the same ordinary-input membership and restores all
eliminated positive coordinates.

Conversely, the 88 theorem proves that at every positive zero, all eight
individual factors are 1. In particular Qs=0 and each group product in
(2) or (3) is 1. Hence both displayed polynomials vanish. Since a sum of
integer squares is zero exactly when each residual is zero, this proves
that **both polynomials have exactly the same positive solution set as 88
on its same nineteen coordinates**, under the same fixed compiler
contract. No new coordinate map or additional input convention is used.

The reasoning does not weaken the strong norm, assume unit signs
individually, or use arbitrary-assignment equality with the original
product polynomial. It relies on the established 88 theorem only after
its complete equation has been restored.

## 2. Exact source construction and arithmetic ledger

The [checker](complete75_coupled88_degree_tradeoffs.py) starts from the
actual 88 schedule. It retains the complete literal definitions of the
seven factors in (1), and the two sides T^2,K of the strong comparison.
It removes the old product-chain gates and the two instructions

    strong_difference=T^2-K,
    norm_strong=strong_difference+1.

Thus the ungrouped definitions cost **78=40M+38A**, rather than the 80
operations needed to define all eight factors. There are no changes to
any other retained instruction. The residual T^2-K is formed and paid
when constructing the final sum of squares, as part of the ordinary
residual compilation below.

With g groups of the seven factors, multiplication within groups takes
7-g further products. The certificate has g+1 equations: the strong
comparison and one equation per group. Its sum of squares adds g+1
residual subtractions, g+1 squarings and g additions. Therefore

    certificate: (47-g)M+38A, total85-g, g+1 equations;
    polynomial: 48M+(39+2g)A, total87+2g.             (4)

For two groups this is 83=45M+38A for the three-equation certificate,
and 91=48M+43A for (2). For three groups it is 82=44M+38A for the
four-equation certificate, and 93=48M+45A for (3).

Every binary addition, subtraction and multiplication is counted,
including squares and products by fixed numerals. No new supplied
witness or hidden side comparison is introduced. The
[receipt](complete75_coupled88_degree_tradeoffs.json) contains both complete
acyclic polynomial schedules, their comparison lists and output registers.

## 3. Exact degrees and highest forms

Give x and every supplied witness degree one and fixed compiler numerals
degree zero. Set

    Q=(B-1)J, k0=eta+zeta, gamma0=rho+sigma,
    Ctop=Q-F-Z-alpha-2d*x, Gtop=2g-eta-zeta.

The seven degrees and highest homogeneous forms are

| Factor | Degree | Highest form |
|---|---:|---|
| N0 |14| `w*s^2*k0*Q^9*Gtop` |
| N1 |22| `8*gamma0*k0*w^2*s^3*Q^15` |
| N2 |42| `-4*delta^2*w^5*s^5*Q^30` |
| N3 |28| `f^2*k0^2*w^2*s^4*Q^18` |
| Nk |9| `-h*w*s*Q^6` |
| Nt |5| `w*Q^3*Ctop` |
| Lnew |9| `-h*w*s*Q^6` |

The strong residual Qs has degree 22 and so contributes only degree 44
to either polynomial.

For91, the two group degrees are 65 and 64. The unique highest contribution
is `(N0_top*N2_top*Nk_top)^2`, namely

    16*(B-1)^90*h^2*delta^4*(eta+zeta)^2
      *w^14*s^16*J^90*(2g-eta-zeta)^2.               (5)

It is nonzero and has degree 130. Since the seven degrees sum to 129,
every two-group partition has largest degree at least 65; this grouping
attains that bound.

For93, the three group degrees are 42, 42, 45. The unique highest contribution
is `(N1_top*Nk_top*Nt_top*Lnew_top)^2`, namely

    64*(B-1)^60*h^4*(rho+sigma)^2*(eta+zeta)^2
      *w^10*s^10*J^60*Ctop^2.                        (6)

It is nonzero because Ctop has F coefficient -1, proving exact degree 90.
The checker enumerates all 301 three-group partitions of these seven
weights and verifies that the smallest possible largest degree is 45.
For a direct bound, a partition with largest degree at most 44 would
have to leave the weight 42 alone, as the next smallest weight is 5.
The other weights 14, 22, 28, 9, 5, 9 sum to 87, and have no subset summing to 43
or 44, so they cannot split into two groups of weight at most 44.

The corresponding 63 two-group partitions are also enumerated, confirming
the minimum 65. These lower bounds concern only these specific factor
partitions with the retained strong comparison and literal sum-of-squares
construction. They do not claim global arithmetic or degree optimality.

## 4. Exact audits and limits

Default replay recomputes and compares the deterministic receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled88_degree_tradeoffs.py

The checker verifies that all retained instructions agree literally with 88,
that the new instructions are exactly the required group products, and
that the strong-unit instructions are absent while both sides of the
strong comparison remain. It audits register availability, equation
counts and the separate multiplication/addition ledgers.

For each variant it evaluates 512 assignments: 384 positive supplied
assignments and 128 signed ones. It independently reconstructs the
original nineteen-equation source, including the positive-root coordinate
and the corrected auxiliary factor. These source residuals supply all
seven factor values and Qs, from which the full new sum of squares is
recomputed. This checks the entire polynomial rather than individual
factor identities alone. Four deliberately negative computed input roots
per variant and zero restored old quotients are included; these are
algebraic fixtures, not asserted accepting compiler tuples.

Three weighted, offset univariate specializations per variant verify all
seven degrees and highest forms, both complete polynomial degrees and
the explicit coefficients (5),(6). All 63 and 301 relevant partitions are
enumerated separately. The full positive-domain equivalence is supplied
by Section 1 and the 88 theorem, not by finite sampling.

The strong square remains fully present and paid. These constructions
preserve all compiler, synchronization and ordinary-input obligations.
No real-witness equivalence, formal proof-assistant verification or global
optimality claim is made.

Three independent full proof/source/default reviews passed without findings.
They checked the positive equivalence, the 78-operation ungrouped ledger,
residual and square accounting, exact degrees and all leading coefficients.
One independently evaluated 256 full seven-factor/strong-residual formulas
per variant, including four negative computed input roots each, and checked
both leading forms at an additional B=128, d=7 weighted/offset specialization.
Another evaluated 768 full sum-of-squares identities on signed assignments
across six compiler bases. Separate enumeration confirmed the 63 and 301
restricted partition optima. A broader independent audit covered all 877
partitions with the strong comparison retained and all 4,140 partitions
with the strong unit among eight factors; within those fixed-factor
sum-of-squares families, no further Pareto point improves these results
or the existing 94/84 construction.
