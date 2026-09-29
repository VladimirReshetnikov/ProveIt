# Squaring the free index modulus does not repair the weakened kernel

This is a new scoped rejection of a same-cost repair, not a smaller complete
universal certificate. The established complete bound remains **76**. The
soundness of the original complete75 candidate remains open.

The tempting change is to replace `U=j*c-J` by `U=j*c^2-J` in the weakened
single-product auxiliary kernel. The register `c^2` is already computed, so
this strengthens a divisibility condition without adding an operation. The
resulting complete *source schedule* still has **75=40M+35A**, thirty positive
coordinates and nineteen equations. Its modified kernel still has42
operations. Nevertheless the exact wrong-index auxiliary family survives.

The companion [checker](explore_pell_kernel_squared_congruence.py) and
[receipt](explore_pell_kernel_squared_congruence.json) audit the whole source,
materialize two auxiliary examples, and attach the strengthened congruence
to the actual main coordinates of the existing q16/r269 counterexample.
No compiler, transport or false raw-input instance is supplied.

## Exact source and retained completeness

Use `A=a+2`, `Delta=A^2-1`, `J=2r+1`, and the single-product source

    K=i*c^2=Delta*(f^2-1),
    K*(U^2-y^2)=1-y^2,
    U=j*c^2-J=o*f-c.                                      (1)

All other seventeen source expressions/equalities are unchanged; the last
two auxiliary source polynomials are changed by substituting `j*c` for the
old positive coordinate `j`. In the actual primitive schedule only

    jc=j*c

becomes `jc=j*c2`. The checker verifies all nineteen residual identities,
including the unchanged correction by the preceding auxiliary norm.

The canonical complete76 witnesses still extend. Their packed index is odd,
so `J=3 modulo4`. Choose their standard auxiliary data

    m=2cJ, f=chi_A(m), R=Delta*psi_A(m), c^2 divides R,
    U=chi_R(J)/R, y=psi_R(J).

For `J=2h+1`, the integer polynomial `Q_h` defined by
`chi_R(2h+1)=R*Q_h(R^2)` satisfies `Q_h(0)=(-1)^h(2h+1)`.
Since `c^2` divides `R`, it follows that

    U=-J modulo c^2.

Set `i_new=(R/c)^2` and `j_new=(U+J)/c^2`, leaving all other coordinates
fixed. These are positive integers. They give `i_new*c^2=R^2` and the new
first expression for `U`; the second expression and norm are unchanged.
Thus the same complete76 construction proves the completeness direction
of this modified75 candidate. This is a canonical witness construction,
not a claim that every noncanonical complete76 value of `j` is divisible
by `c`.

## The stronger wrong-index CRT

Let `A>=2`, let `p>=3` be odd, and put

    c=psi_A(p), d=chi_A(p), Delta=A^2-1,
    f=chi_A(2p)=2d^2-1,
    R=2Delta*c*d, K=R^2, i=4Delta^2*d^2.

Then `K=i*c^2=Delta*(f^2-1)`. Let `J` be any positive odd integer below
`c`, and define `g=gcd(p,c^2)` and `sigma=(-1)^((p-1)/2)`.
Choose an integer `t>=0` with

    p+4pt=-sigma*J modulo c^2,
    (-1)^t=-sigma.                                       (2)

These conditions are soluble **if and only if `g` divides `J`**. Indeed
`c` is odd, so `gcd(4p,c^2)=g`, and after division the first congruence has
the explicit solution

    t=((-sigma*J-p)/g)*(4p/g)^(-1) modulo c^2/g.

The modulus `c^2/g` is odd, so adding it once if necessary supplies the
required parity. Necessity follows by reducing the first congruence modulo
`g`. This is an exact solvability statement for this family, not a
classification of arbitrary solutions of (1).

Set

    s=p+4pt, U=chi_R(s)/R, y=psi_R(s).

Because `s=p modulo4`, the two polynomial identities from the existing
single-product proof give

    U=sigma*s=-J modulo c^2,
    U=sigma*psi_A(s)=sigma*(-1)^t*c=-c modulo f.            (3)

The first equality uses `c^2|R^2`, which already holds in the wrong-index
family. The second uses `R^2=1-A^2 modulo f` and
`psi_A(z+4p)=-psi_A(z) modulo chi_A(2p)`. Therefore

    j=(U+J)/c^2, o=(U+c)/f

are positive integers. The Pell norm at base `R` supplies the middle
equation of (1). All positivity arguments of the original family remain
valid: `R>f>2c`, `s>=3`, and `U>=4R^2-3>max(c,f,J)`.

Thus upgrading the congruence from modulo `c` to modulo `c^2` does not
recover the lost requirement that the auxiliary index be divisible by
`c`. In coprime cases it imposes no further restriction on `J` at all.

## Attach the existing wrong-index kernel and a numerical input bridge

The existing dyadic-balanced primary example has

    q=16, r=269, J=539, p=329,
    X=2^329, Y=2^91, a=Y(X+1), A=a+2.

Its seven first/main kernel equations and scale bounds were proved in
[the dyadic-balanced note](../../1980/EXPLORATION_DYADIC_BALANCED_WRONG_INDEX.md).
The actual `c=psi_A(329)` has138,089 bits and `gcd(p,c)=1`, hence also
`gcd(p,c^2)=1`. Construction (2)--(3) attaches every changed auxiliary
equation. It still has actual index329 rather than539, and
`popcount(269)=4<12`, so4096 does not divide `binom(538,269)`.
The larger CRT and its positive finite precursors are computed exactly;
its final auxiliary Pell outputs are supplied by the proof, not expanded.

One can additionally attach a bounded numerical odd-index input bridge:
take `u=3`, `W=8`, and

    kappa=psi_A(3), mu=chi_A(3),
    delta=(kappa-3)/Delta,
    phi=c-kappa,
    rho=(mu-a*kappa-8)/(4a+3).

Here `delta=4`, `phi>0`, and the exact base-two congruence makes `rho` an
integer. Its positivity follows from
`mu-a*kappa=2kappa-psi_A(2)>kappa>8`. Thus all four numerical bridge
equations hold, with `W<q` and `u<p`. This observation shows that those
equations, as a numerical component, do not restore the correct main
index. It does not identify `u=3` with the actual compiled quantity
`2d*x+b`; in particular this is not a full raw-input witness.

## Focused evidence

The whole modified75 source is expanded independently against its primitive
schedule. Modular checks cover238 admissible triples and retain97 excluded
ones. Two complete auxiliary tuples are materialized:

|A|p|J|c|auxiliary index|bits of U|
|---:|---:|---:|---:|---:|---:|
|2|3|9|15|459|5,585|
|4|3|15|63|15,891|314,859|

For the q16 primary example the checker evaluates the138,089-bit main
coordinate, the276,177-bit reduced CRT modulus, and the276,187-bit auxiliary
index. It verifies the CRT residue, parity, coefficient identity and all
four numerical input-bridge equations. It does not evaluate `Q_h` at this
enormous index; equations (3) are the proof of its two residues. The final
auxiliary coordinates are not numerically materialized.

The current original75 candidate is neither proved nor refuted by this
result. The rejection concerns the proposed strengthened auxiliary kernel.

Author checks and an independent full scoped proof/source/receipt review
pass. Fresh default replay matches the saved receipt.
