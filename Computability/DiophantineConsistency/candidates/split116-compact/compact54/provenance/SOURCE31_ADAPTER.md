# Direct adapter for the literal 31-positive-variable source

This note makes explicit the connection between the bundled
`proofs/parent_quartic31.json` and the ordinary native/Pell theorem. It uses the
whole package31 tuple and the old positive transport coordinate throughout.
It is a mathematical adapter, not a new proof-assistant certificate.

Use the source names and put `q=beta J+1`, `k=eta+zeta`, `C=q-F-alpha`,
`H=4a+3`. Its first defining equations imply

    L=q²−1, N=q³, X=wq, Y=sq³=a−E, E=XY,
    a=E+Y, c=kY+eta, P=E(c−eta)+k=EkY+k.

Thus its first norm is exactly

    tau²−(EkY)(EkY+k)=1.

The remaining definitions give `Delta=(a+2)²−1`,
`D=X+ac+gamma H`, `C2=c²`, `F2=f²`, and `I=ic²`. Its main, strong, and
auxiliary equations are precisely

    D²−Delta c²=1,
    I²=Delta(f²−1),
    I² V²−(I²−1)y²=1.

The packing identity, using `N=q(L+1)`, gives

    R=[(q−1)(q−F)+alpha](q²−1)+(MC+q MF_source)J=jc−V.

Consequently the index equation is `k−hE−R=1`, while the two retained
auxiliary projections give the exact congruences

    V=of−c ≡−c (mod f),   V=jc−R ≡−R (mod c).

The old transport equation is

    (K+w)C+(q−F)−z(q−1)=1.

It forces `C>0`, since its equivalent form is
`(K+w)C=F+(z−1)(q−1)>0`. Thus the strict outer bounds of
`ORDINARY_BLANK_PROOF.md`, Sections 3–4, apply. The first/main norm
classification and the index equation give the same bootstrap `c>A Delta²`,
where `A=a+2`. The ordinary strong-rank argument then yields

    f=chi_A(m), c|m, p|m, I=Delta psi_A(m), c²|(f²−1),

with the same strict size margins. That argument precedes the auxiliary
step and uses neither a supplied `T` nor any auxiliary projection formula.
The exact congruences displayed above therefore supply precisely the two
inputs used in Section 5's auxiliary step-down. It recovers `p=R` and the
remaining power/population/native semantics without modification.

One may alternatively restore the ordinary positive `T` after strong-rank
recovery. From `of≡−R (mod c)` and `f²≡1 (mod c)` it follows that
`o+Rf≡0 (mod c)`. Hence

    T=(o+Rf)/c

is a strictly positive integer and

    c(Tf−1)−Rf²=of−c=V.

This gives an actual solution of the ordinary old-transport system. The
divisibility `c²|(f²−1)` must be obtained from the rank theorem; cancelling
`Delta` directly in `I²=Delta(f²−1)` would not justify it.

For completeness start with the canonical ordinary witnesses supplied by
the halting/native theorem. Its auxiliary construction has positive
`V=of−c=jc−R`, with `o,j>0`, and `V>1`. The norm gives
`y²−V²=(V²−1)/(I²−1)>0`; set the source's `g=y²−V²`. All other registers
are the positive expressions listed above, together with `Baux=I²`.
The source equations follow identically, including
`y²−Baux*g=1`. This establishes the required existence equivalence directly,
without importing an unlisted quartic32 register assignment or changing the
transport-coordinate convention.
