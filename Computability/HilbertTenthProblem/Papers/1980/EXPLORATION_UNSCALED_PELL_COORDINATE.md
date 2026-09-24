# Removing the scale factor from U breaks the 42-operation kernel

The multiplication U=wD0 in the
[43-operation ternary kernel](EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md)
cannot simply be deleted by supplying an unrestricted positive U instead.
The proposed kernel has **42 operations = 24 multiplications and
18 additions/subtractions**, with sixteen positive auxiliary coordinates
and ten equations. It has complete positive counterexamples to its
power-of-three conclusion, including even-index examples with
D0=q^9 at q=6 and q=7. The odd-scale q=7 example also satisfies the
exact scalar index-offset equation and its positive bound.

This is an obstruction to one isolated kernel change. It does not refute
the existing 43-operation kernel or the complete 91-operation tag source.
In particular, the q=6 example does not satisfy that source's index
equation: its even D0 is incompatible with 2r+1=D0+2P for integer P.
The q=7 example closes that scalar-interface gap, but violates the tag
geometry's necessary condition3|q. No tag transport or compiler geometry
is asserted for any example.

The [checker](../verification/explore_unscaled_pell_coordinate.py) and
[receipt](../verification/explore_unscaled_pell_coordinate.json) contain
the exact sources, a materialized initial part of one witness, and an
independently checked modular computation for the ninth-power example.
Author and two independent complete proof/source/dependency reviews and
fresh verification runs pass, including recompilation of the native helper.

## 1. The exact proposed change

Replace the old supplied positive coordinate w by a supplied positive U,
named U0 in the checker. Delete the single instruction U=wD0. Retain
Y=sD0 and every other instruction and comparison. For either fixed sign
sigma, write

    E=UY, Q=UY^2, a=Y(U+1), A=a+3,
    M=6a+8, Delta=A^2-1=a^2+M,
    J=2r+1, Raux=ic^2, u=jc+sigma J.

The ten equations are

    Q(Q+1)k^2=tau(tau+1),
    c=Yk+eta, k=eta+zeta,
    k=r+1+hUY,
    a=Y(U+1),
    d=U+ac+gamma M,
    d^2=1+Delta c^2,
    (ic^2)^2=Delta(f^2-1),
    Delta(f^2-1)(u^2-y^2)=1-y^2,
    u=of+sigma c.                                  (1)

All sixteen coordinates U,s,a,c,d,f,h,i,j,k,o,tau,eta,zeta,gamma,y
remain strictly positive. As in the predecessor, the implemented last
norm uses (ic^2)^2. Its difference from the displayed source polynomial
is the preceding norm residual multiplied by u^2-y^2. The checker
verifies this exact correction and all ten comparisons in both signs.
The complete count is 24M+18A; there is no hidden division instruction.

The intended preliminary hypotheses are unchanged:

    D0>=81, r>=27, r<2D0, D0<r^2.                   (2)

They hold in all three counterexamples below.

## 2. Positive canonical solutions without U's divisibility

Let r>=27 be even, and define the exact integers

    J=2r+1, U=3^J,
    Y=sum_{j=0}^r binom(2r,r+j) U^j.                (3)

This Y is the floor of (U+1)^(2r)/U^r: the omitted negative powers are
strictly between zero and one. Let D0 be any positive divisor of Y
satisfying (2), with U>D0. Put s=Y/D0. The remaining positive canonical
construction in the 43-kernel proof applies without requiring D0 to
divide U. The dependency is explicit below.

Put Ppell=2UY^2+1 and define Pell coordinates by

    d=chi_A(J), c=psi_A(J), k=psi_Ppell(r+1),
    tau=(chi_Ppell(r+1)-1)/2,
    h=(k-r-1)/(UY),
    eta=c-Yk, zeta=k-eta,
    gamma=(d-U-ac)/M.                              (4)

The triangular norm gives the first equation in (1). Ppell is odd, so
tau is a positive integer. Ppell=1 modulo UY gives integral h, and Pell
growth makes h positive. The canonical ratio estimates give
Y<c/k<Y+1, so eta and zeta are positive integers. The recurrence of
chi_A(n)+(3-A)psi_A(n) is 3^n modulo M. At n=J it therefore makes
gamma integral; d-ac>2c>U makes gamma positive. The main Pell norm is
exact by definition.

For the last five positive auxiliaries, set

    m=2cJ,
    f=chi_A(m), i=Delta psi_A(m)/c^2,
    Raux=ic^2,
    y=psi_Raux(J), u=chi_Raux(J)/Raux,
    o=(u-c)/f, j=(u-J)/c.                          (5)

The power expansion at index 2c gives c^2|psi_A(m), so i is a positive
integer. Since J is odd, chi_Raux(J)/Raux is an integer. The exact
auxiliary congruences from the predecessor give

    u=(-1)^r c mod f, u=(-1)^r J mod c.

Here r is even, so o and j are integral with the fixed plus sign.
Pell growth gives u>c>J and makes both strictly positive. The two
remaining norm equations follow from these Pell definitions.

These are precisely the formulas and positivity arguments in Section4
of the linked 43-kernel proof. Their only uses of scale divisibility
are the definitions s=Y/D0 and w=U/D0. The first is provided by our
choice of D0; the second coordinate has been removed. All ratio,
congruence and growth arguments depend on (3), not on D0 being a power
of three. Thus (3)--(5) give every positive coordinate in (1).

## 3. A directly checked scale119 example

Take

    r=28, J=57, U=3^57, D0=119=7*17.

The exact sum (3) has 2530 binary bits and is divisible by119; U is48
modulo119. The scale is not a power of three, and (2) holds:

    81<=119, 27<=28<238, 119<28^2.

The checker materializes U,Y and all coordinates in (4), together with
s. All eleven of these supplied coordinates are strictly positive.
It checks the first seven equations of (1) exactly, including both
integer quotients h and gamma, and verifies the main-rank growth
conditions used by (5). The remaining five auxiliaries are defined
and proved positive by (5); they are not materialized.

This yields a complete positive fixed-plus42 solution with nonpower
D0. The value119 is not a ninth power, so a separate example is useful
for interfaces that prescribe a ninth-power scale.

## 4. An even-index ninth-power counterexample

Take

    q=6, D0=6^9=10,077,696,
    r=32766=2^15-2, J=65533.

The index is even and satisfies all of (2), while D0 is not a power of
three. Let U,Y be (3). We prove D0|Y without materializing Y.

First, U is divisible by3^J. Every nonconstant term of Y vanishes
modulo3^10, and Legendre's exact formula gives

    v3(binom(65532,32766))=9.

Consequently v3(Y)=9. For the factor2, the exact modular computation
described below gives

    Y mod 2^20 = 581632 = 71*2^13.

It follows that v2(Y)=13. Since D0=2^9*3^9, this proves D0|Y. Also
U>D0 and U>48r, so Section2 supplies the complete positive fixed-plus
solution. Neither the very large Y nor the Pell auxiliaries are needed
as materialized integers for this existence proof.

The modular computation rewrites (3) as

    Y=sum_{k=0}^r binom(2r,k) U^(r-k).

At each k, maintain the exact 2-adic valuation and the odd part of
binom(2r,k) modulo2^b. The recurrence

    binom(2r,k)=binom(2r,k-1)*(2r-k+1)/k

updates the valuation by subtracting the two powers of2 and updates
the odd part using the inverse of the odd denominator modulo2^b.
That inverse always exists. The resulting coefficient residue is
then inserted by Horner's recurrence. This proves every modular step
without dividing a nonunit modulo2^b or relying on a conjectured
popcount valuation formula. The checker independently compares this
algorithm with direct integer binomial sums at r=1..64 and four
moduli, giving256 exact comparisons. The large case uses32766 steps.

## 5. An odd ninth power with the exact scalar index interface

The stronger example is

    q=7, D0=7^9=40,353,607,
    r=5*7^8-1=28,824,004, J=57,648,009.

The same exact modular recurrence, now stripping factors of7, gives

    Y mod 7^11 = 1,856,265,922 = 46*7^9.

Since46 is prime to7, this proves v7(Y)=9 and hence D0|Y. The index is
even, U=3^J>D0, and all bounds (2) hold. Section2 again supplies all
sixteen strictly positive coordinates of the fixed-plus42 kernel.

Unlike the q=6 case, this scale is odd and the index lies in the needed
interval. Define

    P=r-(D0-1)/2=8,647,201,
    betaP=D0-r=11,529,603.

Both are positive, and the exact scalar equations

    2r+1=D0+2P, r+betaP=D0                         (6)

hold. Thus the isolated omission still fails if one adds the ninth-power
scale and the same scalar index-offset and bound equations.

The [C++ helper](../verification/unscaled_pell_coordinate_modular.cpp)
performs28,824,004 modular Horner steps for this identity. Its integer
arithmetic is bounded: supported moduli are at most2,000,000,000 and
indices at most100,000,000. Every modular product is below4*10^18,
and the product of a coefficient unit with an unstripped numerator is
below4*10^17. The extended-Euclidean intermediates are also bounded by
the modulus squared plus the modulus. All fit strictly within a signed
64-bit integer. The helper rejects unsupported inputs, excessive
moduli, negative coefficient valuations and nonunit denominators.

Before the large run, the Python checker compiles that maintained source
and cross-checks it against448 direct integer binomial sums: r=1..64,
four powers of2 and three powers of7. It also compares the helper with
separate Python modular implementations at(r,p,b)=(32766,2,20) and
(84034,7,8). These return581632 and5411854 respectively. The receipt
records the compiler version, helper source hash, exact compile command,
and the large invocation. From the repository root, the principal
commands are:

```powershell
New-Item -ItemType Directory -Force tmp/unscaled_pell_coordinate
g++ -O3 -std=c++17 -Wall -Wextra -pedantic Papers/verification/unscaled_pell_coordinate_modular.cpp -o tmp/unscaled_pell_coordinate/modular.exe
./tmp/unscaled_pell_coordinate/modular.exe 28824004 7 11
python Papers/verification/explore_unscaled_pell_coordinate.py
```

The helper prints `28824004 7 11 1856265922`. The complete Python checker
automatically performs the compilation and all cross-checks; it supports
g++ or clang++ and chooses the platform's executable suffix. No enormous
U, Y or Pell auxiliary is materialized in the large check.

This is still not a full tag counterexample. For beta>=2, the retained
tag equations R=kD and q=Rv imply3|q. Our q=7 violates that condition.
Nor is P in (6) supplied as a packing of actual tag fields. The example
therefore addresses only the kernel, ninth-power scale, and scalar
index/bound interface, not the additional computation constraints.

## 6. Evidence and scope

Complete fresh verification checks both42-operation sources, all twenty
symbolic comparisons, the256 Python modular cross-checks, the seven
directly materialized scale119 equations, both ninth-power divisibility
calculations, and the450 cross-checks of the compiled helper. The positive
completion argument covers the remaining equations and all sixteen
coordinates in all three even-index examples, using the fixed plus sign.
The minus schedule is counted
and source-checked but is not claimed to have these same witnesses.

All examples refute the proposed general-scale power conclusion after
deleting only U=wD0. The q=6 and q=7 cases also prescribe a ninth-power
scale, and the q=7 case additionally satisfies the scalar index-offset
and positive bound exactly. They supply neither the tag-history
equations nor the compiled initial-input conditions. Any further claim
about the complete tag system needs those missing conditions.
