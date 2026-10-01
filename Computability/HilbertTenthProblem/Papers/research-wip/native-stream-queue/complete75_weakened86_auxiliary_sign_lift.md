# Exact auxiliary signs and positive lifts for the86 candidate

The [negative-input residue packet](complete75_weakened86_negative_input_residues.md)
classifies a retained subsystem. This separate successor closes its
auxiliary converse after imposing one exact sign condition. At fixed
integer `A>=3`, odd `p>=3`, `c=psi_A(p)` and arbitrary integer target
`J_target`, positive witnesses for the full normalized strong and
auxiliary block exist **if and only if**

    J_target=-p modulo c                 when p=1 modulo4,
    J_target=+p or-p modulo c            when p=3 modulo4.       (1)

The target here is not the repunit coordinate named `Jrep`. The theorem
does not presume that the target is positive or bounded. It reconstructs
all five positive supplied auxiliary coordinates, including for negative
targets of arbitrarily large magnitude.

Together with the prior CRT test, this gives an exact existence
criterion for **full R<0,mu<0 candidate extensions of fixed valid first,
main and outer transport data**. No passing actual outer tuple or
false-input full zero is supplied. The [weakened86 candidate](complete75_weakened_bound86_candidate.md)
therefore remains unresolved: this is a conditional characterization,
not a universal86 proof or a counterexample.

The [checker](complete75_weakened86_auxiliary_sign_lift.py) and
[receipt](complete75_weakened86_auxiliary_sign_lift.json) retain the
unchanged86=48M+38A source,19 positive supplied coordinates and exact
degree203. The established75/87 bounds are unchanged.

## 1. The exact five-coordinate system

Put `Delta=A^2-1`. The positive supplied coordinates are
`f,i,j,o,y`, where y is the literal source's `y_aux`. Set

    t=i*c^2, T=Delta*t, V=of-c.

The three equations are

    f^2-Delta*t^2=1,
    T^2(V^2-y^2)+y^2=1,
    j*c=V+J_target.                                         (2)

These are exactly the source's normalized strong and auxiliary norms
equal to1, together with its linear factor equal to lambda when
`J_target=R+epsilon-lambda`. The literal auxiliary multiplier is
`Delta^2*(i*c^2)^2=T^2`; it is not an approximation to an old multiplier.

Pell classification in the first equation gives an index m>0 with

    f=chi_A(m), psi_A(m)=i*c^2.

The strong-divisibility and binomial argument already recorded in the
[index-gap proof](complete75_weakened86_index_gap.md), Section2, applies
without any input-root sign assumption. In detail,

    gcd(psi_A(m),psi_A(p))=psi_A(gcd(m,p))=c

forces p|m. Write m=p*b. Dividing the Pell binomial expansion by c and
reducing modulo c gives

    psi_A(pb)/c=b*chi_A(p)^(b-1) modulo c.

The left side is divisible by c and `gcd(chi_A(p),c)=1`. Hence c|b,
so **pc|m**. Conversely, every positive multiple m of pc has
`c^2|psi_A(m)` by the same expansion.

Since p is odd, c is odd: the recurrence modulo2 alternates0,1 with
the index. Also

    c>=5^(p-1)>2p, m>=pc>2p+1,
    f>2chi_A(2p)>2c.                                      (3)

For the second inequality, each forward chi step multiplies its
positive first coordinate by more than A>=3. Thus the strict bound
`f>2chi_A(2p)` follows from the index separation; the weaker bound
`f>2c` alone would not justify the later step-down. Since o>=1,
`V=of-c>=f-c>0`.

The second norm in(2) is

    (TV)^2-(T^2-1)y^2=1.

Consequently there is ell>0 with

    TV=chi_T(ell), y=psi_T(ell).

Because T divides the first coordinate and `chi_T(2r)=(-1)^r modulo T`,
ell is odd. Here T>1 follows already from(2) and the positive inputs.

## 2. Two quotient identities and a strict step-down

For ell=2s+1 let Q_s be the integer polynomial determined by

    chi_T(2s+1)=T*Q_s(T^2).

It has `Q_0(z)=1`, `Q_1(z)=4z-3`, and the two-step recurrence

    Q_(s+1)(z)=(4z-2)Q_s(z)-Q_(s-1)(z).

The same recurrence and these initial values prove the exact identities

    Q_s(0)=(-1)^s(2s+1),
    Q_s(1-A^2)=(-1)^s*psi_A(2s+1).                    (4)

Since `T^2=Delta*(f^2-1)=1-A^2 modulo f`, and T is divisible by c,
the actual integer V satisfies

    V=(-1)^((ell-1)/2)*psi_A(ell) modulo f,
    V=(-1)^((ell-1)/2)*ell       modulo c.             (5)

The congruence `V=-c modulo f`, squared and inserted into the Pell
doubling identity, yields

    chi_A(2ell)=chi_A(2p) modulo f.                   (6)

We give the needed strict refinement directly. Choose integers k and
`0<=r<=m/2` with `ell=+r+k*m` or `ell=-r+k*m`. The Pell pair at2m is
`(-1,0) modulo f`, hence

    chi_A(2ell)=(-1)^k*chi_A(2r) modulo f.

If 2r=m, the right side is0 modulo f, whereas
`0<chi_A(2p)<f/2`; this is impossible. Otherwise
`chi_A(2r)<=chi_A(m-1)<f/3`. Odd k would make the strictly positive
sum `chi_A(2r)+chi_A(2p)<f` divisible by f, also impossible. Even k
therefore gives equality of the two small positive chi coordinates,
so r=p. We have proved

    ell=epsilon_p*p+2z*m, epsilon_p in{1,-1}, z integer.       (7)

This z is an index shift, not any supplied candidate coordinate. In
particular it is distinct from the positive supplied auxiliary j.

## 3. Necessity of the exact target signs

Set `s_p=(-1)^((p-1)/2)`. Substituting(7) into(5) gives, for either
choice of epsilon_p,

    V=s_p*(-1)^(z(m+1))*c modulo f,
    V=s_p*(-1)^(zm)*p     modulo c.                         (8)

The formulas are independent of epsilon_p: negating p changes the sign
of psi_A(p) and of the odd-index quotient prefactor simultaneously.
They use the Pell pair at2m being(-1,0) modulo f, and c|m.

Since V=-c modulo f and f>2c, the coefficient in the first line must
equal-1. Since `J_target=-V modulo c` and c>2p, the second line determines
the target sign unambiguously.

If m is odd, the first line forces s_p=-1, hence p=3 modulo4. The
second line then allows either sign, according to the parity of z.
If m is even, the second line is always V=s_p*p modulo c, so the
target sign is `-s_p`. Thus p=1 modulo4 forces target residue-p; when
p=3 modulo4 both residues remain possible. This proves necessity in(1).

## 4. Canonical sufficiency with all five coordinates positive

Let omega be an allowed sign in(1), and suppose
`J_target=omega*p modulo c`. Choose m and an initial odd ell as follows:

| p modulo4 | omega | m | initial ell |
| --- | --- | --- | --- |
| 3 | +1 | pc | p |
| 3 | -1 | pc | p+2m |
| 1 | -1 | 2pc | p+2m |

Set

    f=chi_A(m), t=psi_A(m), i=t/c^2, T=Delta*t.

Section1 proves that i is a positive integer. The strong norm holds
identically. For any ell obtained from the table by adding a nonnegative
multiple of4m, define

    V=chi_T(ell)/T, y=psi_T(ell).

Oddness of ell makes V an integer. Formula(8) gives

    V=-c modulo f, V=-omega*p modulo c.                      (9)

Adding4m preserves both congruences and oddness. As that multiple
increases, V tends to infinity. We may therefore choose it so that
`V+J_target>0`, even if J_target is a large negative integer. Then

    o=(V+c)/f, j=(V+J_target)/c                              (10)

are positive integers. All five coordinates `f,i,j,o,y` are positive,
and every equation in(2) holds exactly. This proves sufficiency and
the positive lift, without a size assumption on the target.

This is an existence construction, not a claim that huge witnesses are
cheap to print or compute. `canonical_recipe` returns exact index and
Pell-expression recipes. The checker's optional `materialize` function
has explicit bit limits and is used only for manageable local hosts.

## 5. Composition with the actual negative-input residue test

Fix the unchanged compiler constants and positive outer data
`Jrep,x,F,alpha,w,s,zplus`, together with main/first indices n,p. Impose
the actual source contract from the preceding packet, including

    q=(B-1)Jrep+1, X=wq^3, Y=sq^3, E=XY,
    a=Y(X+1), A=a+2, H=4a+3,
    k=2psi_(2XY^2+1)(n), c=psi_A(p),
    kY<c<k(Y+1), p odd>=13, n<p<2n,
    chi_A(p)-a*c-X=gamma*H, gamma>=2,
    C=q-F-alpha-2d*x>=0,
    nu=(K0+X)C+(q-F)-zplus(q-1) in{1,-1}.                    (11)

The source's three remaining positive first/main coordinates are fixed
by these data:

    eta=c-kY, zeta=k-eta,
    tau_gap=chi_(2XY^2+1)(n)-XY^2*k.                         (12)

The ratios make eta,zeta positive. The last expression is positive
because, writing `P=2XY^2+1`, it equals
`chi_P(n)-(P-1)psi_P(n)=2psi_P(n)-psi_P(n-1)`.

For each epsilon in{1,-1}, set `lambda=epsilon*nu`, so that
`epsilon*lambda*nu=1`. For each **allowed omega in(1)**, run the preceding
finite CRT classifier with the actual `M,K,u,E,k,gamma` from these data.
The following is an exact conditional theorem:

> There exists a full positive candidate zero extending the fixed
> data(11), with R<0 and mu<0, if and only if at least one of these
> finite CRT classes passes.

Necessity uses the unchanged source's sign-safe norms and full strong
rank: the first, main, input, auxiliary and normalized strong factors
are1, the other factors are epsilon,nu,lambda, and their product is1.
The earlier residue theorem gives a passing class. Sections1--3 now
restrict its target sign to(1).

For sufficiency, a passing class first reconstructs positive
`delta,Z,rho,sigma,h` with R<0,mu<0 and
`J_target=R+epsilon-lambda=omega*p modulo c`. Apply Section4 afterward
to build the five auxiliary coordinates. This order creates no circular
dependency. The literal source audit checks that these five fields
occur only in the strong norm, auxiliary norm and linear factor; all
five other factors remain unchanged. The final factors are exactly

    (1,1,1,1,epsilon,nu,1,lambda),

in the source's order. Their product is1, so the complete unchanged
polynomial is zero. Every supplied coordinate is positive by the two
constructions and(12).

This does not bound or enumerate all choices of the fixed outer data.
The code's `outer_contract` checks those data before `classify_complete`
uses the criterion. It first applies the coarser c-only test, so an
already rejected tuple does not trigger a needless large search for
the Pell period modulo E. The inherited default period finder caps its
search at10,000 state steps and raises beyond that limit unless a valid
return period is supplied explicitly. Thus the mathematical finite
criterion is unrestricted, while the default implementation is guarded;
no claim of practical enumeration for every actual outer tuple is made.

No actual passing outer tuple has been found or is asserted here. The
implemented literal example uses the previous rejected ratio data
`q=16,p=21,n=15,X=2^21,Y=8192`, with `F=2,alpha=3`, the masks10/12,
offset3 and `K0=83`. Its first/main factors are1 and transport factor
is-1, but the complete negative-input classifier has no classes. The
remaining arbitrary positive fields do not make its polynomial zero.
The example does not claim that DC/DR describe an instantiated universal
program.

## 6. Exact checks and scope

The source audit extracts the actual17-row auxiliary sub-DAG, with
only the three open ports `Delta,c,index_difference`, and verifies the
dependency sets of all eight factors. Its192 complete output/factor
identities, including96 signed assignments, check that replacing the
five fields changes exactly the stated three factors and leaves the
other five unchanged.

The quotient-polynomial audit checks64 exact identities(4) through odd
index127, comparing the recurrence with closed Chebyshev-binomial
coefficients. The step-down checks cover11,880 modular cases and720
matches, plus2,376 parity/sign cases. These supplement the uniform
proof, rather than establish it by sampling.

Canonical checks cover42 modular constructions, including p=5 for the
p=1 modulo4 branch and multiple ell+4m lifts. Six p=3 cases at A=3,4,5
materialize all five positive coordinates and evaluate the three actual
source factors for both linear signs. Their targets are
`omega*p-10^6*c`, so positivity is checked with negative targets. These
are complete **auxiliary blocks**, not complete86 zeros. No giant p=5
full auxiliary output is materialized or claimed.

```sh
python3 complete75_weakened86_auxiliary_sign_lift.py
```

Author receipt generation and a fresh default replay pass. All five
local links resolve. Root's independent full proof/source review and
fresh default replay pass without findings. His separate symbolic audit
proves all three literal17-row factor formulas, recomputes the full-DAG
five-coordinate dependency closure and checks all four conditional
epsilon/nu factor products. His additional theory audit checks16 exact
quotient-polynomial identities,30 modular canonical sign lifts and four
fully materialized positive auxiliary blocks.

Native's independent full proof/source/fresh-default review also passes
without findings. His own literal executor and manual scalar audit
check512 complete eight-factor/output identities, including256 signed
assignments, across four radix choices and five-coordinate replacements.
He independently extracts the same17 rows. His separate mathematical
audit checks196 modular residue cases and six fully materialized
positive auxiliary blocks, including a negative target that forces a
further4m index shift. These complete blocks remain local auxiliary
fixtures, not complete candidate zeros.

No candidate source or prior proof packet is changed. The full86
question remains open, now with a full
conditional negative-input extension criterion and an exact auxiliary
sign restriction.
