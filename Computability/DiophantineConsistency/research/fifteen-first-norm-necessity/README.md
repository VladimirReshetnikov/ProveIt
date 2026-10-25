# The first P66 norm still supplies the population kernel

The normalized strong auxiliary-index lemma removes the first norm from early
main-index recovery. It does not supply the separate relation between the first
and main Pell indices used to recover the half-binomial population. A fully
specified free-port family below satisfies every other P66 factor, even with
the exact intended equality `X=2^R`, and admits no completion of the first norm.
This proves failure of pointwise redundancy over the free coefficient ports.
It is **not** a false zero for the actual coherent indexed coefficient tuple,
and does not disprove an existence-level equivalence for that particular tuple.
No cheaper complete replacement, changed equation or numerical endpoint is
claimed. All work here is ordinary mathematics and inert source inspection;
no application, compiler, Lean, TeX/PDF tool or numerical search was run.

## 1. Exact setting and the part that no longer needs N0

Use the accepted P66 definitions, with all fifteen inputs positive:

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, ell=E*k*Y, c=k*Y+eta, a=E+Y,
    A=a+2, H=4*a+3, Delta=A^2-1, D=X+a*c+gamma*H,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MFsrc)*J,
    S=Delta*i*c^2, V=f^2*(c*T-R)-c,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2, Nk=k-h*E-R,
    Nt=(K0+w)*C+(q-F)-z*(q-1), Ns=Delta*f^2-S^2.

The accepted equation is `N0*N1*Na*Nk*Nt*Ns-Delta=0`. For this inquiry
only, suppose its remaining product without N0 equals Delta. Canceling the
positive Delta gives a product of the five integer factors

    N1, Na, Nk, Nt, f^2-Delta*i^2*c^4

equal to 1. The same modulo-four arguments as the accepted proof give

    N1=Na=f^2-Delta*i^2*c^4=1,
    Nk=Nt=epsilon, epsilon in {+1,-1}.

No positivity of Nk or Nt is assumed at this point. The transport argument
first yields only C>=0. Its C=0 boundary is retained. The valid mask bounds
then give `0<R<q^4-2<E`. Since h>0,

    k=R+h*E+epsilon>R, c=k*Y+eta>2*k,
    0<R<c/2.

Apply the separately proved normalized strong auxiliary-index lemma to the
strong norm and Na. It gives `c=psi_A(R)`, with R odd. Because the actual
D is positive and N1=1, `D=chi_A(R)`. The actual trace identity gives

    X=2^R modulo H.

Thus N0 is unnecessary for this early index and trace-congruence stage.
This statement does not yet recover epsilon=1, C>0, an exact power X, or the
population condition for the native compiler.

## 2. The two later uses of N0 in the complete proof

The first norm classifies at the different parameter `P0=2*X*Y^2+1`:

    k=2*psi_P0(n), tau=chi_P0(n), n>=1.

Since P0>A and c>k, the recovered main index R is larger than n. Reduction
modulo E gives `2*n=R+epsilon modulo E`. The bounds in the accepted proof
remove the period multiple. Its duplication comparison excludes epsilon=-1,
giving `2*n=R+1` and Nt=1. Writing R=2*r+1 therefore gives n=r+1.

This *additional* Pell-index relation is used twice:

1. The ratio estimate

       (2*A-1)^2/(2*P0)>(X+1)^2/X>X,
       c/k>X^r/2, Y>X^r/2-1>X^r/3>2^R

   makes the main congruence lift to the exact integer equality X=2^R.
2. The subsequent post-index half-binomial ratio calculation uses both
   recovered Pell indices and the strict interval `k*Y<c<k*(Y+1)`. It gives

       Y=floor((X+1)^(R-1)/X^((R-1)/2))/2,
       v2(Y)=popcount(R)-2.

   That valuation supplies the native mask population inequality. It is a
   further use of N0, even if an independent argument already proved X=2^R.

The source locations are INHERITED_ORDINARY_PROOF Sections4--7 and the
normalized/source54 composition in SHORT_COMPOSITIONS_PROOF Sections2,3,8.
The older raw signed-index/guard exchanges concern a different explicit
source; none supplies the missing first Pell index for P66.

## 3. A free-port zero of every remaining factor

Fix the following small coefficient tuple and positive outer coordinates:

    beta=15, K0=8, MC=6, MFsrc=27,
    J=1, F=1, alpha=14.

Then B=16, d=4 and MF=MFsrc-(B-1)=12. These satisfy the ordinary numerical
mask hypotheses `0<MC,MF<B-1`, `MC=2 modulo4`, `MF=4 modulo8`, and
`popcount(MC)+popcount(MF)=2+2=4=d`. They are not asserted to be the
coefficients of any blank-input compiler. Direct arithmetic gives

    q=16, C=1, G=15*15+14=239,
    R=239*255+(6+16*27)=61383=3 modulo4.

Put

    X=2^R, w=2^(R-4), s=1, Y=4096, E=X*Y,
    z=(w+22)/15.

Since R-4=3 modulo4, w=8 modulo15. Thus z is a positive integer and
`Nt=w+23-15*z=1`. The already exact power X will not be the defect.

Set `A=Y*(X+1)+2`, `a=A-2`, `H=4*A-5`, `Delta=A^2-1`, and define

    c=psi_A(R), D=chi_A(R).

The open interval

    I=(c/(Y+1), c/Y)

has length `c/[Y*(Y+1)]>E`. Indeed R>=5 and the Pell recurrence give
`c> A^4`, while A>Y+1 and A>E. Its lower endpoint is greater than A^3,
hence greater than `R+E+1`. An open interval of length greater than E
contains an integer in every residue class modulo E. Choose

    k in I, k=R+1 modulo E,
    h=(k-R-1)/E, eta=c-k*Y, zeta=k-eta.

All three are positive integers. Their definitions give exactly

    k=eta+zeta, c=k*Y+eta, Nk=1.

The Pell trace projection gives `D-a*c=X modulo H`. Moreover
`D-a*c=2*c-psi_A(R-1)>c>X`, so

    gamma=(D-a*c-X)/H

is a positive integer and the actual supplied D formula holds. Hence N1=1.

## 4. Complete positive normalized-strong and auxiliary witnesses

Let m=R*c. Pell composition gives

    psi_A(m)=c*psi_D(c),
    psi_D(c)=c*D^(c-1)=0 modulo c.

The congruence follows from `D^2-1=Delta*c^2`. Therefore define the positive
integers

    f=chi_A(m), i=psi_A(m)/c^2,
    S=Delta*psi_A(m)=Delta*i*c^2.

They satisfy `f^2-Delta*i^2*c^4=1`, `S^2=Delta*(f^2-1)`, and Ns=Delta.

For j=(R-1)/2, use the integer odd-index polynomial Q_j specified in the
normalized auxiliary lemma:

    chi_t(R)=t*Q_j(t^2),
    Q_j(0)=(-1)^j*R,
    Q_j(1-A^2)=(-1)^j*psi_A(R).

Here j is odd. Put

    Vstar=chi_S(R)/S=Q_j(S^2), y=psi_S(R).

These are positive integers. Because `S^2=1-A^2 modulo f^2` and c divides S,

    Vstar=-c modulo f^2, Vstar=-R modulo c.

Also `f^2=1 modulo c` and gcd(c,f)=1. Consequently

    T=(Vstar+c+R*f^2)/(c*f^2)

is a positive integer. It gives the actual V=Vstar, and the Pell norm at S
gives `S^2*(V^2-y^2)+y^2=1`, namely Na=1. We have constructed every
positive P66 coordinate other than tau, which may be any positive integer
after N0 is omitted. Every remaining factor has its required value:

    N1=Na=Nk=Nt=1, Ns=Delta.

The remaining product therefore equals Delta exactly. This construction
uses no finite search and does not leave a sign or divisibility witness
unassigned.

## 5. No first-norm completion exists at this same tuple

Suppose N0=1 for some tau. Its Pell classification would give
`k=2*psi_P0(n)`. Since P0>A and c>k, one has n<R. Reduction modulo E,
Nk=1, and `E>2*R` then force `2*n=R+1`. Apply the explicit ratio estimate
in Section2 with r=(R-1)/2. It gives `Y>2^R`. This contradicts the chosen
`Y=4096<2^R`. Thus no tau restores N0=1 on this otherwise complete tuple.

For comparison, R=61383 has hexadecimal expansion EFC7 and population12,
whereas v2(Y)=12. The accepted population equality would require10. The
growth contradiction above already proves the obstruction independently
of this population count.

## 6. Exact scope of the result

The counterfamily uses four explicit free ports satisfying the ordinary
mask bounds, not the current indexed beta/K0/MC/MFsrc integers. The accepted
whole indexed tuple and its native/compiler interface remain unchanged and
pinned. No assertion is made that deleting N0 admits a zero for that tuple,
or that the current consistency interpretation becomes false. Such a claim
would need a new actual-tuple argument.

What is proved is enough to reject the proposed local redundancy argument:
early index recovery, all the other positive norm/transport factors, exact
X=2^R, and the basic mask bounds do not recover N0 or the population kernel.
Any successful cheaper replacement must restore a sufficiently strong
cross-Pell/ratio/population condition, or supply a new whole native soundness
proof plus a positive canonical converse. An exact-power bound alone does
not complete that task. No such replacement is established here.

SOURCE_PINS authenticates the mathematical inputs and the complete accepted
P66/auxiliary-lemma inventories. Only this note and inert metadata are new.
