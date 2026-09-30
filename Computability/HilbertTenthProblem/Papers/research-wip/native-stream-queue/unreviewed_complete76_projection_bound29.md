> Preserved author-only WIP. The source was never run and has no receipt or independent review. This proposed76-operation tie is not an established result.

# A complete76 certificate with29 positive witnesses and18 equations

The established [complete76 certificate](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md)
has an equivalent source with **76=41M+35A**, **29 strictly positive
existential coordinates**, and **18 equations**. It absorbs the explicit
input-index gap into a bound on the input Pell projection, reusing the
already computed main product gamma*H. This reduces the coordinate and
equation counts by one. **It does not reduce the76-operation bound.**

The fixed universal compiler, ordinary positive input x, actual packed
index, scale q^3, main-power transport and all program numerals are
unchanged. Every new solution restores a solution of the established
source, and every established solution has a new positive extension.
Thus for each recursively enumerable set, the same effective fixed
compiler represents that set in this29-coordinate source.

## 1. Literal change and exact ledger

Write a for the main parameter, A=a+2, Delta=A^2-1, H=4a+3 and
u=2d*x+b. The original bridge uses positive kappa,mu,delta,phi,rho and
the already supplied endpoint W:

    kappa=u+delta*Delta,
    c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*H.

Delete phi, replace rho by one positive coordinate sigma, and use only

    kappa=u+delta*Delta,
    mu^2=1+Delta*kappa^2,
    mu+sigma*H=W+a*kappa+gamma*H.                       (1)

The main kernel already computes gamma*H for its equation

    dmain=X+a*c+gamma*H.                              (2)

All other equations are retained literally. The new final projection
schedule is

    modulus_multiple=sigma*H;       # M
    difference_multiple=a*kappa;   # M
    exponent_partial=W+difference_multiple; # A
    exponent_rhs=exponent_partial+gam;       # A, gam=gamma*H already paid
    input_projection_left=mu+modulus_multiple; # A
    input_projection_left=exponent_rhs.     # free comparison

Delete the former one-addition `pell_gap=kappa+phi` and its comparison.
The new projection costs2M+3A, versus the former2M+2A. These changes
cancel exactly: the bridge still costs14=7M+7A, the unchanged kernel43,
and the unchanged outer source19. The full literal DAG in the
[checker](complete76_projection_bound29.py) remains acyclic.

The29 positive coordinates, in checker notation, are

    q,C,Jrep,F,alpha,zquot,a,c,d,f,h,i,j,k,o,r,s,w,
    tau,eta,zeta,ga,y_aux,Z,W,kappa,mu,delta,input_sigma.

Here d is the main Pell root and ga is gamma; cell width d in u is the
fixed numeral `cell_bits`, not this coordinate. No positivity is imposed
on computed registers beyond what follows from these supplied coordinates.

## 2. Main facts obtained before the input bridge

The unchanged pre-kernel outer proof and retained43-operation kernel give

    0<W<C<q, q>=16, q^2<=r<q^4,
    p=2r+1, X=2^p, a>X,
    c=psi_A(p), dmain=chi_A(p),
    gamma*H=E(p)-X,
    E(v)=chi_A(v)-a*psi_A(v)=2psi_A(v)-psi_A(v-1).       (3)

Also p is odd and, using the unchanged raw bound and fixed compiler,

    3<=u=2d*x+b<q+b<2q<p<a+1,
    u is odd.                                         (4)

These conclusions do not use the deleted gap or the old input projection.
In particular no previously decoded input, intended computation or canonical
kernel tuple is assumed in the following soundness argument.

For A>=2, E(v) is strictly increasing on nonnegative integer v. Indeed
E(0)=1,E(1)=2 and, for v>=1,

    E(v+1)-E(v)=(4A-3)psi_A(v)-psi_A(v-1)>0.          (5)

## 3. Every new solution restores the established source

The input norm and positivity classify

    kappa=psi_A(v), mu=chi_A(v), v>=1.

The new projection in(1), sigma>0 and(3) imply

    E(v)=W+gamma*H-sigma*H
         <E(p)-X+W<E(p),                             (6)

because X>q>W. By(5), v<p. Thus the old gap bound is a consequence of
the new equations.

For completeness of the decoding argument, modulo Delta the representative
of psi_A(v) is v for odd v and v*A for even v. Since v<p<a+1=A-1,
both representatives lie in[0,Delta). The first equation in(1) gives
psi_A(v)=u modulo Delta, with0<u<p. An even v would give a representative
at least2A>u. Therefore v is odd and v=u.

The standard recurrence congruence

    chi_A(u)-a*psi_A(u)=2^u modulo H

and the last equation in(1) yield W=2^u modulo H. Both W and2^u lie
strictly between0 and H, since W<q<X<a and u<p gives2^u<X<a.
Hence W=2^u as ordinary integers, exactly as required by the unchanged
compiler and its End position.

Restore

    phi=c-kappa,
    rho=gamma-sigma=(E(u)-W)/H.                       (7)

They are integers. Strict Pell growth and u<p give phi>0. Also
`E(u)>psi_A(u)>=psi_A(3)=4A^2-1>W`, using u>=3 and W<q<a.
Thus rho>0. Equations(7) restore both deleted/replaced old equations,
and all other old coordinates and equations are unchanged. The complete
established soundness theorem therefore applies.

## 4. Strict positive converse at the actual full compiler bounds

Take any solution of the established complete76 source. Its proved input
decoding gives u odd, u>=3 and u<p, while p is odd. Consequently p>=u+2.
Set sigma=gamma-rho and discard phi. The new projection follows algebraically;
the only new issue is strict positivity of sigma.

The following elementary gap bound is stronger than needed. For A>=2 and
u>=1, the Pell recurrence and0<=psi_A(u-1)<psi_A(u) give

    psi_A(u+2)-2psi_A(u)
      =(4A^2-3)psi_A(u)-2A*psi_A(u-1)
      >(4A^2-2A-3)psi_A(u)>A.                         (8)

By(3), E(p)>psi_A(p) and E(u)<2psi_A(u). Therefore p>=u+2 implies

    E(p)-E(u)>psi_A(u+2)-2psi_A(u)>A>X.              (9)

For the actual main and input projections,

    H*sigma=H*(gamma-rho)=E(p)-E(u)-X+W>0.           (10)

This proves sigma is a strictly positive integer. It uses the actual
complete-kernel bound a>X=2^p and its decoded indices, not an artificial
small-index fixture or an extra bound imposed on compiler padding.
Every other supplied coordinate remains strictly positive. The main
power and its transport quotient, actual packed r and dummy selection
are unchanged. Conversely(7) uniquely restores the discarded data, so
the two positive solution sets are in bijection on their shared coordinates.

## 5. Source audit and finite evidence

The checker expands every one of the18 source comparisons, retaining the
exact auxiliary-norm correction at the same earlier equation. It verifies
all fixed aliases, acyclic dependencies, the76=41M+35A primitive ledger,
the absence of phi/rho, and use of every one of the29 positive coordinates.
It also checks the exact two-way projection substitution independently.

Finite Pell checks verify monotonicity and(8) across small parameters.
Separate exact bridge fixtures exercise both witness maps and all new
positive coordinates. Some fixtures match the numerical q^2<=r and
X=2^(2r+1)<a bounds; they do not assert the remaining full compiler
equations, binomial-floor Y or astronomical auxiliary Pell coordinates.
The complete equivalence is the parametric proof above, building on the
reviewed complete76 theorem. No smaller arithmetic-operation certificate
or proof-assistant formalization is claimed. Independent review is pending.
