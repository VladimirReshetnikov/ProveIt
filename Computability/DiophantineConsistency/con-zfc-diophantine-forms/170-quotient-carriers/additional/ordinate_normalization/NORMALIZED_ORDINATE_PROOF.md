# A residue chart before eliminating a Pell square root

Research note, 25 October 2026. This is an auxiliary result for the ProveIt
universal compiler. It is not claimed to improve the fixed-instance
Con(ZFC) Pareto frontier. The literal source has 91 binary operations,
17 positive witnesses, and exact degree 269. The comparison is the
repository's complete92 norm-unit construction, with 92 operations,
17 witnesses, and degree 325. The underlying complete84 compiler and its
accepted signed-quotient theorem are inherited assumptions of this note.

## 1. The new algebra

Use the complete84 notation, with the main Pell discriminant
Delta=(a+2)^2-1, c>0, strong multiplier i>0, auxiliary quotient T>0,
and the integer rank expression R. Put

    I=i*c^2, S=Delta*I, Q=S^2, D=1+I*S,
    u=c*T, b=c+R*D, p=D*u^2.

Let z be a new positive integer coordinate, replacing the old auxiliary
ordinate y. Define

    qz=Q*z,
    W=1+(qz-z)*(qz-2),
    A=p+b^2-W,
    K=A^2-4*p*b^2.

The retained P5 is the product of the original first, main, input,
index, and transport factors. The new equation is

    P5*(K+1)-1=0.                                      (1)

All definitions are polynomial abbreviations. No quotient occurs in the
literal equation. The exact source is `equation91_degree269.json`.

The conceptual change is to impose y=Q*z-1 *before* eliminating f.
The auxiliary norm then has an exact polynomial factor Q:

    y^2-1=Q*z*(Q*z-2),
    Q*V^2-(Q-1)*y^2-1
      =Q*[V^2-1-(Q-1)*z*(Q*z-2)]
      =Q*(V^2-W).                                    (2)

The old root elimination squared the high-degree Q coefficient. Here it
cancels as a nonzero integer before the field norm is taken. The product
(Qz-z)(Qz-2), rather than a separate Q-1 producer, saves one multiplication.

## 2. Soundness, including all signs and denominators

Every retained witness is positive and the fixed-program tuple is valid.
Before using any equation, the actual parent definitions give

    Delta>0, c>0, i>0, T>0, Q>1, D>c.

For every integer R, b=c+R*D is nonzero: if R>=0 it is positive,
and if R<=-1 it is negative. Also u=c*T>0. Consequently 2*u*b is
nonzero on the entire retained positive domain. This fact does not use
native decoding, a bound on R, or an equation at a zero.

At a zero of (1), the two integer factors P5 and K+1 are units.
But K+1=A^2-4*p*b^2+1 is 1 or 2 modulo 4, so it cannot be -1.
Therefore

    P5=1, K=0.

Define, in the proof only,

    f=A/(2*u*b).

Since K=0 and p=D*u^2, f^2=D. A rational square root of an integer
is an integer: reduction to coprime numerator and denominator proves the
denominator is 1. Thus f is a nonzero integer. Define the integer

    y=Q*z-1>0, V=u*f-b.

The equation A=2*u*b*f now gives

    V^2=D*u^2-2*u*b*f+b^2=p+b^2-A=W.

By (2), the original auxiliary norm is 1. The original normalized
strong norm is f^2-Delta*i^2*c^4=D-(D-1)=1. The retained five factors
have product 1. Hence the complete84 polynomial vanishes on the
restored signed f and positive y, with all other coordinates unchanged.

To restore the sign of f, use the accepted source-specific signed-T
theorem consumed by both complete90 and complete92. The only original
direct consumers of f are f*f and T*f. If restored f were negative,
simultaneously replacing f,T by -f,-T would preserve every old computed
value and yield a positive-f, negative-T zero. The accepted theorem
excludes this on the full valid fixed-program recipe. Thus f>0, and a
new positive zero restores a genuine positive complete84 zero at the
same ordinary input. The rational formula makes restored f unique.

This argument uses the same inherited signed-domain result as the
repository's 90- and 92-operation elimination constructions; it does not
claim that arbitrary four- or six-port constants satisfy that theorem.

## 3. Canonical completeness and the residue lemma

For an integer S>=2, let psi_S(n) be the Pell ordinate determined by

    psi_S(0)=0, psi_S(1)=1,
    psi_S(n+2)=2*S*psi_S(n+1)-psi_S(n).

For every m>=0,

    psi_S(2m+1) = (-1)^m (mod 4*S^2).               (3)

Proof: odd ordinates satisfy the two-step recurrence
v_(m+1)=(4*S^2-2)*v_m-v_(m-1), with v_0=1 and
v_1=4*S^2-1. Modulo 4*S^2 this recurrence has the solution
v_m=(-1)^m. This is an elementary induction, not a finite test.

The inherited valid compiler supplies canonical accepting outer data
with R=3 modulo 4. Its complete strong/auxiliary construction can take

    y*=psi_S(R), V*=chi_S(R)/S.

The old construction proves V* integral, positive, and congruent to
-c modulo f^2 and to -R modulo c. It therefore gives a positive
old auxiliary quotient T=(V*+c+R*f^2)/(c*f). These canonical data are
the same data used in the fixed P66 completeness construction, where
the stronger quotient with denominator c*f^2 is integral.

Since R=3 modulo 4, (3) gives 4*Q | y*+1. Consequently

    z=(y*+1)/Q

is a strictly positive integer (indeed a positive multiple of 4).
Keep all other canonical coordinates and remove f. Equation (2), the
old strong norm, and the old five-factor value P5=1 give
A=2*u*b*f, hence K=0 and (1). Thus every accepted ordinary input has
a positive new witness tuple.

The new chart need not contain every old positive tuple: an old auxiliary
ordinate can occupy the other residue class modulo Q. The assertion is
preservation of the accepted ordinary-input set, with a sound unique
root restoration and an explicit canonical completeness map. No full
zero-set bijection with complete84 or complete92 is claimed.

## 4. Paid arithmetic and exact degree

Remove all original producers depending on f or y. There are exactly
66 remaining rows. The new tail contains 25 rows, giving

    91 = 50 multiplications + 41 additions/subtractions.

The parent witness list loses f and replaces y by z, so 17 positive
witnesses remain. The ordinary input and the same six fixed numerals
are preserved. Every source row, witness, input, and fixed port is live.

After fixing the program tuple, the inherited cancellation-aware degrees
are deg(P5)=81, deg(Q)=46, deg(D)=34, deg(R)=4, deg(c)=5.
Thus deg(b)=38, deg(u)=6, deg(p)=46 and deg(b^2)=76. The new
W has degree 94, with leader Q_top^2*z^2. It dominates p and b^2,
so A has degree 94, and A^2 has degree 188. The term 4*p*b^2 has
degree 122 and cannot cancel that leader. Finally (1) has exact degree
81+188=269.

With q0=Bm1*Jrep, k0=eta+zeta, gamma0=rho+sigma, and

    Ttransport=w*(q0-F-Z-alpha-twice_cell_bits*x)
               -transport_quotient*q0,

the inherited leading forms are

    P5_top=-32*h*gamma0*delta^2*k0^3*w^10*s^13*q0^49*Ttransport,
    Q_top=i^2*k0^4*w^4*s^8*q0^28.

The entire new leader is therefore

    -32*h*gamma0*delta^2*i^8*k0^19*w^26*s^45*q0^161
        *Ttransport*z^4.

The coefficient at

    Jrep^162*h*rho*delta^2*i^8*eta^19*w^26*s^45
        *transport_quotient*z^4

is 32*Bm1^162, nonzero for every valid compiler slice. Hence degree269
is attained uniformly; it is not just the degree of a numerical sample.

## 5. What this establishes

Relative to the named accepted complete84 calibration and signed-domain
proof, this is a complete universal polynomial with 17 witnesses and
the improved operation/degree pair (91,269), compared with (92,325).
All new arithmetic arguments are ordinary unbounded proofs formalizable
in ZFC. The standard-library checker establishes the finite source and
algebraic claims; it does not compile an object-language ZFC proof.

For the user's particular fixed Con(ZFC) problem, existing 14-positive
and 13-positive equations are cheaper. Accordingly this packet is useful
as a reusable compression lemma and separate universal tradeoff, and
must not be advertised as a new smallest fixed consistency equation.
