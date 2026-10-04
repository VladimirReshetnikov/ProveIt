# No free83 auxiliary extension of the new even-main-rank square/product82 family

## Theorem and exact scope

Let A>=4 be even, Delta=A^2-1, p>=2 even, c=psi_A(p), and R odd. Retain any five source factors whose product is 1. In the literal free-coefficient83 interface

    V=c(T f-1)-R f^2,
    Na=S^2 V^2-(S^2-1)y^2,
    Ns=Delta f^2-S^2,

there are no positive integers f,S,T,y with Na*Ns=Delta.

Consequently none of the full fixed outer witness tuples constructed in Sections 1-7 of square-product82-counterfamily-20261004/COUNTERFAMILY.md extends to a free83 zero by changing only f,S,T,y. That family has A even, p divisible by 4, c even, R=3 modulo 4, and P5=1. This is a nonextension theorem for that fixed family; it does not prove soundness of free83 or rule out changing the five retained factors/outer witnesses.

The proof covers nonsquarefree Delta and all actual strong-factor divisors. It does not assume without proof that strong solutions have f=chi_A(m). No upstream code or saved arithmetic schedule is run.

## 1. Pell residue separation by index parity

For any integer a>=2 and m>=1, set F=chi_a(m). For each t>=0, the residue of psi_a(t) modulo F has a representative

    epsilon*psi_a(j), 0<=j<=m, epsilon in {+1,-1}, j=t modulo 2.

Indeed the quadratic unit u=a+sqrt(a^2-1) obeys u^(2m)=-1 coefficientwise modulo F. Reduction of t modulo 2m therefore changes only the sign of psi. Reflection t -> 2m-t preserves psi modulo F, since psi_a(2m)=0 and chi_a(2m)=-1 modulo F. Both reductions preserve index parity.

Residues of opposite index parity cannot agree even up to sign. For m=1 this says 0 and 1 are distinct modulo a. For m>=2 put b=psi_a(m), bprev=psi_a(m-1). The recurrence and monotonicity give b>(2a-1)bprev, while F=a*b-bprev. Hence

    b+bprev<F.

Two representatives with distinct parity have distinct indices. Their positive difference has magnitude <F, and their sum is at most b+bprev<F. Thus neither equality nor equality up to a negative sign is possible modulo F. A zero representative likewise cannot equal a nonzero one modulo F.

## 2. The correct strong Pell lattice, including nonsquarefree Delta

Write Delta=d*b0^2, with d squarefree. Since A is even, Delta=3 modulo4 and d,b0 are odd. Let a+b*sqrt(d) be the least positive integer Pell unit for d. Write

    A+b0*sqrt(d)=(a+b*sqrt(d))^e.

The standard generation theorem for integer Pell solutions applies. If a were odd, b would be even (modulo4, since d=3 modulo4), and all its powers would have odd first coordinate. Thus a is even; then b is odd and the first-coordinate parity alternates with the exponent, forcing e odd. Set

    C=psi_a(e), delta=a^2-1=d*b^2.

Then b0=b*C, Delta=delta*C^2, and

    C*psi_A(t)=psi_a(e*t)                         (1)

for every t>=0.

For every m>=0,

    gcd(chi_a(m),b0)=1.                          (2)

First gcd(chi_a(m),b)=1 from chi_a(m)^2-d*b^2*psi_a(m)^2=1. If an odd prime l divided both chi_a(m) and C, work in the ring F_l[s]/(s^2-delta). The unit u=a+s would satisfy u^(2m)=-1 and u^(2e)=1. Raising the first equality to odd e and the second to m gives -1=1, a contradiction. The prime 2 does not divide b0. This proves (2).

Suppose Ns=Delta. From S^2=Delta(f^2-1), b0|S. Writing S=b0*s and then using squarefreeness gives d|s; set s=d*v. Thus f^2-d*v^2=1, so for some m>=1

    f=chi_a(m), S=d*b0*b*psi_a(m)=delta*C*psi_a(m). (3)

This is the actual strong lattice. In general it is larger than the subfamily f=chi_A(m), S=Delta*psi_A(m).

## 3. No unit-auxiliary, strong-Delta solution

Assume Na=1 and Ns=Delta. Necessarily S>=2: S=1 would give Delta*f^2=Delta+1, impossible. The positive integer Pell solutions at discriminant S^2-1 have least unit S+sqrt(S^2-1). Hence, for an integer t>=1 and epsilon=sign(V),

    S*V=epsilon*chi_S(t), y=psi_S(t).

Modulo S, chi_S(t) is nonzero for even t and divisible by S for odd t, so t is odd. Write t=2h+1 and use the integer-polynomial identity

    chi_S(t)/S=Q_h(S^2),
    Q_h(1-A^2)=(-1)^h*psi_A(t).

Since S^2=Delta*(f^2-1),

    V=epsilon*(-1)^h*psi_A(t) modulo f.

The literal V identity also gives V=-c modulo f. Multiplying by C and applying (1) gives

    psi_a(e*t)=+/-psi_a(e*p) modulo chi_a(m).

Here e*t is odd and e*p is even, contradicting Section 1. This proves the unit-auxiliary obstruction without any squarefree assumption. In this section R is unrestricted: it vanishes in the reduction modulo f.

## 4. Every positive auxiliary branch normalizes to the unit branch

The source-specific auxiliary small-norm theorem in the frozen structural packet proves: if Na*Ns=Delta and all variables are positive, then every positive Na is a square z^2, with z^2|Delta. This theorem needs no assumption about the five retained factors; here their product is 1, so Ns=Delta/z^2.

Since Delta=d*b0^2 and d is squarefree, z|b0. Multiply the strong equation by z^2:

    Delta*(z*f)^2-(z*S)^2=Delta.

The classification in Section 2 gives z*f=chi_a(m) for some m>=1. By (2), z=1. Thus Na=1 and Ns=Delta, already impossible by Section 3.

This yields a separate useful arithmetic corollary: when A is even, a represented positive strong divisor Delta/z^2, with z^2|Delta and f,S positive integers, must actually equal Delta.

## 5. The negative auxiliary branch is blocked by parity

The same frozen auxiliary small-norm theorem proves that Na<0 can occur only as

    f=1, S=A, Ns=-1, Na=-Delta.

Its equality-case descent gives

    V=+/-2*Delta*psi_(2A^2-1)(r), r>=0,

so V is even. But the literal expression with f=1 is

    V=c(T-1)-R,

which is odd because p even implies c even and R is odd. Contradiction.

Since Na*Ns=Delta>0, positive Na covers every positive Ns and negative Na covers every negative Ns. Sections 4 and 5 exhaust all possible signs and divisors, proving the theorem.

## Source boundary

The only imported source-specific arithmetic result is the proved small-norm descent and its direct consequences in:

- /workspace/shared/free83-structural-packet-frozen-20261004/author/early_auxiliary_norm_lemma.md

Its general lemma concerns H*v^2-(H-1)*y^2: a negative value is at most -(H-1); a positive value below H is a square; equality -(H-1) has v=2(H-1)*psi_(2H-1)(r). The source's consequences use |Na*Ns|<=Delta, which holds here with equality. No claimed generic unit normalization from an older universal circuit is imported.

The literal free83 interface is read from the frozen source and independently quoted in the inner-families release. The new82 family supplies only P5=1, A even, p even, and R odd; no mask alteration or surrogate packed R is introduced.
