# Fixed-gap divisibility and a locally feasible constant-term-one gap

There is a useful exact restriction on the selective-gap proposal D*J-1:
its transport kernel has bounded order, independent of tableau dimensions.
A different explicit gap, (D+2)*J+1, satisfies the SAME local masks and
avoids that divisibility restriction. Neither statement supplies a Wang
compiler, a coordinated dummy controller or a nine-positive equation.
No program, compiler, checker, source generator, Lean or network was run.
The closed one-word review and all native/source packets are unchanged.

## 1. A divisibility lemma for every integer polynomial fixed gap

Let B>=2,N>=1, q=B^N, M=q-1 and J=1+B+...+B^(N-1). Let P be any
integer. Suppose alpha=A(J), where A is a fixed polynomial with INTEGER
coefficients, and the transport has an integer solution

    (P+1)C = 1-A(J) modulo M.                        (1)

Put g=gcd(P+1,M)>0. Then

    g divides (B-1)*(1-A(0)).                        (2)

Proof. Write A(J)=A(0)+J*H(J) with integral H. Solvability gives
g | 1-A(J). Since g | M=(B-1)J, multiplication by B-1 gives

    (B-1)*(1-A(J))
      =(B-1)*(1-A(0))-M*H(J),

and proves (2). Negative coefficients and any polynomial degree are
allowed; positivity of a proposed source gap is a separate condition.
If A(0)!=1 then g<=(B-1)*abs(1-A(0)), a bound depending only on fixed
B and that polynomial. If A(0)=1, (2) has right side0 and gives no
size bound. It does not assert that (1) is then consistent.

For the selective gap alpha=D*J-1, A(0)=-1, so g | 2(B-1). In the
native setting B is even and M is odd; hence g is odd and

    g | B-1.                                        (3)

One also has gcd(g,J)=1, because any common divisor divides
2-D*J and J, hence divides2 and is odd. In particular g is coprime
to N, since J=N modulo g under (3).

If C1,C2 are two integer solutions at these SAME fixed N,h, their
difference is a multiple of M/g. Equation(3) therefore gives

    C2-C1 = t*J,   t a multiple of (B-1)/g.          (4)

When 0<C1,C2<M and C2>C1, 0<t<B-1, so the positive numerical
difference t*J has the identical base-B digit t in every cell.
This is a numerical word-difference assertion. Adding that word to
C1 can involve carries; it does not assert that every digit of C2
is obtained by changing the corresponding digit of C1 by t.

At fixed N,h there are exactly g residue solutions of a consistent
linear congruence and at most g candidates after field bounds/masks.
Thus this lane offers at most B-1 compatible words at each dimension.
For example it cannot support a controller required to cover EVERY
rank class modulo dN at fixed N,h once dN>B-1. This is a precisely
specified surjectivity obstruction. A particular target rank could
still occur, dimensions can vary, and a deterministic encoding need
not require that controller. No universal impossibility follows.
The closed review's separate single-bit toggle obstruction remains valid.

## 2. A different fixed gap passes all retained local masks

Use one WHOLE coherent native tuple, with MF0 denoting the NATIVE
high mask, not its shifted source port. In the compact44/indexed
tuples B=2^d and

    0<MC,MF0<B-1, MC=2 modulo4, MF0=4 modulo8,
    a=MC*J+1, b=MF0*J-1.

The source's fourth port is MF_source=MF0+(B-1). It is never used in
place of MF0 in this intersection. All complements below are restricted
to the relevant d-bit or dN-bit word.

Put

    D=MC AND MF0, E=D+2,
    H=MF0 AND NOT MC, U=NOT(MC OR MF0).

D has bit1 clear, MC has bit1 set and MF0 has bits0,1 clear. Thus E
is the disjoint union of D and bit1, and E is supported inside MC.
Also 0<E<B-1: MF0<=B-4 and E<=MF0+2<=B-2.

Choose ANY Z supported inside U*J whose least significant bit is1.
This is possible because both masks have bit0 clear. Define

    C=H*J OR Z,
    F=M-C-E*J,
    alpha=E*J+1.                                    (5)

The supports in C are disjoint, C is disjoint from E*J, and both are
dN-bit words. Consequently C,F,E*J partition the all-ones word M:
F is the bitwise complement of C OR E*J, and

    C+F+alpha=q.                                    (6)

C has bit0=1, so C>=1 and subtracting1 simply clears that bit. Since
C is disjoint from MC*J, this proves

    (C-1) AND (MC*J+1)=0.                           (7)

Every bit of MF0*J is covered by H*J inside C or D*J inside E*J.
Thus F is disjoint from MF0*J. Decrementing MF0*J to form b clears
its bit2 and sets bits0,1, changing no other bits. F has bit0=0
because C has bit0=1, and bit1=0 because E*J has bit1=1. Hence

    F AND (MF0*J-1)=0.                              (8)

For the actual whole compact44/indexed masks, F is STRICTLY positive
for every such Z. At micro-radix position1063, rho=2^67, the printed
MC recipe has digit rho-4: its all-ones digit loses1 from the dummy
support and another2 from the explicit correction. MF0 has no support
at that micro-position. Therefore binary bit67*1063+2 lies in MC,
outside MF0 and outside the extra GLOBAL bit1 of E. Neither C nor
E*J contains it, so F contains it. The native proof pins the complete
recipe; the indexed proof retains these identical masks. No coefficient
port is combined with a differently calibrated tuple.

Thus (5) supplies positive C,F,alpha and both exact retained mask
conditions, with alpha=(D+2)J+1. It is only a local mask theorem.
There is no assertion that any of its Z choices satisfies transport.

## 3. The new gap genuinely escapes the bounded-kernel lemma

For (5), equation(1) becomes

    (P+1)C = -E*J modulo M.                         (9)

Its polynomial has constant term1, so lemma(2) imposes no size bound.
There are also explicit arithmetic dimensions with a large kernel,
independently of the masks. Fix h>=1 and L=P+1=B^h+K0+1>1, with
gcd(B,L)=1. Choose N divisible by h and by the multiplicative order
of B modulo L*(B-1). That order exists. Then

    L*(B-1) divides B^N-1, hence L divides J.

Thus g=gcd(L,M)=L, which grows with h. The positive integer

    C0=(B-1-E)*J/L

satisfies (9); taking F0=M-C0-E*J also gives F0>0 and (6) when
L>1. These arithmetic C0,F0 are NOT asserted to satisfy the masks.
The local construction of section2 and the transport construction
here are separate existence statements; their intersection is unproved.
For the printed tuples K0 is even, so L is odd and coprime to the
power-of-two B, as required for this auxiliary arithmetic observation.
No compatibility with the old prime-power padding dimensions is implied.

## 4. The remaining coordinated-controller obligation

At fixed J and alpha, the actual retained packed rank is

    G=(q-1)(q-F)+alpha,
    Rank=G*(q^2-1)+(MC+q*MF_source)*J.

Since deltaF=-deltaC, its EXACT change between two accepted words is

    deltaRank=(q-1)*(q^2-1)*deltaC.

For a kernel step deltaC=M/g this coefficient is
M^2*(q^2-1)/g. If gcd(q^2-1,dN)=1, that integer is a unit modulo
dN, because g divides M. A no-wrap interval of dN consecutive kernel
parameters satisfying all masks and local computation constraints would
therefore be a sufficient replacement controller. Neither such an
interval nor a different adequate coordinated family has been built.
The old controller's unit condition is proved only at its own licensed
dimensions; section3 does not automatically preserve those dimensions.

The substantive missing task is a uniform construction in the
intersection of the mask-defined Boolean words, (9), valid computation
constraints and a sufficient rank-controller family, at one cofinal
padding schedule. Additional carry/slack bits must have an exact local
soundness/completeness argument and cannot be treated as independent
dummy flips. These lemmas isolate an avoidable constant-term obstruction
and a concrete alternative local gap. They do not settle that compiler
problem or establish an operation, degree or unknown-count improvement.
