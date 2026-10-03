# A free auxiliary coefficient: 83 paid gates, with a failed full-witness inverse

The [source](complete83_free_coefficient_scout.py) and [receipt](complete83_free_coefficient_scout.json) emit one complete **83=46M+37A** polynomial with **18 positive supplied witnesses** and exact degree **111**. This is an **unproved arithmetic candidate, not an 83-operation universal bound**. Its ordinary input and fixed numeral ports are unchanged from [scaled output84](complete84_scaled_strong_output.md).

The literal rational pullback exists, but its integer restriction fails on additional full positive candidate zeros at every already accepted input. This does **not** exhibit a false accepted input: all constructed extensions keep an accepted parent's ordinary input. Whether the candidate recognizes any additional ordinary inputs remains open here.

## 1. The one-row deletion and complete identities

Write A for the Pell parameter a+2, Delta=A²−1, c=`R10a`, and D=`R14`. The source register named `A` holds Delta. The immediate parent already pays for

    c² = c2,  Delta*c² = Ac2,
    S = i*Ac2,  Kaux = S²,
    V = c*(T*f−1)−R*f²,
    Na = Kaux*(V²−y²)+y²,
    Ns_scaled = Delta*f²−Kaux.

Here T=`auxiliary_quotient`, R=`r_lhs`, and y=`y_aux`. The parent output is the product of seven factors minus Delta. Its positive zeros have six retained factors equal to 1 and `Ns_scaled=Delta`.

Delete only `aux_coefficient_root=i*Ac2` and supply its output S directly in place of i. The six fixed numeral ports, ordinary input x, all other supplied coordinates, all 83 remaining rows and all seven finalizer operations remain literal. In particular, Ac2 is still paid and live in the main norm. No side equation asserting divisibility is added.

The complete core costs 76=40M+36A and the finalizer costs 7=6M+1A. The only saving is one multiplication. The source is fully live. The forward graph substitution

    S=i*Ac2

proves the entire polynomial identity

    F83(S=i*Ac2)=F84                                  (1)

over every commutative ring. On rational assignments with Ac2 nonzero, the unique inverse of this literal substitution is

    i=S/Ac2=S/(Delta*c²),
    F84(i=S/Ac2)=F83.                                 (2)

Both identities concern the complete output. They are not merely identities between selected factors. On the supplied positive domain Delta*c²>0, so the rational inverse is positive; its integrality is the missing condition.

The helper checks i's sole consumer, f's two consumers, T's sole consumer and y's sole consumer, and reconstructs all 83 formal register identities under (1). The changed f,T,y,S coordinates can affect only the auxiliary and strong factors; the first, main, input, index and transport factors retain their entire source expressions.

## 2. What is already proved about the ordinary-input relation

Every full positive parent zero maps to a full positive candidate zero by (1). Thus every ordinary input accepted by the parent is accepted by this candidate. This elementary completeness direction needs neither a new Pell argument nor a refreshed native witness.

The converse does not follow from (2). Moreover, the following stronger result shows that (2) cannot give a bijection of the full positive integer witness sets, even if the accepted ordinary-input languages eventually prove equal:

> For every full positive zero of the immediate 84-operation parent on a valid fixed-program slice, there is a full positive 83-operation zero at the same ordinary input and with the same first/main/input/index/transport data whose inverse (2) is nonintegral.

The proof constructs new f,T,y,S and retains every other supplied coordinate. It uses only parent conclusions already established before this construction. In particular

    p=R is odd and p≥25,
    c=psi_A(p), D=chi_A(p), A≥3,
    D²−Delta*c²=1.

All five unaffected factors are 1. The size lower bound is inherited; the construction itself works more generally and needs only the indicated nontrivial odd indices. The parent parameter q need not be retyped during the proof.

## 3. Pell identities used in both branches

Define `chi_B(n)+psi_B(n)*sqrt(B²−1)=(B+sqrt(B²−1))^n`. For positive integers B≥2 and odd t=2v+1,

    chi_B(t)=B*Q_v(B²),
    Q_v(0)=(-1)^v*t,
    Q_v(1−A²)=(-1)^v*psi_A(t).                        (3)

These are integer-polynomial identities from the pinned half-parameter proof. The executable evidence independently evaluates the odd quotient by its recurrence

    Q_0(B²)=1, Q_1(B²)=4B²−3,
    Q_(v+1)(B²)=(4B²−2)Q_v(B²)−Q_(v−1)(B²).

Whenever f=chi_A(m), b=psi_A(m), and S=Delta*b, one has

    S²=Delta*(f²−1),
    Delta*f²−S²=Delta.                                (4)

For a positive odd t, set

    V=chi_S(t)/S=Q_((t−1)/2)(S²),  y=psi_S(t).

Then V and y are positive integers and

    S²*V²−(S²−1)*y²=1.                               (5)

We will arrange

    V=−c modulo f,  V=−p modulo c,  f²=1 modulo c.    (6)

In both branches gcd(c,f)=1. Thus (6) makes

    T=(V+c+p*f²)/(c*f)                               (7)

a positive integer. Equation (7) is precisely the actual emitted argument

    V=c*(T*f−1)−p*f².

There is no uncharged division in the circuit: (7) defines an existential witness in the completeness construction.

## 4. Main index p=3 modulo 4

Set

    f=D=chi_A(p), b=c, S=Delta*c, t=p.

Here v=(p−1)/2 is odd. Because S²=Delta*(f²−1), reducing (3) modulo f gives `V=−psi_A(p)=−c`. Since c divides S, reducing modulo c gives `V=−p`. The main norm gives f²=1 modulo c and gcd(c,f)=1. Consequently (7) is a positive integer.

Equations (4) and (5) give the two required factor values. Together with the five unaffected factors, they make the entire new product equal Delta. All supplied coordinates are positive. Yet the inverse (2) is

    i=1/c,

which is nonintegral because c>1.

## 5. Main index p=1 modulo 4

Set

    f=chi_A(2p), b=psi_A(2p)=2D*c,
    S=Delta*b.

For odd p, c is odd: the recurrence for psi_A modulo 2 alternates 0,1. Therefore

    gcd(c,8p)=gcd(c,p) divides p.

The two congruences

    t=p modulo c,  t=3p modulo 8p                    (8)

are compatible. Choose any positive representative. It is odd and equals 3 modulo 4, so v=(t−1)/2 is odd. Since c divides S, (3) and (8) immediately give `V=−p modulo c`.

To obtain the other congruence, work coefficientwise in the quadratic ring modulo f. Pell duplication gives

    (chi_A(4p),psi_A(4p))=(-1,0) modulo f,
    (chi_A(8p),psi_A(8p))=(1,0) modulo f.

Thus `psi_A(t)=psi_A(3p) modulo f`. The exact triplication identity is

    psi_A(3p)=(2*chi_A(2p)+1)c=(2f+1)c.

Combining this with the second identity in (3) gives `V=−c modulo f`. Also `f²−Delta*(2Dc)²=1`, so f²=1 modulo c and gcd(c,f)=1. Equation (7) again supplies a positive integer T, and (4)–(5) again restore the exact full factor values.

This time the literal inverse is

    i=2D/c.

It is nonintegral: c is odd and greater than 1, while gcd(c,D)=1. No assumption that A is even was needed in either branch.

These two cases exhaust every full positive parent zero. The candidate's witness fiber over each accepted ordinary input therefore strictly contains the image of the literal parent substitution, whenever that fiber is nonempty. The construction does not prove the existence of a new accepted input.

## 6. Remaining soundness obligations

The candidate equation is a product equal to Delta. With free S, the scaled strong factor is no longer known to be Delta times an integer strong norm. Hence a generic candidate zero cannot first be treated as seven unit equations. A new soundness proof would have to handle those divisor/sign possibilities, or prove a different normalization theorem.

Even if all intended factor values are granted, Sections 4–5 show that main and auxiliary Pell equations, their two congruences, positivity and arbitrarily large main rank do not force `Delta*c²|S`. The original strong-rank lemma used exactly that divisibility. Applying it after the deletion would be circular.

A proof preserving only the ordinary-input projection could potentially replace native witnesses after decoding a candidate. Nothing here disproves that possibility. No counterexample at an unaccepted ordinary input and no soundness theorem for this 83-operation candidate is supplied. The established universal bound therefore remains 84.

## 7. Exact degree of the unproved candidate

This section concerns its arithmetic polynomial, not universal soundness. Give all supplied witnesses and x degree 1 and fixed numerals degree 0. Write

    Q=(B−1)J, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q−F−Z−alpha−twice_cell_bits*x,
    Ttransport=w*C1−transport_quotient*Q.

The pinned parent leading-form proof gives the product of the five unchanged factors degree 81 and leader

    −32 Q^49 h gamma0 delta² k0³ w^10 s^13 Ttransport.

The source gives `c_top=k0*s*Q³`, `Delta_top=w²*s²*Q⁸`, and `V_top=c_top*T*f`. With S now supplied, the auxiliary factor has exact degree 16 and leader `S²*c_top²*T²*f²`; the scaled strong factor has exact degree 14 and leader `Delta_top*f²`. Hence the full factor degrees are

    22,18,32,16,7,2,14,

and their product has uniform exact degree 111 with leader

    −32 Q^63 h gamma0 delta² k0^5 w^12 s^17
       *S²*Ttransport*T²*f^4.                         (9)

The coefficient of `J^64*h*rho*delta²*eta^5*w^12*s^17*S²*transport_quotient*T²*f^4` is `32*(B−1)^64`, nonzero on every inherited valid fixed-program slice. The final subtraction of degree-12 Delta cannot cancel it. Naive gate propagation gives the distinct upper bound 121. Two dense coefficient diagnostics corroborate all seven degrees and (9); those numerical assignments are not claimed to encode valid compiler programs.

## 8. Bounded executable evidence

This is a pinned-data CLI, not a maintained compiler API. It authenticates the immediate 84 source/receipt/proof and the named mathematical proof dependencies. No predecessor Python or historical verifier executes. The packet contains the entire 83-row source and all paid finalizer operations.

Beyond the formal source identity, the receipt records 40 whole forward substitutions (20 rational), 24 whole rational pullbacks, two complete degree diagnostics, and ten independent Pell/CRT cases. Three cases materialize their positive main/strong/auxiliary subsystems, including both residue classes of p. The others use exact modular recurrence checks, avoiding enormous auxiliary Pell expansions. None is described as a full compiled halting witness. Full positive candidate zeros are established parametrically from actual parent zeros by Sections 2–5, not by substituting placeholders into a numerical circuit test.

Run from any working directory:

    python3 complete83_free_coefficient_scout.py --root ABS_WIP --expect complete83_free_coefficient_scout.json

`--output PATH` writes the deterministic receipt. Checks use explicit exceptions and recursively type-exact JSON comparison; normal and optimized Python enforce the same conditions. The frozen parent files are unchanged.
