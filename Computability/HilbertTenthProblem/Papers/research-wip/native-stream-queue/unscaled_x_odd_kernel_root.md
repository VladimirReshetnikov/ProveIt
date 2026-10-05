# An odd native scale survives after the X divisibility condition is removed

**Removing q|X leaves a real arithmetic gap, even on a canonical half-binomial fiber.** Take q=27 and R=1223. They satisfy q>=16, 3q+1<=R<q^4 and R=3 modulo4. With X=2^R and the canonical half-binomial Y, the exact values satisfy

    q^3 | Y,       q does not divide X.

All retained first/main/index/normalized-strong/auxiliary equations have positive canonical witnesses. A positive input-norm split is available too. This refutes a kernel-only assertion that recovery of X=2^R and the cubic Y scale forces q to be dyadic. It does not refute a complete83 compiler: its outer mask, repunit and transport equations are not supplied here.

## 1. The exact scalar certificate

Put r=611 and define the integer

    X=2^1223,
    Y=(1/2)*sum_(j=0..611) binom(1222,611+j)*X^j.     (1)

The central coefficient is even and X is even, so (1) is integral. Direct integer arithmetic and a separate prime-adic binomial recurrence give

    Y modulo 3^12 = 452709 = 23*3^9,
    X modulo27 =14.                                  (2)

Since 23 is not divisible by3, (2) proves v3(Y)=9. Therefore s=Y/27^3 is a positive integer, although X/27 is not an integer. Y has747253 bits; its hexadecimal-byte SHA256 is `c0b09b5f941fabe318153b830833c0b5a3e3ad95d3d13d83e08d77c9801c631a`. The full huge integer is unnecessary for the witness definitions or modular proof.

For a reproducible short arithmetic certificate for (2), let m=3^12, x0=2^1223 modulo m, b0=1 and z0=1. For j=1,...,611 use the exact binomial recurrence

    b_j=b_(j-1)*(1223-j)/j,
    z_j=x0*z_(j-1)+b_j modulo m.

Then Y=z_611/2 modulo m, where 2 is inverted modulo m. The independent implementation retains the power of3 in b_j separately, strips powers of3 from each numerator and denominator, and inverts only the remaining denominator unit. It never divides by a nonunit modulo m. The direct implementation instead uses exact integer binomial coefficients in (1); it shares neither coefficients nor recurrence state with the modular calculation. Both are fresh scalar formula checks, with no source-array input.

## 2. Positive completion of the retained kernel

The canonical positive converse already proved in `pell_kernel_half_binomial42.md`, and its bound-independent version in `complete83_bounded_marker_complement_obstruction.md`, use the following definitions at fresh X,Y,R:

    E=XY, a=Y(X+1), A=a+2, Delta=A^2−1, H=4a+3,
    P=2XY^2+1,
    c=psi_A(R), D=chi_A(R),
    k=2psi_P(612), tau=chi_P(612),
    eta=c−kY, zeta=k−eta, h=(k−R−1)/E.                (3)

Here chi and psi are the standard integer Pell sequences. The converse proof uses X=2^R and Y>=X^611/2 to give Y<c/k<Y+1, so eta,zeta>0. Since P=1 modulo E, h is an integer, and strict Pell growth makes it positive. It follows that

    tau^2−(XY^2*k)(XY^2*k+k)=1,
    k−hE−R=1, D^2−Delta*c^2=1.                      (4)

This argument does not invoke a power-of-two conclusion about q. Its only retained use of q is that Y=sq^3, established in Section1. The half-binomial ratio and norm identities depend on X,Y,R themselves.

Define the integer sequence

    G_0=G_1=0, G_2=1,
    G_(j+2)=2A*G_(j+1)−G_j+2^j.

Equivalently, H G_j=chi_A(j)−a psi_A(j)−2^j. It is strictly increasing from index1. Thus gamma=G_R>0 gives D=X+ac+gamma H. An optional positive input component is obtained at u=3, W=8<q:

    kappa=psi_A(3)=3+4Delta, delta=4,
    mu=chi_A(3), rho=G_3=2A+2, sigma=G_R−G_3>0.

Then gamma=rho+sigma, mu=W+a*kappa+rho H, and mu^2−Delta*kappa^2=1. This is a kernel input component, not the ordinary-input loader of an actual fixed compiler.

For the exact current normalized auxiliary completion put

    m_aux=2cR, f=chi_A(m_aux), i=psi_A(m_aux)/c^2,
    S=Delta*psi_A(m_aux),
    y=psi_S(R), V=chi_S(R)/S,
    T=(V+c+R*f^2)/(c*f).                              (5)

All displayed supplied coordinates are positive integers. Expanding the 2c-th power of the main Pell unit proves c^2 divides psi_A(m_aux). Odd R gives integral V; R=3 modulo4 gives V=−c modulo f and V=−R modulo c. The identity f^2=1 modulo c makes c,f coprime, proving integrality of T. The same canonical identities give

    c(Tf−1)−R*f^2=V,
    S^2(V^2−y^2)+y^2=1,
    Delta*f^2−S^2=Delta.                              (6)

These are the actual normalized auxiliary and scaled strong expressions. No weakened strong condition, negative root or negative unit is used. Equations(3)–(6) are a parametric mathematical completion; the enormous full Pell coordinates are not numerically materialized.

## 3. Retained failed claim and full-source boundary

**Remark 1.** The proposed inference “X=2^R, Y=sq^3 and the standard native index bounds force q to be dyadic even if q|X was removed” is false by (1)–(6). This remains a counterexample when both ratio slacks, all normalized auxiliaries and a positive shared input split are retained. An argument for that conclusion must use an additional constraint, such as the original X scale or a proved consequence of the complete outer rows.

In particular q=27 is not a valid actual repunit value at the inherited compiler's minimal allowed B>=32. No fixed program, masks, ordinary x or transport witness is assigned here, and no false accepted input is claimed. The example therefore does not settle the reverse-transport-shear83 candidate or any other complete source. It isolates one precise missing recovery step after supplying X directly. The universal84 bound remains unchanged.

## 4. Evidence and read scope

The fresh standard-library helper `unscaled_x_odd_kernel_root_checks.py` computes the single scalar example in two independent ways and records the exact residue, valuation and bit/hash data. Its JSON receipt is frozen separately. Neither source arrays nor any supplied, committed, archived or frozen code were executed or imported. Only new scalar formula code ran before freeze.

The half-binomial proof (SHA256 `0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992`) was read through Section6, lines1–267. The full bounded-marker complement proof (SHA256 `db10e8b4f839ee3c7255b91412370ce7ecd1308b5f155a0e9ad133047b768a85`) supplies the same normalized/Bezout completion used here. The root metadata binds these dependencies and the exact author artifacts. This is an exact finite counterexample with a proved canonical completion, not a proof-assistant formalization or a universal compiler.
