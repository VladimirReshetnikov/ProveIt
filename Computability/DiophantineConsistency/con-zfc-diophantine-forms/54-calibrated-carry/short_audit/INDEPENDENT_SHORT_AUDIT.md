# Independent audit of the round-8 short positive equations

## Verdict

No algebraic, sign, positive-completeness, operation-ledger, degree, or
coefficient-binding defect was found in the six active short circuits.
The two retained comparison circuits also pass. The conclusions are
conditional on the explicitly inherited native compiler, ordinary
strong-rank/signed-recovery theorem, and K215/refutation calibration. This
audit does not replace those unbounded theorems or create a formal kernel
certificate.

The checker in this directory was authored independently. It imports or
executes neither the short-circuit producer/checker nor any upstream
program. Its inputs are the literal JSON DAGs and the four native payloads.
The accompanying JSON receipt pins each circuit by SHA-256 and records all
exact algebraic and finite checks. Normal and optimized Python execution
produce identical receipts.

## Soundness, including the potentially dangerous signs

Let n=XY^2. The first norm is exactly

    N0 = tau^2 - n(n+1) k^2,

where tau=ell+r for the first-gap version. Positivity gives n>=2 and k>0.
The consecutive product n(n+1) is not a rational square, so N0 is nonzero
at every positive assignment, before imposing any equation. Likewise
Delta=(a+2)^2-1 lies strictly between consecutive squares and c>0, so
N1=D^2-Delta c^2 is unconditionally nonzero.

Thus A=N0N1 is a nonzero integer. The exact identity

    A^2+B(B-2)+C^2 = A^2+(B-1)^2+C^2-1

makes every zero satisfy A=+/-1, B=1, C=0. This step does not assume any
individual norm sign or any positivity of V or V+u.

For N0=-1, replacing x by |x| gives

    nt < x < (n+1/2)t.

The unit transformation has ordinate t'=(2n+1)t-2x, strictly between
0 and t. It preserves x^2-n(n+1)t^2 exactly, giving a valid descent.
N1=-1 is impossible because Delta is 0 or 3 modulo 4. Hence N0=N1=1.

C=0 gives A0=I^2 with I=ic^2>1. In the gap case put y0=V+u, which need
not initially be positive. The auxiliary polynomial is exactly

    Na = I^2 V^2 - (I^2-1)y0^2.

B=1 makes Na a unit. Modulo 4 this norm is y0^2 if I is even and V^2
if I is odd, so Na=-1 is impossible. Also y0 cannot be zero because
I^2 V^2=1 would contradict I>1. Therefore y=|y0| is a legitimate
positive old auxiliary coordinate, with Na=1.

The only signs not resolved locally are Nk=Nt=epsilon. The short proof
correctly invokes the ordinary signed-recovery argument for precisely
this situation. In that argument Nt=+/-1 first gives only Cw>=0, not
Cw>0. The boundary Cw=0 is retained through rank recovery; recovering
Nk=1 then forces Nt=1 and rules out Cw=0. The short proof does not
silently discard the negative pair or the weak transport boundary.
It also does not cancel Delta out of the strong equation or assume the
supplied i is divisible by Delta. Those conclusions, where required,
belong to the inherited rank argument.

For squared V, the positive substitution T_old=fT is an exact polynomial
pullback to the old quotient. For the 73/62 circuit T already is the old
quotient. These reductions establish soundness at every positive zero,
not merely at canonical compiler witnesses.

For the ordinary product circuits, Ns=1+I^2-A0 cannot be -1 modulo 4:
A0 is 0 or 1 modulo 4, so Ns has residue 0, 1, or 2. Thus their unit
recovery reaches the same system. For the normalized 73/68 comparison,
the three unconditionally nonzero norms and their minimum argument are
also valid; the proof does not use the ordinary strong coordinate where
the normalized one is needed.

## Completeness and positive quotient/gap reconstruction

Canonical native witnesses supply c=psi_(a+2)(R), the normalized strong
equation, and R=3 modulo 4. The low phase is justified for this authentic
tuple by q=B^N, J=1 modulo 4, MC=2 modulo 4 and the recovered low mask:
Cw=1 modulo 4, hence R=Cw+2=3 modulo 4. It is not asserted for arbitrary
assignments to the circuit inputs.

For the ordinary form set i=Delta*j, S=ic^2. Then
S^2=Delta(f^2-1), c divides S, and f^2=1 modulo c. The odd-index integer
polynomials satisfy

    chi_t(2j+1) = t Q_j(t^2),
    Q_j(0) = (-1)^j(2j+1),
    Q_j(1-a0^2) = (-1)^j psi_a0(2j+1).

The two initial values and second-order recurrence prove these identities
for every j; they therefore apply modulo f^2, not just modulo f. With
V=chi_S(R)/S and y=psi_S(R), oddness of (R-1)/2 yields

    V=-c modulo f^2,  V=-R modulo c.

Since gcd(c,f)=1, the numerator V+c+Rf^2 is divisible by cf^2. Its
positivity makes T=(V+c+Rf^2)/(cf^2) a positive integer. The Pell identity
gives the required auxiliary norm. Because R>=3 and S>1,
V>=4S^2-3>1 and y^2-V^2=(V^2-1)/(S^2-1)>0, so u=y-V is positive.
Similarly tau^2-ell^2=ell*k+1>0 gives r=tau-ell>0.

This reconstructs an auxiliary witness; it does not claim that every old
T is divisible by f. For the old-quotient variant use T_old=fT.
The active 66-gate scaled polynomial uses the same squared-quotient
pullback and the same authentic native phase. No old/new coefficient
ports are mixed.

## Literal circuit and exact degree audit

The independently checked ledgers are:

| Circuit | Gates | Multiply | Add | Subtract | Exact degree |
|---|---:|---:|---:|---:|---:|
| p66_degree157 | 66 | 38 | 15 | 13 | 157 |
| p68_degree101 | 68 | 38 | 16 | 14 | 101 |
| p70_degree80 | 70 | 39 | 17 | 14 | 80 |
| p71_degree78 | 71 | 40 | 17 | 14 | 78 |
| p72_degree64 | 72 | 40 | 18 | 14 | 64 |
| p73_degree62 | 73 | 41 | 18 | 14 | 62 |
| comparison p70_degree84 | 70 | 39 | 17 | 14 | 84 |
| comparison p73_degree68 | 73 | 40 | 18 | 15 | 68 |

All 15 witness ports, all four fixed coefficient ports and every producer
are live. Macro-by-macro symbolic identity checks prove that each literal
DAG implements its stated formula, without random-evaluation assumptions.

The upper bounds are not naive circuit-degree bounds. The independent
checker propagates exact homogeneous leading polynomials over Z, treating
the four fixed ports as degree-zero indeterminates. At a cancellation it
expands that node's entire ancestry exactly. In every circuit the unique
such event is N1: its apparent degree 22 cancels, and its fully expanded
323-monomial polynomial has exact degree 18. This is consistent with the
independently verified identity, Z=X+gamma H,

    N1 = 2acZ + Z^2 - Hc^2.

The degree-18 leader is 8 gamma E0^2 c0, not a surviving (ac)^2 term.

Put q0=beta J, k0=eta+zeta, E0=wsq0^4, c0=k0sq0^3,
ell0=k0ws^2q0^7 and T0=w(q0-F-alpha)-zq0. The exact output leaders are:

- 66/157: -8 q0^91 h gamma i^4 k0^13 w^13 s^26 T^2 f^4 T0.
- 68/101: 8 h gamma i^2 ell0^2 E0^5 c0^7 T^2 f^6 T0.
- 70/80: 64 gamma^2 E0^4 c0^2 ell0^4.
- 71/78: h^2 E0^6 c0^4 T^4 f^12 T0^2.
- 72/64: 4 h^2 E0^6 c0^2 T^2 f^8 u^2 T0^2.
- 73/62: 4 h^2 E0^6 c0^2 T^2 f^6 u^2 T0^2.

The checker also extracts exact distinguished monomial coefficients:
8 beta^92, -8 beta^56, 64 beta^50, beta^38, 4 beta^32 and
4 beta^32 respectively. Because the actual bound beta is positive, these
are nonzero after coefficient specialization. Hence every bound is
attained for the actual supplied tuple, not just for generic formal
coefficient ports. Full exponent vectors are in the JSON receipt.

## Binding and independent reproducibility

Each JSON resolves to the same native binding file and exact aliases
beta->beta, K0->K, MC->MC, MF->MF_source. All compressed and decompressed
hashes, byte lengths and bit lengths agree with that binding. The checker
loads the actual little-endian integers, verifies beta=2^429959-1, and
checks the unshifted native mask bounds, low residues and population sum.
MF_source is used already shifted, without adding beta a second time.
This corroborates binding; the full native semantic interface was a
separate audit and remains an explicit dependency.

The independent receipt additionally records:

- 2,400 signed direct-formula evaluations with actual native coefficient
  residues over three primes;
- 48 complete affine univariate polynomial evaluations with actual ports,
  all attaining the claimed degrees;
- exact odd-index polynomial identities through index 31;
- six exact squared-modulus Pell reconstructions, including positive T
  and positive auxiliary gap;
- exact descent, main-norm cancellation, gap and quotient identities;
- all 256 stated modulo-4 sign cases;
- verification that the proposed compressed radical deletion really
  loses a condition, including a strengthened local fixture with a0=3,
  Delta=8, c=35, i=1, S=9800, Dstrong=12005001 nonsquare, T=1,
  V=384159997, y=384159999 and main Pell root 99. Here a0-2 is positive,
  unlike the smaller a0=2 fixture retained as a diagnostic of the source.
  These are local norm obstructions, not complete positive parent tuples
  or false consistency-equation roots. The checker also proves the exact
  family identities c=4a0^2-1, S=(a0^2-1)c^2, T=1,
  V=4S^2-3, y=V+2, without asserting nonsquareness for every family member.

Run:

    python3 audit_short_independent.py
    python3 -O audit_short_independent.py

The algebraic identities and homogeneous calculations are exact; the
finite Pell/modular examples are diagnostics, not substitutes for the
unbounded proof. No consistency witness was sought or assumed.
